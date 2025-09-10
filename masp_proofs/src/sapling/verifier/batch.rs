use bellman::groth16::{PreparedVerifyingKey, Proof};
use bellman::{SynthesisError, groth16};
use bls12_381::Bls12;
use group::GroupEncoding;
use masp_primitives::transaction::components::sapling::{Authorized, Bundle};
use pairing::Engine;
use rand_core::{CryptoRng, RngCore};

use super::SaplingVerificationContextInner;

/// Batch of zk proofs and public inputs
#[derive(Default, Clone, Debug)]
pub struct Batch {
    /// The batch of zk proofs
    proofs: Vec<Proof<Bls12>>,
    /// The public inputs for each corresponding proofs
    inputs: Vec<Vec<<Bls12 as Engine>::Fr>>,
}

impl Batch {
    /// Verify all proofs in the batch
    pub fn verify(
        &self,
        vk: &PreparedVerifyingKey<Bls12>,
        rng: &mut impl RngCore,
    ) -> Result<bool, SynthesisError> {
        let proofs = self.proofs.iter().collect::<Vec<_>>();
        groth16::verify_proofs_batch(vk, rng, proofs.as_slice(), self.inputs.as_slice())
    }

    /// Add a proof to a batch
    pub fn queue(&mut self, proof: Proof<Bls12>, inputs: Vec<<Bls12 as Engine>::Fr>) {
        self.proofs.push(proof);
        self.inputs.push(inputs);
    }
}

/// Batch validation context for MASP/Sapling.
///
/// This batch-validates Spend, Convert, and Output proofs, and RedJubjub signatures.
///
/// Signatures are verified assuming ZIP 216 is active.
pub struct BatchValidator {
    bundles_added: bool,
    spend_proofs: Batch,
    convert_proofs: Batch,
    output_proofs: Batch,
    signatures: redjubjub::batch::Verifier,
}

impl Default for BatchValidator {
    fn default() -> Self {
        Self::new()
    }
}

impl BatchValidator {
    /// Constructs a new batch validation context.
    pub fn new() -> Self {
        BatchValidator {
            bundles_added: false,
            spend_proofs: Default::default(),
            convert_proofs: Default::default(),
            output_proofs: Default::default(),
            signatures: redjubjub::batch::Verifier::new(),
        }
    }

    /// Checks the bundle against Sapling-specific consensus rules, and adds its proof and
    /// signatures to the validator.
    ///
    /// Returns `false` if the bundle doesn't satisfy all of the consensus rules. This
    /// `BatchValidator` can continue to be used regardless, but some or all of the proofs
    /// and signatures from this bundle may have already been added to the batch even if
    /// it fails other consensus rules.
    pub fn check_bundle(&mut self, bundle: Bundle<Authorized>, sighash: [u8; 32]) -> bool {
        self.bundles_added = true;

        let mut ctx = SaplingVerificationContextInner::new();

        for spend in bundle.shielded_spends {
            // Deserialize the proof
            let zkproof = match groth16::Proof::read(&spend.zkproof[..]) {
                Ok(p) => p,
                Err(_) => return false,
            };

            // Check the Spend consensus rules, and batch its proof and spend
            // authorization signature.
            let consensus_rules_passed = ctx.check_spend(
                spend.cv,
                spend.anchor,
                &spend.nullifier.0,
                spend.rk,
                &sighash,
                spend.spend_auth_sig,
                zkproof,
                self,
                |this, rk, _, spend_auth_sig| {
                    let rk = redjubjub::VerificationKeyBytes::<redjubjub::SpendAuth>::from(
                        rk.0.to_bytes(),
                    );
                    let spend_auth_sig = {
                        let mut buf = [0; 64];
                        spend_auth_sig.write(&mut buf[..]).unwrap();
                        redjubjub::Signature::<redjubjub::SpendAuth>::from(buf)
                    };

                    this.signatures.queue((rk, spend_auth_sig, &sighash));
                    true
                },
                |this, proof, public_inputs| {
                    this.spend_proofs.queue(proof, public_inputs.to_vec());
                    true
                },
            );
            if !consensus_rules_passed {
                return false;
            }
        }
        for convert in bundle.shielded_converts {
            // Deserialize the proof
            let zkproof = match groth16::Proof::read(&convert.zkproof[..]) {
                Ok(p) => p,
                Err(_) => return false,
            };

            // Check the Convert consensus rules, and batch its proof
            let consensus_rules_passed = ctx.check_convert(
                convert.cv,
                convert.anchor,
                zkproof,
                self,
                |this, proof, public_inputs| {
                    this.convert_proofs.queue(proof, public_inputs.to_vec());
                    true
                },
            );
            if !consensus_rules_passed {
                return false;
            }
        }

        for output in bundle.shielded_outputs {
            // Deserialize the ephemeral key
            let epk = match jubjub::ExtendedPoint::from_bytes(&output.ephemeral_key.0).into() {
                Some(p) => p,
                None => return false,
            };

            // Deserialize the proof
            let zkproof = match groth16::Proof::read(&output.zkproof[..]) {
                Ok(p) => p,
                Err(_) => return false,
            };

            // Check the Output consensus rules, and batch its proof.
            let consensus_rules_passed = ctx.check_output(
                output.cv,
                output.cmu,
                epk,
                zkproof,
                |proof, public_inputs| {
                    self.output_proofs.queue(proof, public_inputs.to_vec());
                    true
                },
            );
            if !consensus_rules_passed {
                return false;
            }
        }

        // Check the whole-bundle consensus rules, and batch the binding signature.
        ctx.final_check(
            bundle.value_balance,
            &sighash,
            bundle.authorization.binding_sig,
            |bvk, _, binding_sig| {
                let bvk =
                    redjubjub::VerificationKeyBytes::<redjubjub::Binding>::from(bvk.0.to_bytes());
                let binding_sig = {
                    let mut buf = [0; 64];
                    binding_sig.write(&mut buf[..]).unwrap();
                    redjubjub::Signature::<redjubjub::Binding>::from(buf)
                };

                self.signatures.queue((bvk, binding_sig, &sighash));
                true
            },
        )
    }

    /// Batch-validates the accumulated bundles.
    ///
    /// Returns `true` if every proof and signature in every bundle added to the batch
    /// validator is valid, or `false` if one or more are invalid. No attempt is made to
    /// figure out which of the accumulated bundles might be invalid; if that information
    /// is desired, construct separate [`BatchValidator`]s for sub-batches of the bundles.
    pub fn validate<R: RngCore + CryptoRng>(
        self,
        spend_vk: &groth16::VerifyingKey<Bls12>,
        convert_vk: &groth16::VerifyingKey<Bls12>,
        output_vk: &groth16::VerifyingKey<Bls12>,
        mut rng: R,
    ) -> bool {
        if !self.bundles_added {
            // An empty batch is always valid, but is not free to run; skip it.
            return true;
        }

        if let Err(e) = self.signatures.verify(&mut rng) {
            tracing::debug!("Signature batch validation failed: {}", e);
            return false;
        }

        let prepared_spend_key = groth16::prepare_verifying_key(spend_vk);
        let prepared_conv_key = groth16::prepare_verifying_key(convert_vk);
        let prepared_out_key = groth16::prepare_verifying_key(output_vk);
        let mut verify_proofs = |batch: &Batch, vk| batch.verify(vk, &mut rng);

        if verify_proofs(&self.spend_proofs, &prepared_spend_key).is_err() {
            tracing::debug!("Spend proof batch validation failed");
            return false;
        }

        if verify_proofs(&self.convert_proofs, &prepared_conv_key).is_err() {
            tracing::debug!("Convert proof batch validation failed");
            return false;
        }

        if verify_proofs(&self.output_proofs, &prepared_out_key).is_err() {
            tracing::debug!("Output proof batch validation failed");
            return false;
        }

        true
    }
}

#[cfg(feature = "benchmarks")]
impl BatchValidator {
    /// Verify the signatures. Intended for testing purposes only.
    pub fn verify_signatures<R: RngCore + CryptoRng>(
        self,
        mut rng: R,
    ) -> Result<(), redjubjub::Error> {
        self.signatures.verify(&mut rng)
    }

    /// Verify the spend proofs Intended for testing purposes only.
    pub fn verify_spend_proofs<R: RngCore>(
        self,
        spend_vk: &groth16::VerifyingKey<Bls12>,
        rng: &mut R,
    ) -> Result<bool, bellman::SynthesisError> {
        let prepared = prepare_verifying_key(spend_vk);
        self.spend_proofs.verify(&prepared, rng)
    }

    /// Verify the convert proofs. Intended for testing purposes only.
    pub fn verify_convert_proofs<R: RngCore>(
        self,
        convert_vk: &groth16::VerifyingKey<Bls12>,
        rng: &mut R,
    ) -> Result<bool, bellman::SynthesisError> {
        let prepared = prepare_verifying_key(convert_vk);
        self.convert_proofs.verify(&prepared, rng)
    }

    /// Verify the output proofs. Intended for testing purposes only.
    pub fn verify_output_proofs<R: RngCore>(
        self,
        output_vk: &groth16::VerifyingKey<Bls12>,
        rng: &mut R,
    ) -> Result<bool, bellman::SynthesisError> {
        let prepared = prepare_verifying_key(output_vk);
        self.output_proofs.verify(&prepared, rng)
    }
}
