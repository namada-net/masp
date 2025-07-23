//! Abstractions over the proving system and parameters for ease of use.

use bellman::groth16::{Parameters, PreparedVerifyingKey};
use bls12_381::Bls12;
use masp_primitives::{
    asset_type::AssetType,
    convert::AllowedConversion,
    merkle_tree::MerklePath,
    sapling::{
        Diversifier, Node, PaymentAddress, ProofGenerationKey, Rseed,
        prover::TxProver,
        redjubjub::{PublicKey, Signature},
    },
    transaction::components::{GROTH_PROOF_SIZE, I128Sum},
};
use std::path::Path;

use crate::{parse_parameters, sapling::SaplingProvingContext};

#[cfg(feature = "local-prover")]
use crate::{
    MASP_CONVERT_NAME, MASP_OUTPUT_NAME, MASP_SPEND_NAME, default_params_folder, load_parameters,
};

/// An implementation of [`TxProver`] using Sapling Spend and Output parameters from
/// locally-accessible paths.
pub struct LocalTxProver {
    spend_params: Parameters<Bls12>,
    spend_vk: PreparedVerifyingKey<Bls12>,
    output_params: Parameters<Bls12>,
    convert_params: Parameters<Bls12>,
    convert_vk: PreparedVerifyingKey<Bls12>,
}

impl LocalTxProver {
    /// Creates a `LocalTxProver` using parameters from the given local paths.
    ///
    /// # Examples
    ///
    /// ```should_panic
    /// use std::path::Path;
    /// use masp_proofs::prover::LocalTxProver;
    ///
    /// let tx_prover = LocalTxProver::new(
    ///     Path::new("/path/to/masp-spend.params"),
    ///     Path::new("/path/to/masp-output.params"),
    ///     Path::new("/path/to/masp-convert.params"),
    /// );
    /// ```
    ///
    /// # Panics
    ///
    /// This function will panic if the paths do not point to valid parameter files with
    /// the expected hashes.
    pub fn new(spend_path: &Path, output_path: &Path, convert_path: &Path) -> Self {
        let p = load_parameters(spend_path, output_path, convert_path);
        LocalTxProver {
            spend_params: p.spend_params,
            spend_vk: p.spend_vk,
            output_params: p.output_params,
            convert_params: p.convert_params,
            convert_vk: p.convert_vk,
        }
    }

    /// Creates a `LocalTxProver` using parameters specified as byte arrays.
    ///
    /// # Examples
    ///
    /// ```should_panic
    /// use std::path::Path;
    /// use masp_proofs::prover::LocalTxProver;
    ///
    /// let tx_prover = LocalTxProver::from_bytes(&[0u8], &[0u8], &[0u8]);
    /// ```
    ///
    /// # Panics
    ///
    /// This function will panic if the byte arrays do not contain valid parameters with
    /// the expected hashes.
    pub fn from_bytes(
        spend_param_bytes: &[u8],
        output_param_bytes: &[u8],
        convert_param_bytes: &[u8],
    ) -> Self {
        let p = parse_parameters(spend_param_bytes, output_param_bytes, convert_param_bytes);

        LocalTxProver {
            spend_params: p.spend_params,
            spend_vk: p.spend_vk,
            output_params: p.output_params,
            convert_params: p.convert_params,
            convert_vk: p.convert_vk,
        }
    }

    /// Attempts to create a `LocalTxProver` using parameters from the default local
    /// location.
    ///
    /// Returns `None` if any of the parameters cannot be found in the default local
    /// location.
    ///
    /// # Examples
    ///
    /// ```
    /// use masp_proofs::prover::LocalTxProver;
    ///
    /// match LocalTxProver::with_default_location() {
    ///     Some(tx_prover) => (),
    ///     None => println!("Please run zcash-fetch-params or fetch-params.sh to download the parameters."),
    /// }
    /// ```
    ///
    /// # Panics
    ///
    /// This function will panic if the parameters in the default local location do not
    /// have the expected hashes.
    #[cfg(feature = "local-prover")]
    #[cfg_attr(docsrs, doc(cfg(feature = "local-prover")))]
    pub fn with_default_location() -> Option<Self> {
        let params_dir = default_params_folder()?;
        let (spend_path, output_path, convert_path) = if params_dir.exists() {
            (
                params_dir.join(MASP_SPEND_NAME),
                params_dir.join(MASP_OUTPUT_NAME),
                params_dir.join(MASP_CONVERT_NAME),
            )
        } else {
            return None;
        };
        if !(spend_path.exists() && output_path.exists() && convert_path.exists()) {
            return None;
        }

        Some(LocalTxProver::new(&spend_path, &output_path, &convert_path))
    }

    // /// Creates a `LocalTxProver` using Sapling parameters bundled inside the binary.
    // ///
    // /// This requires the `bundled-prover` feature, which will increase the binary size by
    // /// around 50 MiB.
    // #[cfg(feature = "bundled-prover")]
    // #[cfg_attr(docsrs, doc(cfg(feature = "bundled-prover")))]
    // pub fn bundled() -> Self {
    //     let (spend_buf, output_buf) = wagyu_zcash_parameters::load_sapling_parameters();
    //     let p = parse_parameters(&spend_buf[..], &output_buf[..]);

    //     LocalTxProver {
    //         spend_params: p.spend_params,
    //         spend_vk: p.spend_vk,
    //         output_params: p.output_params,
    //     }
    //}
}

impl TxProver for LocalTxProver {
    type SaplingProvingContext = SaplingProvingContext;

    fn new_sapling_proving_context(&self) -> Self::SaplingProvingContext {
        SaplingProvingContext::new()
    }

    fn spend_proof(
        &self,
        ctx: &mut Self::SaplingProvingContext,
        proof_generation_key: ProofGenerationKey,
        diversifier: Diversifier,
        rseed: Rseed,
        ar: jubjub::Fr,
        asset_type: AssetType,
        value: u64,
        anchor: bls12_381::Scalar,
        merkle_path: MerklePath<Node>,
        rcv: jubjub::Fr,
    ) -> Result<([u8; GROTH_PROOF_SIZE], jubjub::ExtendedPoint, PublicKey), ()> {
        let (proof, cv, rk) = ctx.spend_proof(
            proof_generation_key,
            diversifier,
            rseed,
            ar,
            asset_type,
            value,
            anchor,
            merkle_path,
            &self.spend_params,
            &self.spend_vk,
            rcv,
        )?;

        let mut zkproof = [0u8; GROTH_PROOF_SIZE];
        proof
            .write(&mut zkproof[..])
            .expect("should be able to serialize a proof");

        Ok((zkproof, cv, rk))
    }

    fn output_proof(
        &self,
        ctx: &mut Self::SaplingProvingContext,
        esk: jubjub::Fr,
        payment_address: PaymentAddress,
        rcm: jubjub::Fr,
        asset_type: AssetType,
        value: u64,
        rcv: jubjub::Fr,
    ) -> ([u8; GROTH_PROOF_SIZE], jubjub::ExtendedPoint) {
        let (proof, cv) = ctx.output_proof(
            esk,
            payment_address,
            rcm,
            asset_type,
            value,
            &self.output_params,
            rcv,
        );

        let mut zkproof = [0u8; GROTH_PROOF_SIZE];
        proof
            .write(&mut zkproof[..])
            .expect("should be able to serialize a proof");

        (zkproof, cv)
    }

    fn convert_proof(
        &self,
        ctx: &mut Self::SaplingProvingContext,
        allowed_conversion: AllowedConversion,
        value: u64,
        anchor: bls12_381::Scalar,
        merkle_path: MerklePath<Node>,
        rcv: jubjub::Fr,
    ) -> Result<([u8; GROTH_PROOF_SIZE], jubjub::ExtendedPoint), ()> {
        let (proof, cv) = ctx.convert_proof(
            allowed_conversion,
            value,
            anchor,
            merkle_path,
            &self.convert_params,
            &self.convert_vk,
            rcv,
        )?;

        let mut zkproof = [0u8; GROTH_PROOF_SIZE];
        proof
            .write(&mut zkproof[..])
            .expect("should be able to serialize a proof");

        Ok((zkproof, cv))
    }

    fn binding_sig(
        &self,
        ctx: &mut Self::SaplingProvingContext,
        assets_and_values: &I128Sum,
        sighash: &[u8; 32],
    ) -> Result<Signature, ()> {
        ctx.binding_sig(assets_and_values, sighash)
    }
}
