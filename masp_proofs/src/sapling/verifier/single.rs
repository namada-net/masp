use bellman::groth16::{PreparedVerifyingKey, Proof, verify_proof};
use bls12_381::Bls12;
use group::GroupEncoding;
use masp_primitives::{
    constants::{SPENDING_KEY_GENERATOR, VALUE_COMMITMENT_RANDOMNESS_GENERATOR},
    sapling::redjubjub::{PublicKey, Signature},
    transaction::components::I128Sum,
};

use super::SaplingVerificationContextInner;

/// A context object for verifying the Sapling components of a single Zcash transaction.
pub struct SaplingVerificationContext {
    inner: SaplingVerificationContextInner,
    zip216_enabled: bool,
}

impl SaplingVerificationContext {
    /// Construct a new context to be used with a single transaction.
    pub fn new(zip216_enabled: bool) -> Self {
        SaplingVerificationContext {
            inner: SaplingVerificationContextInner::new(),
            zip216_enabled,
        }
    }

    /// Perform consensus checks on a Sapling SpendDescription, while
    /// accumulating its value commitment inside the context for later use.
    #[allow(clippy::too_many_arguments)]
    pub fn check_spend(
        &mut self,
        cv: jubjub::ExtendedPoint,
        anchor: bls12_381::Scalar,
        nullifier: &[u8; 32],
        rk: PublicKey,
        sighash_value: &[u8; 32],
        spend_auth_sig: Signature,
        zkproof: Proof<Bls12>,
        verifying_key: &PreparedVerifyingKey<Bls12>,
    ) -> bool {
        let zip216_enabled = true;
        self.inner.check_spend(
            cv,
            anchor,
            nullifier,
            rk,
            sighash_value,
            spend_auth_sig,
            zkproof,
            &mut (),
            |_, rk, msg, spend_auth_sig| {
                rk.verify_with_zip216(
                    &msg,
                    &spend_auth_sig,
                    SPENDING_KEY_GENERATOR,
                    zip216_enabled,
                )
            },
            |_, proof, public_inputs| {
                verify_proof(verifying_key, &proof, &public_inputs[..]).is_ok()
            },
        )
    }

    /// Perform consensus checks on a Sapling SpendDescription, while
    /// accumulating its value commitment inside the context for later use.
    #[allow(clippy::too_many_arguments)]
    pub fn check_convert(
        &mut self,
        cv: jubjub::ExtendedPoint,
        anchor: bls12_381::Scalar,
        zkproof: Proof<Bls12>,
        verifying_key: &PreparedVerifyingKey<Bls12>,
    ) -> bool {
        self.inner
            .check_convert(cv, anchor, zkproof, &mut (), |_, proof, public_inputs| {
                verify_proof(verifying_key, &proof, &public_inputs[..]).is_ok()
            })
    }

    /// Perform consensus checks on a Sapling OutputDescription, while
    /// accumulating its value commitment inside the context for later use.
    pub fn check_output(
        &mut self,
        cv: jubjub::ExtendedPoint,
        cmu: bls12_381::Scalar,
        epk: jubjub::ExtendedPoint,
        zkproof: Proof<Bls12>,
        verifying_key: &PreparedVerifyingKey<Bls12>,
    ) -> bool {
        self.inner
            .check_output(cv, cmu, epk, zkproof, |proof, public_inputs| {
                verify_proof(verifying_key, &proof, &public_inputs[..]).is_ok()
            })
    }

    /// Perform consensus checks on the valueBalance and bindingSig parts of a
    /// Sapling transaction. All SpendDescriptions and OutputDescriptions must
    /// have been checked before calling this function.
    pub fn final_check(
        &self,
        value_balance: I128Sum,
        sighash_value: &[u8; 32],
        binding_sig: Signature,
    ) -> bool {
        self.inner.final_check(
            value_balance,
            sighash_value,
            binding_sig,
            |bvk, msg, binding_sig| {
                // Compute the signature's message for bvk/binding_sig
                let mut data_to_be_signed = [0u8; 64];
                data_to_be_signed[0..32].copy_from_slice(&bvk.0.to_bytes());
                data_to_be_signed[32..64].copy_from_slice(msg);

                bvk.verify_with_zip216(
                    &data_to_be_signed,
                    &binding_sig,
                    VALUE_COMMITMENT_RANDOMNESS_GENERATOR,
                    self.zip216_enabled,
                )
            },
        )
    }
}
