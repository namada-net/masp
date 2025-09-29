//! Abstractions over the proving system and parameters.

use crate::{
    asset_type::AssetType,
    convert::AllowedConversion,
    merkle_tree::MerklePath,
    sapling::{
        Node,
        redjubjub::{PublicKey, Signature},
    },
    transaction::components::{GROTH_PROOF_SIZE, I128Sum},
};

use super::{Diversifier, PaymentAddress, ProofGenerationKey, Rseed};

/// Interface for creating zero-knowledge proofs for shielded transactions.
pub trait TxProver {
    /// Type for persisting any necessary context across multiple Sapling proofs.
    type SaplingProvingContext;

    /// Instantiate a new Sapling proving context.
    fn new_sapling_proving_context(&self) -> Self::SaplingProvingContext;

    /// Create the value commitment, re-randomized key, and proof for a MASP
    /// [`SpendDescription`], while accumulating its value commitment randomness inside
    /// the context for later use.
    ///    
    /// [`SpendDescription`]: crate::transaction::components::SpendDescription
    #[allow(clippy::too_many_arguments)]
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
    ) -> Result<([u8; GROTH_PROOF_SIZE], jubjub::ExtendedPoint, PublicKey), ()>;

    /// Create the value commitment and proof for a MASP OutputDescription,
    /// while accumulating its value commitment randomness inside the context for later
    /// use.
    ///
    #[allow(clippy::too_many_arguments)]
    fn output_proof(
        &self,
        ctx: &mut Self::SaplingProvingContext,
        esk: jubjub::Fr,
        payment_address: PaymentAddress,
        rcm: jubjub::Fr,
        asset_type: AssetType,
        value: u64,
        rcv: jubjub::Fr,
    ) -> ([u8; GROTH_PROOF_SIZE], jubjub::ExtendedPoint);

    /// Create the value commitment, and proof for a MASP ConvertDescription,
    /// while accumulating its value commitment randomness inside
    /// the context for later use.
    ///
    fn convert_proof(
        &self,
        ctx: &mut Self::SaplingProvingContext,
        allowed_conversion: AllowedConversion,
        value: u64,
        anchor: bls12_381::Scalar,
        merkle_path: MerklePath<Node>,
        rcv: jubjub::Fr,
    ) -> Result<([u8; GROTH_PROOF_SIZE], jubjub::ExtendedPoint), ()>;

    /// Create the `bindingSig` for a Sapling transaction. All calls to
    /// [`TxProver::spend_proof`] and [`TxProver::output_proof`] must be completed before
    /// calling this function.
    fn binding_sig(
        &self,
        ctx: &mut Self::SaplingProvingContext,
        amount: &I128Sum,
        sighash: &[u8; 32],
    ) -> Result<Signature, ()>;
}

#[cfg(any(test, feature = "test-dependencies"))]
pub mod mock {
    use crate::{
        asset_type::AssetType,
        constants::spending_key_generator,
        convert::AllowedConversion,
        merkle_tree::MerklePath,
        sapling::{
            Diversifier, Node, PaymentAddress, ProofGenerationKey, Rseed,
            redjubjub::{PublicKey, Signature},
        },
        transaction::components::{GROTH_PROOF_SIZE, I128Sum},
    };

    use super::TxProver;

    pub struct MockTxProver;

    impl TxProver for MockTxProver {
        type SaplingProvingContext = ();

        fn new_sapling_proving_context(&self) -> Self::SaplingProvingContext {}

        fn spend_proof(
            &self,
            _ctx: &mut Self::SaplingProvingContext,
            proof_generation_key: ProofGenerationKey,
            _diversifier: Diversifier,
            _rcm: Rseed,
            ar: jubjub::Fr,
            asset_type: AssetType,
            value: u64,
            _anchor: bls12_381::Scalar,
            _merkle_path: MerklePath<Node>,
            rcv: jubjub::Fr,
        ) -> Result<([u8; GROTH_PROOF_SIZE], jubjub::ExtendedPoint, PublicKey), ()> {
            let cv = asset_type.value_commitment(value, rcv).commitment().into();

            let rk =
                PublicKey(proof_generation_key.ak.into()).randomize(ar, spending_key_generator());

            Ok(([0u8; GROTH_PROOF_SIZE], cv, rk))
        }

        fn output_proof(
            &self,
            _ctx: &mut Self::SaplingProvingContext,
            _esk: jubjub::Fr,
            _payment_address: PaymentAddress,
            _rcm: jubjub::Fr,
            asset_type: AssetType,
            value: u64,
            rcv: jubjub::Fr,
        ) -> ([u8; GROTH_PROOF_SIZE], jubjub::ExtendedPoint) {
            let cv = asset_type.value_commitment(value, rcv).commitment().into();

            ([0u8; GROTH_PROOF_SIZE], cv)
        }

        fn convert_proof(
            &self,
            _ctx: &mut Self::SaplingProvingContext,
            allowed_conversion: AllowedConversion,
            value: u64,
            _anchor: bls12_381::Scalar,
            _merkle_path: MerklePath<Node>,
            rcv: jubjub::Fr,
        ) -> Result<([u8; GROTH_PROOF_SIZE], jubjub::ExtendedPoint), ()> {
            let cv = allowed_conversion
                .value_commitment(value, rcv)
                .commitment()
                .into();

            Ok(([0u8; GROTH_PROOF_SIZE], cv))
        }

        fn binding_sig(
            &self,
            _ctx: &mut Self::SaplingProvingContext,
            _value: &I128Sum,
            _sighash: &[u8; 32],
        ) -> Result<Signature, ()> {
            Err(())
        }
    }
}
