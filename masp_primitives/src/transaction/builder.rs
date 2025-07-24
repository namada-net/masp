//! Structs for building transactions.

use std::error;
use std::fmt;
use std::sync::mpsc::Sender;

use borsh::{BorshDeserialize, BorshSchema, BorshSerialize};

use rand::{CryptoRng, RngCore};

use crate::{
    MaybeArbitrary,
    asset_type::AssetType,
    consensus::{self, BlockHeight, BranchId},
    convert::AllowedConversion,
    keys::OutgoingViewingKey,
    memo::MemoBytes,
    merkle_tree::MerklePath,
    sapling::{Diversifier, Node, Note, PaymentAddress, prover::TxProver},
    transaction::{
        Transaction, TransactionData, TransparentAddress, TxVersion, Unauthorized,
        components::{
            amount::{BalanceError, I128Sum, MAX_MONEY, U64Sum, ValueSum},
            sapling::{
                self,
                builder::{BuildParams, SaplingBuilder, SaplingMetadata},
            },
            transparent::{self, builder::TransparentBuilder},
        },
        fees::FeeRule,
        sighash::{SignableInput, signature_hash},
        txid::TxIdDigester,
    },
    zip32::{ExtendedKey, ExtendedSpendingKey},
};

#[cfg(feature = "transparent-inputs")]
use crate::transaction::components::transparent::TxOut;

const DEFAULT_TX_EXPIRY_DELTA: u32 = 20;
/// Errors that can occur during transaction construction.
#[derive(Debug, PartialEq, Eq)]
pub enum Error<FeeError> {
    /// Insufficient funds were provided to the transaction builder; the given
    /// additional amount is required in order to construct the transaction.
    InsufficientFunds(I128Sum),
    /// The transaction has inputs in excess of outputs and fees; the user must
    /// add a change output.
    ChangeRequired(U64Sum),
    /// An error occurred in computing the fees for a transaction.
    Fee(FeeError),
    /// An overflow or underflow occurred when computing value balances
    Balance(BalanceError),
    /// An error occurred in constructing the transparent parts of a transaction.
    TransparentBuild(transparent::builder::Error),
    /// An error occurred in constructing the Sapling parts of a transaction.
    SaplingBuild(sapling::builder::Error),
}

impl<FE: fmt::Display> fmt::Display for Error<FE> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Error::InsufficientFunds(amount) => write!(
                f,
                "Insufficient funds for transaction construction; need an additional {:?} zatoshis",
                amount
            ),
            Error::ChangeRequired(amount) => write!(
                f,
                "The transaction requires an additional change output of {:?} zatoshis",
                amount
            ),
            Error::Balance(e) => write!(f, "Invalid amount {:?}", e),
            Error::Fee(e) => write!(f, "An error occurred in fee calculation: {}", e),
            Error::TransparentBuild(err) => err.fmt(f),
            Error::SaplingBuild(err) => err.fmt(f),
        }
    }
}

impl<FE: fmt::Debug + fmt::Display> error::Error for Error<FE> {}

impl<FE> From<BalanceError> for Error<FE> {
    fn from(e: BalanceError) -> Self {
        Error::Balance(e)
    }
}

/// Reports on the progress made by the builder towards building a transaction.
pub struct Progress {
    /// The number of steps completed.
    cur: u32,
    /// The expected total number of steps (as of this progress update), if known.
    end: Option<u32>,
}

impl Progress {
    pub fn new(cur: u32, end: Option<u32>) -> Self {
        Self { cur, end }
    }

    /// Returns the number of steps completed so far while building the transaction.
    ///
    /// Note that each step may not be of the same complexity/duration.
    pub fn cur(&self) -> u32 {
        self.cur
    }

    /// Returns the total expected number of steps before this transaction will be ready,
    /// or `None` if the end is unknown as of this progress update.
    ///
    /// Note that each step may not be of the same complexity/duration.
    pub fn end(&self) -> Option<u32> {
        self.end
    }
}

/// Generates a [`Transaction`] from its inputs and outputs.
#[derive(Clone, Debug, BorshSerialize, BorshDeserialize, BorshSchema)]
pub struct Builder<P, Key = ExtendedSpendingKey, Notifier = Sender<Progress>> {
    params: P,
    target_height: BlockHeight,
    expiry_height: BlockHeight,
    transparent_builder: TransparentBuilder,
    sapling_builder: SaplingBuilder<P, Key>,
    #[borsh(skip)]
    progress_notifier: Option<Notifier>,
}

impl<P, K, N> Builder<P, K, N> {
    /// Returns the network parameters that the builder has been configured for.
    pub fn params(&self) -> &P {
        &self.params
    }

    /// Returns the target height of the transaction under construction.
    pub fn target_height(&self) -> BlockHeight {
        self.target_height
    }

    /// Returns the set of transparent inputs currently committed to be consumed
    /// by the transaction.
    pub fn transparent_inputs(&self) -> &[impl transparent::fees::InputView] {
        self.transparent_builder.inputs()
    }

    /// Returns the set of transparent outputs currently set to be produced by
    /// the transaction.
    pub fn transparent_outputs(&self) -> &[impl transparent::fees::OutputView] {
        self.transparent_builder.outputs()
    }

    /// Returns the set of Sapling inputs currently committed to be consumed
    /// by the transaction.
    pub fn sapling_inputs(&self) -> &[impl sapling::fees::InputView<(), K>] {
        self.sapling_builder.inputs()
    }

    /// Returns the set of Sapling outputs currently set to be produced by
    /// the transaction.
    pub fn sapling_outputs(&self) -> &[impl sapling::fees::OutputView] {
        self.sapling_builder.outputs()
    }

    /// Returns the set of Sapling converts currently set to be produced by
    /// the transaction.
    pub fn sapling_converts(&self) -> &[impl sapling::fees::ConvertView] {
        self.sapling_builder.converts()
    }
}

impl<
    P: consensus::Parameters,
    K: ExtendedKey + std::fmt::Debug + Clone + PartialEq + for<'a> MaybeArbitrary<'a>,
> Builder<P, K>
{
    /// Creates a new `Builder` targeted for inclusion in the block with the given height,
    /// using default values for general transaction fields and the default OS random.
    ///
    /// # Default values
    ///
    /// The expiry height will be set to the given height plus the default transaction
    /// expiry delta (20 blocks).
    pub fn new(params: P, target_height: BlockHeight) -> Self {
        Self::new_internal(params, target_height)
    }
}

impl<
    P: consensus::Parameters,
    K: ExtendedKey + std::fmt::Debug + Clone + PartialEq + for<'a> MaybeArbitrary<'a>,
> Builder<P, K>
{
    /// Common utility function for builder construction.
    ///
    /// WARNING: THIS MUST REMAIN PRIVATE AS IT ALLOWS CONSTRUCTION
    /// OF BUILDERS WITH NON-CryptoRng RNGs
    fn new_internal(params: P, target_height: BlockHeight) -> Builder<P, K> {
        Builder {
            params: params.clone(),
            target_height,
            expiry_height: target_height + DEFAULT_TX_EXPIRY_DELTA,
            transparent_builder: TransparentBuilder::empty(),
            sapling_builder: SaplingBuilder::new(params, target_height),
            progress_notifier: None,
        }
    }

    /// Adds a Sapling note to be spent in this transaction.
    ///
    /// Returns an error if the given Merkle path does not have the same anchor as the
    /// paths for previous Sapling notes.
    pub fn add_sapling_spend(
        &mut self,
        extsk: K,
        diversifier: Diversifier,
        note: Note,
        merkle_path: MerklePath<Node>,
    ) -> Result<(), sapling::builder::Error> {
        self.sapling_builder
            .add_spend(extsk, diversifier, note, merkle_path)
    }

    /// Adds a Sapling note to be spent in this transaction.
    ///
    /// Returns an error if the given Merkle path does not have the same anchor as the
    /// paths for previous Sapling notes.
    pub fn add_sapling_convert(
        &mut self,
        allowed: AllowedConversion,
        value: u64,
        merkle_path: MerklePath<Node>,
    ) -> Result<(), sapling::builder::Error> {
        self.sapling_builder
            .add_convert(allowed, value, merkle_path)
    }

    /// Adds a Sapling address to send funds to.
    pub fn add_sapling_output(
        &mut self,
        ovk: Option<OutgoingViewingKey>,
        to: PaymentAddress,
        asset_type: AssetType,
        value: u64,
        memo: MemoBytes,
    ) -> Result<(), sapling::builder::Error> {
        if value > MAX_MONEY {
            return Err(sapling::builder::Error::InvalidAmount);
        }
        self.sapling_builder
            .add_output(ovk, to, asset_type, value, memo)
    }

    /// Adds a transparent coin to be spent in this transaction.
    #[cfg(feature = "transparent-inputs")]
    #[cfg_attr(docsrs, doc(cfg(feature = "transparent-inputs")))]
    pub fn add_transparent_input(
        &mut self,
        coin: TxOut,
    ) -> Result<(), transparent::builder::Error> {
        self.transparent_builder.add_input(coin)
    }

    /// Adds a transparent address to send funds to.
    pub fn add_transparent_output(
        &mut self,
        to: &TransparentAddress,
        asset_type: AssetType,
        value: u64,
    ) -> Result<(), transparent::builder::Error> {
        if value > MAX_MONEY {
            return Err(transparent::builder::Error::InvalidAmount);
        }

        self.transparent_builder.add_output(to, asset_type, value)
    }

    /// Sets the notifier channel, where progress of building the transaction is sent.
    ///
    /// An update is sent after every Spend or Output is computed, and the `u32` sent
    /// represents the total steps completed so far. It will eventually send number of
    /// spends + outputs. If there's an error building the transaction, the channel is
    /// closed.
    pub fn with_progress_notifier(&mut self, progress_notifier: Sender<Progress>) {
        self.progress_notifier = Some(progress_notifier);
    }

    /// Returns the sum of the transparent, Sapling, and TZE value balances.
    pub fn value_balance(&self) -> I128Sum {
        let value_balances = [
            self.transparent_builder.value_balance(),
            self.sapling_builder.value_balance(),
        ];

        value_balances.into_iter().sum::<I128Sum>()
    }

    /// Builds a transaction from the configured spends and outputs.
    ///
    /// Upon success, returns a tuple containing the final transaction, and the
    /// [`SaplingMetadata`] generated during the build process.
    pub fn build<FR: FeeRule>(
        self,
        prover: &impl TxProver,
        fee_rule: &FR,
        rng: &mut (impl CryptoRng + RngCore),
        bparams: &mut impl BuildParams,
    ) -> Result<(Transaction, SaplingMetadata), Error<FR::Error>> {
        let fee = fee_rule
            .fee_required(
                &self.params,
                self.target_height,
                self.transparent_builder.outputs(),
                self.sapling_builder.inputs().len(),
                self.sapling_builder.outputs().len(),
            )
            .map_err(Error::Fee)?;
        self.build_internal(prover, fee, rng, bparams)
    }

    fn build_internal<FE>(
        self,
        prover: &impl TxProver,
        fee: U64Sum,
        rng: &mut (impl CryptoRng + RngCore),
        bparams: &mut impl BuildParams,
    ) -> Result<(Transaction, SaplingMetadata), Error<FE>> {
        let consensus_branch_id = BranchId::for_height(&self.params, self.target_height);

        // determine transaction version
        let version = TxVersion::suggested_for_branch(consensus_branch_id);

        //
        // Consistency checks
        //

        // After fees are accounted for, the value balance of the transaction must be zero.
        let balance_after_fees = self.value_balance() - I128Sum::from_sum(fee);

        if balance_after_fees != ValueSum::zero() {
            return Err(Error::InsufficientFunds(-balance_after_fees));
        };

        let transparent_bundle = self.transparent_builder.build();

        let mut ctx = prover.new_sapling_proving_context();
        let sapling_bundle = self
            .sapling_builder
            .build(
                prover,
                &mut ctx,
                rng,
                bparams,
                self.target_height,
                self.progress_notifier.as_ref(),
            )
            .map_err(Error::SaplingBuild)?;

        let unauthed_tx: TransactionData<Unauthorized<K>> = TransactionData {
            version,
            consensus_branch_id: BranchId::for_height(&self.params, self.target_height),
            lock_time: 0,
            expiry_height: self.expiry_height,
            transparent_bundle,
            sapling_bundle,
        };

        //
        // Signatures -- everything but the signatures must already have been added.
        //
        let txid_parts = unauthed_tx.digest(TxIdDigester);

        let transparent_bundle = unauthed_tx
            .transparent_bundle
            .clone()
            .map(|b| b.apply_signatures());

        // the commitment being signed is shared across all Sapling inputs; once
        // V4 transactions are deprecated this should just be the txid, but
        // for now we need to continue to compute it here.
        let shielded_sig_commitment =
            signature_hash(&unauthed_tx, &SignableInput::Shielded, &txid_parts);

        let (sapling_bundle, tx_metadata) = match unauthed_tx
            .sapling_bundle
            .map(|b| {
                b.apply_signatures(
                    prover,
                    &mut ctx,
                    rng,
                    bparams,
                    shielded_sig_commitment.as_ref(),
                )
            })
            .transpose()
            .map_err(Error::SaplingBuild)?
        {
            Some((bundle, meta)) => (Some(bundle), meta),
            None => (None, SaplingMetadata::empty()),
        };

        let authorized_tx = TransactionData {
            version: unauthed_tx.version,
            consensus_branch_id: unauthed_tx.consensus_branch_id,
            lock_time: unauthed_tx.lock_time,
            expiry_height: unauthed_tx.expiry_height,
            transparent_bundle,
            sapling_bundle,
        };

        // The unwrap() here is safe because the txid hashing
        // of freeze() should be infalliable.
        Ok((authorized_tx.freeze().unwrap(), tx_metadata))
    }
}

pub trait MapBuilder<P1, K1, N1, P2, K2, N2>: sapling::builder::MapBuilder<P1, K1, P2, K2> {
    fn map_notifier(&self, s: N1) -> N2;
}

impl<P1, K1, N1> Builder<P1, K1, N1> {
    pub fn map_builder<P2, K2, N2, F: MapBuilder<P1, K1, N1, P2, K2, N2>>(
        self,
        f: F,
    ) -> Builder<P2, K2, N2> {
        Builder::<P2, K2, N2> {
            params: f.map_params(self.params),
            target_height: self.target_height,
            expiry_height: self.expiry_height,
            transparent_builder: self.transparent_builder,
            progress_notifier: self.progress_notifier.map(|x| f.map_notifier(x)),
            sapling_builder: self.sapling_builder.map_builder(f),
        }
    }
}

#[cfg(any(test, feature = "test-dependencies"))]
mod testing {
    use rand::{CryptoRng, RngCore};
    use std::convert::Infallible;

    use super::{Builder, Error, SaplingMetadata};
    use crate::{
        consensus::{self, BlockHeight},
        sapling::prover::mock::MockTxProver,
        transaction::{Transaction, builder::BuildParams, fees::fixed},
    };

    impl<P: consensus::Parameters> Builder<P> {
        /// Creates a new `Builder` targeted for inclusion in the block with the given height
        /// and randomness source, using default values for general transaction fields.
        ///
        /// # Default values
        ///
        /// The expiry height will be set to the given height plus the default transaction
        /// expiry delta (20 blocks).
        ///
        /// WARNING: DO NOT USE IN PRODUCTION
        pub fn test_only_new_with_rng(params: P, height: BlockHeight) -> Builder<P> {
            Self::new_internal(params, height)
        }

        pub fn mock_build(
            self,
            rng: &mut (impl CryptoRng + RngCore),
            bparams: &mut impl BuildParams,
        ) -> Result<(Transaction, SaplingMetadata), Error<Infallible>> {
            self.build(&MockTxProver, &fixed::FeeRule::standard(), rng, bparams)
        }
    }
}

#[cfg(test)]
mod tests {
    use ff::Field;
    use rand::Rng;
    use rand_core::OsRng;

    use crate::{
        asset_type::AssetType,
        consensus::{NetworkUpgrade, Parameters, TEST_NETWORK},
        memo::MemoBytes,
        merkle_tree::{CommitmentTree, IncrementalWitness},
        sapling::Rseed,
        transaction::{
            TransparentAddress,
            components::amount::{DEFAULT_FEE, I128Sum, ValueSum},
            sapling::builder as build_s,
        },
        zip32::ExtendedSpendingKey,
    };

    use super::{Builder, Error};

    /*#[test]
    fn fails_on_overflow_output() {
        let extsk = ExtendedSpendingKey::master(&[]);
        let dfvk = extsk.to_diversifiable_full_viewing_key();
        let ovk = dfvk.fvk().ovk;
        let to = dfvk.default_address().1;

        let masp_activation_height = TEST_NETWORK
            .activation_height(NetworkUpgrade::MASP)
            .unwrap();

        let mut builder = Builder::new(TEST_NETWORK, masp_activation_height);
        assert_eq!(
            builder.add_sapling_output(
                Some(ovk),
                to,
                zec(),
                MAX_MONEY + 1,
                MemoBytes::empty()
            ),
            Err(build_s::Error::InvalidAmount)
        );
    }*/

    /// Generate ZEC asset type
    fn zec() -> AssetType {
        AssetType::new(b"ZEC").unwrap()
    }

    #[test]
    fn binding_sig_present_if_shielded_spend() {
        let mut rng = OsRng;

        let transparent_address = TransparentAddress(rng.r#gen::<[u8; 20]>());

        let extsk = ExtendedSpendingKey::master(&[]);
        let dfvk = extsk.to_diversifiable_full_viewing_key();
        let to = dfvk.default_address().1;

        let mut rng = OsRng;

        let note1 = to
            .create_note(
                zec(),
                50000,
                Rseed::BeforeZip212(jubjub::Fr::random(&mut rng)),
            )
            .unwrap();
        let cmu1 = note1.commitment();
        let mut tree = CommitmentTree::empty();
        tree.append(cmu1).unwrap();
        let witness1 = IncrementalWitness::from_tree(&tree);

        let tx_height = TEST_NETWORK
            .activation_height(NetworkUpgrade::MASP)
            .unwrap();
        let mut builder = Builder::new(TEST_NETWORK, tx_height);

        // Create a tx with a sapling spend. binding_sig should be present
        builder
            .add_sapling_spend(extsk, *to.diversifier(), note1, witness1.path().unwrap())
            .unwrap();

        builder
            .add_transparent_output(&transparent_address, zec(), 49000)
            .unwrap();

        // Expect a binding signature error, because our inputs aren't valid, but this shows
        // that a binding signature was attempted
        assert_eq!(
            builder.mock_build(&mut OsRng, &mut build_s::RngBuildParams::new(OsRng)),
            Err(Error::SaplingBuild(build_s::Error::BindingSig))
        );
    }

    #[test]
    fn fails_on_negative_change() {
        let mut rng = OsRng;

        let transparent_address = TransparentAddress(rng.r#gen::<[u8; 20]>());
        // Just use the master key as the ExtendedSpendingKey for this test
        let extsk = ExtendedSpendingKey::master(&[]);
        let tx_height = TEST_NETWORK
            .activation_height(NetworkUpgrade::MASP)
            .unwrap();

        // Fails with no inputs or outputs
        // 0.0001 t-ZEC fee
        {
            let builder = Builder::new(TEST_NETWORK, tx_height);
            assert_eq!(
                builder.mock_build(&mut OsRng, &mut build_s::RngBuildParams::new(OsRng)),
                Err(Error::InsufficientFunds(I128Sum::from_sum(
                    DEFAULT_FEE.clone()
                )))
            );
        }

        let dfvk = extsk.to_diversifiable_full_viewing_key();
        let ovk = Some(dfvk.fvk().ovk);
        let to = dfvk.default_address().1;

        // Fail if there is only a Sapling output
        // 0.0005 z-ZEC out, 0.00001 t-ZEC fee
        {
            let mut builder = Builder::new(TEST_NETWORK, tx_height);
            builder
                .add_sapling_output(ovk, to, zec(), 50000, MemoBytes::empty())
                .unwrap();
            assert_eq!(
                builder.mock_build(&mut OsRng, &mut build_s::RngBuildParams::new(OsRng)),
                Err(Error::InsufficientFunds(
                    I128Sum::from_pair(zec(), 50000) + &I128Sum::from_sum(DEFAULT_FEE.clone())
                ))
            );
        }

        // Fail if there is only a transparent output
        // 0.0005 t-ZEC out, 0.00001 t-ZEC fee
        {
            let mut builder = Builder::new(TEST_NETWORK, tx_height);
            builder
                .add_transparent_output(&transparent_address, zec(), 50000)
                .unwrap();
            assert_eq!(
                builder.mock_build(&mut OsRng, &mut build_s::RngBuildParams::new(OsRng)),
                Err(Error::InsufficientFunds(
                    I128Sum::from_pair(zec(), 50000) + &I128Sum::from_sum(DEFAULT_FEE.clone())
                ))
            );
        }

        let note1 = to
            .create_note(
                zec(),
                50999,
                Rseed::BeforeZip212(jubjub::Fr::random(&mut rng)),
            )
            .unwrap();
        let cmu1 = note1.commitment();
        let mut tree = CommitmentTree::empty();
        tree.append(cmu1).unwrap();
        let mut witness1 = IncrementalWitness::from_tree(&tree);

        // Fail if there is insufficient input
        // 0.0003 z-ZEC out, 0.0002 t-ZEC out, 0.00001 t-ZEC fee, 0.00050999 z-ZEC in
        {
            let mut builder = Builder::new(TEST_NETWORK, tx_height);
            builder
                .add_sapling_spend(extsk, *to.diversifier(), note1, witness1.path().unwrap())
                .unwrap();
            builder
                .add_sapling_output(ovk, to, zec(), 30000, MemoBytes::empty())
                .unwrap();
            builder
                .add_transparent_output(&transparent_address, zec(), 20000)
                .unwrap();
            assert_eq!(
                builder.mock_build(&mut OsRng, &mut build_s::RngBuildParams::new(OsRng)),
                Err(Error::InsufficientFunds(ValueSum::from_pair(zec(), 1)))
            );
        }

        let note2 = to
            .create_note(zec(), 1, Rseed::BeforeZip212(jubjub::Fr::random(&mut rng)))
            .unwrap();
        let cmu2 = note2.commitment();
        tree.append(cmu2).unwrap();
        witness1.append(cmu2).unwrap();
        let witness2 = IncrementalWitness::from_tree(&tree);

        // Succeeds if there is sufficient input
        // 0.0003 z-ZEC out, 0.0002 t-ZEC out, 0.0001 t-ZEC fee, 0.0006 z-ZEC in
        //
        // (Still fails because we are using a MockTxProver which doesn't correctly
        // compute bindingSig.)
        {
            let mut builder = Builder::new(TEST_NETWORK, tx_height);
            builder
                .add_sapling_spend(extsk, *to.diversifier(), note1, witness1.path().unwrap())
                .unwrap();
            builder
                .add_sapling_spend(extsk, *to.diversifier(), note2, witness2.path().unwrap())
                .unwrap();
            builder
                .add_sapling_output(ovk, to, zec(), 30000, MemoBytes::empty())
                .unwrap();
            builder
                .add_transparent_output(&transparent_address, zec(), 20000)
                .unwrap();
            assert_eq!(
                builder.mock_build(&mut OsRng, &mut build_s::RngBuildParams::new(OsRng)),
                Err(Error::SaplingBuild(build_s::Error::BindingSig))
            )
        }
    }
}
