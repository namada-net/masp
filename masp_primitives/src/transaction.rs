use borsh::{BorshDeserialize, BorshSchema, BorshSerialize};

pub mod builder;
pub mod components;
pub mod fees;
pub mod sighash;
pub mod sighash_v5;
pub mod txid;
use blake2b_simd::Hash as Blake2bHash;
use byteorder::{LittleEndian, ReadBytesExt, WriteBytesExt};
use ff::PrimeField;
use memuse::DynamicUsage;
use std::collections::BTreeMap;
use std::{
    fmt::{self, Debug},
    hash::Hash,
    io::{self, Read, Write},
    ops::Deref,
};
use zcash_encoding::{Array, CompactSize, Vector};

use crate::{
    consensus::{BlockHeight, BranchId},
    sapling::redjubjub,
};

use self::{
    components::{
        amount::{I128Sum, ValueSum},
        sapling::{
            self, ConvertDescriptionV5, OutputDescriptionV5, SpendDescription, SpendDescriptionV5,
        },
        transparent::{self, TxIn, TxOut},
    },
    txid::{BlockTxCommitmentDigester, TxIdDigester, to_txid},
};
use crate::MaybeArbitrary;
use borsh::schema::Fields;
use borsh::schema::add_definition;
use borsh::schema::{Declaration, Definition};
use std::marker::PhantomData;
use std::ops::RangeInclusive;

#[cfg_attr(feature = "arbitrary", derive(arbitrary::Arbitrary))]
#[derive(
    Clone,
    Copy,
    PartialOrd,
    Ord,
    PartialEq,
    Eq,
    Hash,
    Debug,
    BorshSerialize,
    BorshDeserialize,
    BorshSchema,
)]
pub struct TransparentAddress(pub [u8; 20]);

pub const GROTH_PROOF_SIZE: usize = 48 + 96 + 48;
pub type GrothProofBytes = [u8; GROTH_PROOF_SIZE];

const MASPV5_TX_VERSION: u32 = 2;
const MASPV5_VERSION_GROUP_ID: u32 = 0x26A7270A;

#[cfg_attr(feature = "arbitrary", derive(arbitrary::Arbitrary))]
#[derive(
    Clone, Copy, PartialOrd, Ord, PartialEq, Eq, Hash, BorshSerialize, BorshDeserialize, BorshSchema,
)]
pub struct TxId([u8; 32]);

memuse::impl_no_dynamic_usage!(TxId);

impl fmt::Debug for TxId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // The (byte-flipped) hex string is more useful than the raw bytes, because we can
        // look that up in RPC methods and block explorers.
        let txid_str = self.to_string();
        f.debug_tuple("TxId").field(&txid_str).finish()
    }
}

impl fmt::Display for TxId {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut data = self.0;
        data.reverse();
        formatter.write_str(&hex::encode(data))
    }
}

impl AsRef<[u8; 32]> for TxId {
    fn as_ref(&self) -> &[u8; 32] {
        &self.0
    }
}

impl TxId {
    pub fn from_bytes(bytes: [u8; 32]) -> Self {
        TxId(bytes)
    }

    pub fn read<R: Read>(mut reader: R) -> io::Result<Self> {
        let mut hash = [0u8; 32];
        reader.read_exact(&mut hash)?;
        Ok(TxId::from_bytes(hash))
    }

    pub fn write<W: Write>(&self, mut writer: W) -> io::Result<()> {
        writer.write_all(&self.0)?;
        Ok(())
    }
}

/// The set of defined transaction format versions.
///
/// This is serialized in the first four or eight bytes of the transaction format, and
/// represents valid combinations of the `(overwintered, version, version_group_id)`
/// transaction fields. Note that this is not dependent on epoch, only on transaction encoding.
/// For example, if a particular epoch defines a new transaction version but also allows the
/// previous version, then only the new version would be added to this enum.
#[cfg_attr(feature = "arbitrary", derive(arbitrary::Arbitrary))]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TxVersion {
    MASPv5,
}

impl TxVersion {
    pub fn read<R: Read>(mut reader: R) -> io::Result<Self> {
        let header = reader.read_u32::<LittleEndian>()?;
        let version = header & 0x7FFFFFFF;

        match (version, reader.read_u32::<LittleEndian>()?) {
            (MASPV5_TX_VERSION, MASPV5_VERSION_GROUP_ID) => Ok(TxVersion::MASPv5),
            _ => Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                "Unknown transaction format",
            )),
        }
    }

    pub fn header(&self) -> u32 {
        match self {
            TxVersion::MASPv5 => MASPV5_TX_VERSION,
        }
    }

    pub fn version_group_id(&self) -> u32 {
        match self {
            TxVersion::MASPv5 => MASPV5_VERSION_GROUP_ID,
        }
    }

    pub fn write<W: Write>(&self, mut writer: W) -> io::Result<()> {
        writer.write_u32::<LittleEndian>(self.header())?;
        // For consistency with librustzcash & future use
        #[allow(clippy::match_single_binding)]
        match self {
            _ => writer.write_u32::<LittleEndian>(self.version_group_id()),
        }
    }

    pub fn suggested_for_branch(consensus_branch_id: BranchId) -> Self {
        match consensus_branch_id {
            BranchId::MASP => TxVersion::MASPv5,
        }
    }
}

impl BorshSerialize for TxVersion {
    fn serialize<W: Write>(&self, writer: &mut W) -> io::Result<()> {
        self.write(writer)
    }
}

impl BorshDeserialize for TxVersion {
    fn deserialize_reader<R: Read>(reader: &mut R) -> io::Result<Self> {
        Self::read(reader)
    }
}

impl BorshSchema for TxVersion {
    fn add_definitions_recursively(definitions: &mut BTreeMap<Declaration, Definition>) {
        let definition = Definition::Struct {
            fields: Fields::NamedFields(vec![
                ("header".into(), u32::declaration()),
                ("version_group_id".into(), u32::declaration()),
            ]),
        };
        add_definition(Self::declaration(), definition, definitions);
        u32::add_definitions_recursively(definitions);
    }

    fn declaration() -> Declaration {
        "TxVersion".into()
    }
}

/// Authorization state for a bundle of transaction data.
pub trait Authorization {
    type TransparentAuth: transparent::Authorization
        + PartialEq
        + BorshDeserialize
        + BorshSerialize
        + for<'a> MaybeArbitrary<'a>;

    type SaplingAuth: sapling::Authorization
        + PartialEq
        + BorshDeserialize
        + BorshSerialize
        + for<'a> MaybeArbitrary<'a>;
}
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct Unproven;
#[cfg_attr(feature = "arbitrary", derive(arbitrary::Arbitrary))]
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Authorized;

impl Authorization for Authorized {
    type TransparentAuth = transparent::Authorized;
    type SaplingAuth = sapling::Authorized;
}

pub struct Unauthorized<K: crate::zip32::ExtendedKey>(PhantomData<K>);

impl<K: crate::zip32::ExtendedKey + PartialEq + Clone + Debug + for<'a> MaybeArbitrary<'a>>
    Authorization for Unauthorized<K>
{
    type TransparentAuth = transparent::builder::Unauthorized;
    type SaplingAuth = sapling::builder::Unauthorized<K>;
}

/// A MASP transaction.
#[cfg_attr(feature = "arbitrary", derive(arbitrary::Arbitrary))]
#[derive(Debug, Clone)]
pub struct Transaction {
    txid: TxId,
    data: TransactionData<Authorized>,
}

impl Deref for Transaction {
    type Target = TransactionData<Authorized>;

    fn deref(&self) -> &TransactionData<Authorized> {
        &self.data
    }
}

impl PartialEq for Transaction {
    fn eq(&self, other: &Transaction) -> bool {
        self.txid == other.txid
    }
}

#[cfg_attr(feature = "arbitrary", derive(arbitrary::Arbitrary))]
#[derive(Debug, PartialEq, Clone)]
pub struct TransactionData<A: Authorization> {
    version: TxVersion,
    consensus_branch_id: BranchId,
    lock_time: u32,
    expiry_height: BlockHeight,
    transparent_bundle: Option<transparent::Bundle<A::TransparentAuth>>,
    sapling_bundle: Option<sapling::Bundle<A::SaplingAuth>>,
}

impl<A: Authorization> TransactionData<A> {
    pub fn from_parts(
        version: TxVersion,
        consensus_branch_id: BranchId,
        lock_time: u32,
        expiry_height: BlockHeight,
        transparent_bundle: Option<transparent::Bundle<A::TransparentAuth>>,
        sapling_bundle: Option<sapling::Bundle<A::SaplingAuth>>,
    ) -> Self {
        TransactionData {
            version,
            consensus_branch_id,
            lock_time,
            expiry_height,
            transparent_bundle,
            sapling_bundle,
        }
    }

    pub fn version(&self) -> TxVersion {
        self.version
    }

    pub fn consensus_branch_id(&self) -> BranchId {
        self.consensus_branch_id
    }

    pub fn lock_time(&self) -> u32 {
        self.lock_time
    }

    pub fn expiry_height(&self) -> BlockHeight {
        self.expiry_height
    }

    pub fn transparent_bundle(&self) -> Option<&transparent::Bundle<A::TransparentAuth>> {
        self.transparent_bundle.as_ref()
    }

    pub fn sapling_bundle(&self) -> Option<&sapling::Bundle<A::SaplingAuth>> {
        self.sapling_bundle.as_ref()
    }
    pub fn digest<D: TransactionDigest<A>>(&self, digester: D) -> D::Digest {
        digester.combine(
            digester.digest_header(
                self.version,
                self.consensus_branch_id,
                self.lock_time,
                self.expiry_height,
            ),
            digester.digest_transparent(self.transparent_bundle.as_ref()),
            digester.digest_sapling(self.sapling_bundle.as_ref()),
        )
    }

    pub fn map_authorization<B: Authorization>(
        self,
        f_transparent: impl transparent::MapAuth<A::TransparentAuth, B::TransparentAuth>,
        f_sapling: impl sapling::MapAuth<A::SaplingAuth, B::SaplingAuth>,
    ) -> TransactionData<B> {
        TransactionData {
            version: self.version,
            consensus_branch_id: self.consensus_branch_id,
            lock_time: self.lock_time,
            expiry_height: self.expiry_height,
            transparent_bundle: self
                .transparent_bundle
                .map(|b| b.map_authorization(f_transparent)),
            sapling_bundle: self.sapling_bundle.map(|b| b.map_authorization(f_sapling)),
        }
    }
}

impl<A: Authorization> TransactionData<A> {
    pub fn sapling_value_balance(&self) -> I128Sum {
        self.sapling_bundle
            .as_ref()
            .map_or(ValueSum::zero(), |b| b.value_balance.clone())
    }
}

impl TransactionData<Authorized> {
    pub fn freeze(self) -> io::Result<Transaction> {
        Transaction::from_data(self)
    }
}

impl BorshSerialize for Transaction {
    fn serialize<W: Write>(&self, writer: &mut W) -> io::Result<()> {
        self.write(writer)
    }
}

impl BorshDeserialize for Transaction {
    fn deserialize_reader<R: Read>(reader: &mut R) -> io::Result<Self> {
        Self::read(reader, BranchId::MASP)
    }
}

fn untagged_vec<X: BorshSchema>(length_range: RangeInclusive<u64>) -> Definition {
    Definition::Sequence {
        length_width: 0,
        length_range,
        elements: X::declaration(),
    }
}

fn untagged_option<X: BorshSchema>() -> Definition {
    Definition::Enum {
        tag_width: 0,
        variants: vec![
            (0, "None".into(), <()>::declaration()),
            (1, "Some".into(), X::declaration()),
        ],
    }
}

impl BorshSchema for Transaction {
    fn add_definitions_recursively(
        definitions: &mut BTreeMap<borsh::schema::Declaration, borsh::schema::Definition>,
    ) {
        let definition = Definition::Enum {
            tag_width: 1,
            variants: vec![
                (253, "u16".into(), u16::declaration()),
                (254, "u32".into(), u32::declaration()),
                (255, "u64".into(), u64::declaration()),
            ],
        };
        add_definition(
            format!("{}::CompactSize", Self::declaration()),
            definition,
            definitions,
        );
        add_definition(
            format!("{}::vin", Self::declaration()),
            untagged_vec::<TxIn<_>>(u64::MIN..=u64::MAX),
            definitions,
        );
        add_definition(
            format!("{}::vout", Self::declaration()),
            untagged_vec::<TxOut>(u64::MIN..=u64::MAX),
            definitions,
        );
        add_definition(
            format!("{}::sd_v5s", Self::declaration()),
            untagged_vec::<SpendDescriptionV5>(u64::MIN..=u64::MAX),
            definitions,
        );
        add_definition(
            format!("{}::cd_v5s", Self::declaration()),
            untagged_vec::<ConvertDescriptionV5>(u64::MIN..=u64::MAX),
            definitions,
        );
        add_definition(
            format!("{}::od_v5s", Self::declaration()),
            untagged_vec::<OutputDescriptionV5>(u64::MIN..=u64::MAX),
            definitions,
        );
        add_definition(
            format!("{}::value_balance", Self::declaration()),
            untagged_option::<I128Sum>(),
            definitions,
        );
        add_definition(
            format!("{}::spend_anchor", Self::declaration()),
            untagged_option::<[u8; 32]>(),
            definitions,
        );
        add_definition(
            format!("{}::convert_anchor", Self::declaration()),
            untagged_option::<[u8; 32]>(),
            definitions,
        );
        add_definition(
            format!("{}::v_spend_proofs", Self::declaration()),
            untagged_vec::<[u8; GROTH_PROOF_SIZE]>(u64::MIN..=u64::MAX),
            definitions,
        );
        add_definition(
            format!("{}::v_spend_auth_sigs", Self::declaration()),
            untagged_vec::<redjubjub::Signature>(u64::MIN..=u64::MAX),
            definitions,
        );
        add_definition(
            format!("{}::v_convert_proofs", Self::declaration()),
            untagged_vec::<[u8; GROTH_PROOF_SIZE]>(u64::MIN..=u64::MAX),
            definitions,
        );
        add_definition(
            format!("{}::v_output_proofs", Self::declaration()),
            untagged_vec::<[u8; GROTH_PROOF_SIZE]>(u64::MIN..=u64::MAX),
            definitions,
        );
        add_definition(
            format!("{}::authorization", Self::declaration()),
            untagged_option::<sapling::Authorized>(),
            definitions,
        );
        let definition = Definition::Struct {
            fields: Fields::NamedFields(vec![
                ("version".into(), TxVersion::declaration()),
                ("consensus_branch_id".into(), BranchId::declaration()),
                ("lock_time".into(), u32::declaration()),
                ("expiry_height".into(), BlockHeight::declaration()),
                (
                    "vin::count".into(),
                    format!("{}::CompactSize", Self::declaration()),
                ),
                ("vin".into(), format!("{}::vin", Self::declaration())),
                (
                    "vout::count".into(),
                    format!("{}::CompactSize", Self::declaration()),
                ),
                ("vout".into(), format!("{}::vout", Self::declaration())),
                (
                    "sd_v5s::count".into(),
                    format!("{}::CompactSize", Self::declaration()),
                ),
                ("sd_v5s".into(), format!("{}::sd_v5s", Self::declaration())),
                (
                    "cd_v5s::count".into(),
                    format!("{}::CompactSize", Self::declaration()),
                ),
                ("cd_v5s".into(), format!("{}::cd_v5s", Self::declaration())),
                (
                    "od_v5s::count".into(),
                    format!("{}::CompactSize", Self::declaration()),
                ),
                ("od_v5s".into(), format!("{}::od_v5s", Self::declaration())),
                (
                    "value_balance".into(),
                    format!("{}::value_balance", Self::declaration()),
                ),
                (
                    "spend_anchor".into(),
                    format!("{}::spend_anchor", Self::declaration()),
                ),
                (
                    "convert_anchor".into(),
                    format!("{}::convert_anchor", Self::declaration()),
                ),
                (
                    "v_spend_proofs".into(),
                    format!("{}::v_spend_proofs", Self::declaration()),
                ),
                (
                    "v_spend_auth_sigs".into(),
                    format!("{}::v_spend_auth_sigs", Self::declaration()),
                ),
                (
                    "v_convert_proofs".into(),
                    format!("{}::v_convert_proofs", Self::declaration()),
                ),
                (
                    "v_output_proofs".into(),
                    format!("{}::v_output_proofs", Self::declaration()),
                ),
                (
                    "authorization".into(),
                    format!("{}::authorization", Self::declaration()),
                ),
            ]),
        };
        add_definition(Self::declaration(), definition, definitions);
        <[u8; 32]>::add_definitions_recursively(definitions);
        redjubjub::Signature::add_definitions_recursively(definitions);
        <[u8; GROTH_PROOF_SIZE]>::add_definitions_recursively(definitions);
        sapling::Authorized::add_definitions_recursively(definitions);
        I128Sum::add_definitions_recursively(definitions);
        TxIn::add_definitions_recursively(definitions);
        TxOut::add_definitions_recursively(definitions);
        SpendDescriptionV5::add_definitions_recursively(definitions);
        ConvertDescriptionV5::add_definitions_recursively(definitions);
        OutputDescriptionV5::add_definitions_recursively(definitions);
        u8::add_definitions_recursively(definitions);
        u16::add_definitions_recursively(definitions);
        u32::add_definitions_recursively(definitions);
        u64::add_definitions_recursively(definitions);
        TxVersion::add_definitions_recursively(definitions);
        <()>::add_definitions_recursively(definitions);
        BranchId::add_definitions_recursively(definitions);
        BlockHeight::add_definitions_recursively(definitions);
    }

    fn declaration() -> borsh::schema::Declaration {
        "Transaction".into()
    }
}

impl Transaction {
    fn from_data(data: TransactionData<Authorized>) -> io::Result<Self> {
        match data.version {
            TxVersion::MASPv5 => Ok(Self::from_data_v5(data)),
        }
    }
    fn from_data_v5(data: TransactionData<Authorized>) -> Self {
        let txid = to_txid(
            data.version,
            data.consensus_branch_id,
            &data.digest(TxIdDigester),
        );

        Transaction { txid, data }
    }

    pub fn into_data(self) -> TransactionData<Authorized> {
        self.data
    }

    pub fn txid(&self) -> TxId {
        self.txid
    }

    pub fn read<R: Read>(mut reader: R, _consensus_branch_id: BranchId) -> io::Result<Self> {
        let version = TxVersion::read(&mut reader)?;
        match version {
            TxVersion::MASPv5 => Self::read_v5(reader, version),
        }
    }

    fn read_transparent<R: Read>(
        mut reader: R,
    ) -> io::Result<Option<transparent::Bundle<transparent::Authorized>>> {
        let vin = Vector::read(&mut reader, TxIn::read)?;
        let vout = Vector::read(&mut reader, TxOut::read)?;
        Ok(if vin.is_empty() && vout.is_empty() {
            None
        } else {
            Some(transparent::Bundle {
                vin,
                vout,
                authorization: transparent::Authorized,
            })
        })
    }

    fn read_i128_sum<R: Read>(mut reader: R) -> io::Result<I128Sum> {
        I128Sum::read(&mut reader).map_err(|_| {
            io::Error::new(
                io::ErrorKind::InvalidData,
                "Amount valueBalance out of range",
            )
        })
    }

    fn read_v5<R: Read>(mut reader: R, version: TxVersion) -> io::Result<Self> {
        let (consensus_branch_id, lock_time, expiry_height) =
            Self::read_v5_header_fragment(&mut reader)?;
        let transparent_bundle = Self::read_transparent(&mut reader)?;
        let sapling_bundle = Self::read_v5_sapling(&mut reader)?;

        let data = TransactionData {
            version,
            consensus_branch_id,
            lock_time,
            expiry_height,
            transparent_bundle,
            sapling_bundle,
        };

        Ok(Self::from_data_v5(data))
    }

    fn read_v5_header_fragment<R: Read>(mut reader: R) -> io::Result<(BranchId, u32, BlockHeight)> {
        let consensus_branch_id = reader.read_u32::<LittleEndian>().and_then(|value| {
            BranchId::try_from(value).map_err(|e| {
                io::Error::new(
                    io::ErrorKind::InvalidInput,
                    "invalid consensus branch id: ".to_owned() + e,
                )
            })
        })?;
        let lock_time = reader.read_u32::<LittleEndian>()?;
        let expiry_height: BlockHeight = reader.read_u32::<LittleEndian>()?.into();
        Ok((consensus_branch_id, lock_time, expiry_height))
    }

    #[allow(clippy::redundant_closure)]
    fn read_v5_sapling<R: Read>(
        mut reader: R,
    ) -> io::Result<Option<sapling::Bundle<sapling::Authorized>>> {
        let sd_v5s = Vector::read(&mut reader, SpendDescriptionV5::read)?;
        let cd_v5s = Vector::read(&mut reader, ConvertDescriptionV5::read)?;
        let od_v5s = Vector::read(&mut reader, OutputDescriptionV5::read)?;
        let n_spends = sd_v5s.len();
        let n_converts = cd_v5s.len();
        let n_outputs = od_v5s.len();
        let value_balance = if n_spends > 0 || n_converts > 0 || n_outputs > 0 {
            Self::read_i128_sum(&mut reader)?
        } else {
            ValueSum::zero()
        };

        let spend_anchor = if n_spends > 0 {
            Some(sapling::read_base(&mut reader, "spend anchor")?)
        } else {
            None
        };

        let convert_anchor = if n_converts > 0 {
            Some(sapling::read_base(&mut reader, "convert anchor")?)
        } else {
            None
        };

        let v_spend_proofs = Array::read(&mut reader, n_spends, |r| sapling::read_zkproof(r))?;
        let v_spend_auth_sigs = Array::read(&mut reader, n_spends, |r| {
            SpendDescription::read_spend_auth_sig(r)
        })?;
        let v_convert_proofs = Array::read(&mut reader, n_converts, |r| sapling::read_zkproof(r))?;
        let v_output_proofs = Array::read(&mut reader, n_outputs, |r| sapling::read_zkproof(r))?;

        let binding_sig = if n_spends > 0 || n_converts > 0 || n_outputs > 0 {
            Some(redjubjub::Signature::read(&mut reader)?)
        } else {
            None
        };

        let shielded_spends = sd_v5s
            .into_iter()
            .zip(v_spend_proofs.into_iter().zip(v_spend_auth_sigs))
            .map(|(sd_5, (zkproof, spend_auth_sig))| {
                // the following `unwrap` is safe because we know n_spends > 0.
                sd_5.into_spend_description(spend_anchor.unwrap(), zkproof, spend_auth_sig)
            })
            .collect();

        let shielded_converts = cd_v5s
            .into_iter()
            .zip(v_convert_proofs)
            .map(|(cd_5, zkproof)| cd_5.into_convert_description(convert_anchor.unwrap(), zkproof))
            .collect();

        let shielded_outputs = od_v5s
            .into_iter()
            .zip(v_output_proofs)
            .map(|(od_5, zkproof)| od_5.into_output_description(zkproof))
            .collect();

        Ok(binding_sig.map(|binding_sig| sapling::Bundle {
            value_balance,
            shielded_spends,
            shielded_converts,
            shielded_outputs,
            authorization: sapling::Authorized { binding_sig },
        }))
    }
    pub fn write<W: Write>(&self, writer: W) -> io::Result<()> {
        match self.version {
            TxVersion::MASPv5 => self.write_v5(writer),
        }
    }
    pub fn write_transparent<W: Write>(&self, mut writer: W) -> io::Result<()> {
        if let Some(bundle) = &self.transparent_bundle {
            Vector::write(&mut writer, &bundle.vin, |w, e| e.write(w))?;
            Vector::write(&mut writer, &bundle.vout, |w, e| e.write(w))?;
        } else {
            CompactSize::write(&mut writer, 0)?;
            CompactSize::write(&mut writer, 0)?;
        }

        Ok(())
    }

    pub fn write_v5<W: Write>(&self, mut writer: W) -> io::Result<()> {
        self.write_v5_header(&mut writer)?;
        self.write_transparent(&mut writer)?;
        self.write_v5_sapling(&mut writer)?;
        Ok(())
    }

    pub fn write_v5_header<W: Write>(&self, mut writer: W) -> io::Result<()> {
        self.version.write(&mut writer)?;
        writer.write_u32::<LittleEndian>(u32::from(self.consensus_branch_id))?;
        writer.write_u32::<LittleEndian>(self.lock_time)?;
        writer.write_u32::<LittleEndian>(u32::from(self.expiry_height))?;
        Ok(())
    }

    pub fn write_v5_sapling<W: Write>(&self, mut writer: W) -> io::Result<()> {
        if let Some(bundle) = &self.sapling_bundle {
            Vector::write(&mut writer, &bundle.shielded_spends, |w, e| {
                e.write_v5_without_witness_data(w)
            })?;

            Vector::write(&mut writer, &bundle.shielded_converts, |w, e| {
                e.write_v5_without_witness_data(w)
            })?;

            Vector::write(&mut writer, &bundle.shielded_outputs, |w, e| {
                e.write_v5_without_proof(w)
            })?;

            if !(bundle.shielded_spends.is_empty()
                && bundle.shielded_converts.is_empty()
                && bundle.shielded_outputs.is_empty())
            {
                bundle.value_balance.write(&mut writer)?;
            }
            if !bundle.shielded_spends.is_empty() {
                writer.write_all(bundle.shielded_spends[0].anchor.to_repr().as_ref())?;
            }
            if !bundle.shielded_converts.is_empty() {
                writer.write_all(bundle.shielded_converts[0].anchor.to_repr().as_ref())?;
            }

            Array::write(
                &mut writer,
                bundle.shielded_spends.iter().map(|s| s.zkproof),
                |w, e| w.write_all(e),
            )?;
            Array::write(
                &mut writer,
                bundle.shielded_spends.iter().map(|s| s.spend_auth_sig),
                |w, e| e.write(w),
            )?;

            Array::write(
                &mut writer,
                bundle.shielded_converts.iter().map(|s| s.zkproof),
                |w, e| w.write_all(e),
            )?;

            Array::write(
                &mut writer,
                bundle.shielded_outputs.iter().map(|s| s.zkproof),
                |w, e| w.write_all(e),
            )?;

            if !(bundle.shielded_spends.is_empty()
                && bundle.shielded_converts.is_empty()
                && bundle.shielded_outputs.is_empty())
            {
                bundle.authorization.binding_sig.write(&mut writer)?;
            }
        } else {
            CompactSize::write(&mut writer, 0)?;
            CompactSize::write(&mut writer, 0)?;
            CompactSize::write(&mut writer, 0)?;
        }

        Ok(())
    }

    // TODO: should this be moved to `from_data` and stored?
    pub fn auth_commitment(&self) -> Blake2bHash {
        self.data.digest(BlockTxCommitmentDigester)
    }
}

#[derive(Clone, Debug)]
pub struct TransparentDigests<A> {
    pub inputs_digest: A,
    pub outputs_digest: A,
}

#[derive(Clone, Debug)]
pub struct TxDigests<A> {
    pub header_digest: A,
    pub transparent_digests: Option<TransparentDigests<A>>,
    pub sapling_digest: Option<A>,
}

pub trait TransactionDigest<A: Authorization> {
    type HeaderDigest;
    type TransparentDigest;
    type SaplingDigest;
    type Digest;

    fn digest_header(
        &self,
        version: TxVersion,
        consensus_branch_id: BranchId,
        lock_time: u32,
        expiry_height: BlockHeight,
    ) -> Self::HeaderDigest;

    fn digest_transparent(
        &self,
        transparent_bundle: Option<&transparent::Bundle<A::TransparentAuth>>,
    ) -> Self::TransparentDigest;

    fn digest_sapling(
        &self,
        sapling_bundle: Option<&sapling::Bundle<A::SaplingAuth>>,
    ) -> Self::SaplingDigest;

    fn combine(
        &self,
        header_digest: Self::HeaderDigest,
        transparent_digest: Self::TransparentDigest,
        sapling_digest: Self::SaplingDigest,
    ) -> Self::Digest;
}

pub enum DigestError {
    NotSigned,
}

#[cfg(any(test, feature = "test-dependencies"))]
pub mod testing {
    use proptest::prelude::*;

    use crate::consensus::BranchId;

    use super::{
        Authorized, Transaction, TransactionData, TxId, TxVersion,
        components::{
            sapling::testing::{self as sapling},
            transparent::testing::{self as transparent},
        },
    };

    pub fn arb_txid() -> impl Strategy<Value = TxId> {
        prop::array::uniform32(any::<u8>()).prop_map(TxId::from_bytes)
    }

    pub fn arb_tx_version(branch_id: BranchId) -> impl Strategy<Value = TxVersion> {
        match branch_id {
            BranchId::MASP => Just(TxVersion::MASPv5).boxed(),
        }
    }

    prop_compose! {
        pub fn arb_txdata(consensus_branch_id: BranchId)(
            version in arb_tx_version(consensus_branch_id),
        )(
            lock_time in any::<u32>(),
            expiry_height in any::<u32>(),
            transparent_bundle in transparent::arb_bundle(),
            sapling_bundle in sapling::arb_bundle_for_version(version),
            version in Just(version)
        ) -> TransactionData<Authorized> {
            TransactionData {
                version,
                consensus_branch_id,
                lock_time,
                expiry_height: expiry_height.into(),
                transparent_bundle,
                sapling_bundle,
            }
        }
    }

    prop_compose! {
        pub fn arb_tx(branch_id: BranchId)(tx_data in arb_txdata(branch_id)) -> Transaction {
            Transaction::from_data(tx_data).unwrap()
        }
    }
}
