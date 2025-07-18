//! Structs and constants specific to the Sapling shielded pool.

pub mod group_hash;
pub mod keys;
pub mod note_encryption;
pub mod pedersen_hash;
pub mod prover;
pub mod redjubjub;
pub mod util;

use bitvec::{order::Lsb0, view::AsBits};
use blake2s_simd::Params as Blake2sParams;
use borsh::{BorshDeserialize, BorshSerialize};
use byteorder::{LittleEndian, ReadBytesExt, WriteBytesExt};
use ff::{Field, PrimeField};
use group::{cofactor::CofactorGroup, Curve, Group, GroupEncoding};
use incrementalmerkletree::{self, Altitude};
use lazy_static::lazy_static;
use rand_core::{CryptoRng, RngCore};
use std::{
    array::TryFromSliceError,
    cmp::Ordering,
    convert::TryFrom,
    fmt::{Display, Formatter},
    hash::{Hash, Hasher},
    io::{self, Read, Write},
    str::FromStr,
};
use subtle::{Choice, ConstantTimeEq, CtOption};

use crate::{
    asset_type::AssetType,
    constants::{self, SPENDING_KEY_GENERATOR},
    keys::prf_expand,
    merkle_tree::{HashSer, Hashable},
    transaction::components::amount::MAX_MONEY,
};

use self::{
    group_hash::group_hash,
    pedersen_hash::{pedersen_hash, Personalization},
    redjubjub::{PrivateKey, PublicKey, Signature},
};
use borsh::schema::add_definition;
use borsh::schema::Declaration;
use borsh::schema::Definition;
use borsh::schema::Fields;
use borsh::BorshSchema;
use std::collections::BTreeMap;

pub const SAPLING_COMMITMENT_TREE_DEPTH: usize = 32;

/// Compute a parent node in the Sapling commitment tree given its two children.
pub fn merkle_hash(depth: usize, lhs: &[u8; 32], rhs: &[u8; 32]) -> [u8; 32] {
    let lhs = {
        let mut tmp = [false; 256];
        for (a, b) in tmp.iter_mut().zip(lhs.as_bits::<Lsb0>()) {
            *a = *b;
        }
        tmp
    };

    let rhs = {
        let mut tmp = [false; 256];
        for (a, b) in tmp.iter_mut().zip(rhs.as_bits::<Lsb0>()) {
            *a = *b;
        }
        tmp
    };

    jubjub::ExtendedPoint::from(pedersen_hash(
        Personalization::MerkleTree(depth),
        lhs.iter()
            .copied()
            .take(bls12_381::Scalar::NUM_BITS as usize)
            .chain(
                rhs.iter()
                    .copied()
                    .take(bls12_381::Scalar::NUM_BITS as usize),
            ),
    ))
    .to_affine()
    .get_u()
    .to_repr()
}

/// A node within the Sapling commitment tree.
#[cfg_attr(feature = "arbitrary", derive(arbitrary::Arbitrary))]
#[derive(Clone, Copy, Debug, PartialEq, Eq, BorshSerialize, BorshDeserialize, Default)]
pub struct Node {
    repr: [u8; 32],
}

impl PartialOrd for Node {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Node {
    fn cmp(&self, other: &Self) -> Ordering {
        #[repr(C)]
        struct Limb(u64, u64, u64, u64);

        #[repr(C)]
        struct Limbs {
            this: Limb,
            other: Limb,
        }

        // SAFETY: Getting 4 u64 limbs from `repr` is safe,
        // given that the original values are 256-bit
        let limbs: Limbs = unsafe {
            let self_limbs: [u64; 4] = std::mem::transmute_copy(&self.repr);
            let other_limbs: [u64; 4] = std::mem::transmute_copy(&other.repr);

            // NB: Convert the data from its LE representation
            // to our native endianness
            std::mem::transmute((self_limbs.map(u64::from_le), other_limbs.map(u64::from_le)))
        };

        // NB: Compare the values in reverse order,
        // since the original data is LE
        limbs
            .this
            .3
            .cmp(&limbs.other.3)
            .then(limbs.this.2.cmp(&limbs.other.2))
            .then(limbs.this.1.cmp(&limbs.other.1))
            .then(limbs.this.0.cmp(&limbs.other.0))
    }
}

impl Node {
    pub fn new(repr: [u8; 32]) -> Self {
        Node { repr }
    }

    /// Constructs a new note commitment tree node from a [`bls12_381::Scalar`]
    pub fn from_scalar(cmu: bls12_381::Scalar) -> Self {
        Self {
            repr: cmu.to_repr(),
        }
    }
}

impl incrementalmerkletree::Hashable for Node {
    fn empty_leaf() -> Self {
        Node {
            repr: Note::uncommitted().to_repr(),
        }
    }

    fn combine(altitude: Altitude, lhs: &Self, rhs: &Self) -> Self {
        Node {
            repr: merkle_hash(altitude.into(), &lhs.repr, &rhs.repr),
        }
    }

    fn empty_root(altitude: Altitude) -> Self {
        EMPTY_ROOTS[<usize>::from(altitude)]
    }
}

impl HashSer for Node {
    fn read<R: Read>(mut reader: R) -> io::Result<Self> {
        let mut repr = [0u8; 32];
        reader.read_exact(&mut repr)?;
        Ok(Node { repr })
    }

    fn write<W: Write>(&self, mut writer: W) -> io::Result<()> {
        writer.write_all(self.repr.as_ref())
    }
}

impl From<Node> for bls12_381::Scalar {
    fn from(node: Node) -> Self {
        // Tree nodes should be in the prime field.
        bls12_381::Scalar::from_repr(node.repr).unwrap()
    }
}

lazy_static! {
    static ref EMPTY_ROOTS: Vec<Node> = {
        let mut v = vec![Node::blank()];
        for d in 0..SAPLING_COMMITMENT_TREE_DEPTH {
            let next = Node::combine(d, &v[d], &v[d]);
            v.push(next);
        }
        v
    };
}

/// Create the spendAuthSig for a Sapling SpendDescription.
pub fn spend_sig<R: RngCore + CryptoRng>(
    ask: PrivateKey,
    ar: jubjub::Fr,
    sighash: &[u8; 32],
    rng: &mut R,
) -> Signature {
    spend_sig_internal(ask, ar, sighash, rng)
}

pub(crate) fn spend_sig_internal<R: RngCore>(
    ask: PrivateKey,
    ar: jubjub::Fr,
    sighash: &[u8; 32],
    rng: &mut R,
) -> Signature {
    // We compute `rsk`...
    let rsk = ask.randomize(ar);

    // We compute `rk` from there (needed for key prefixing)
    let rk = PublicKey::from_private(&rsk, SPENDING_KEY_GENERATOR);

    // Compute the signature's message for rk/spend_auth_sig
    let mut data_to_be_signed = [0u8; 64];
    data_to_be_signed[0..32].copy_from_slice(&rk.0.to_bytes());
    data_to_be_signed[32..64].copy_from_slice(&sighash[..]);

    // Do the signing
    rsk.sign(&data_to_be_signed, rng, SPENDING_KEY_GENERATOR)
}

#[derive(Clone)]
pub struct ValueCommitment {
    pub asset_generator: jubjub::ExtendedPoint,
    pub value: u64,
    pub randomness: jubjub::Fr,
}

impl ValueCommitment {
    pub fn commitment(&self) -> jubjub::SubgroupPoint {
        (CofactorGroup::clear_cofactor(&self.asset_generator) * jubjub::Fr::from(self.value))
            + (constants::VALUE_COMMITMENT_RANDOMNESS_GENERATOR * self.randomness)
    }
}

#[derive(Clone, Debug)]
pub struct ProofGenerationKey {
    pub ak: jubjub::SubgroupPoint,
    pub nsk: jubjub::Fr,
}

impl ProofGenerationKey {
    pub fn to_viewing_key(&self) -> ViewingKey {
        ViewingKey {
            ak: self.ak,
            nk: NullifierDerivingKey(constants::PROOF_GENERATION_KEY_GENERATOR * self.nsk),
        }
    }
}

impl BorshSerialize for ProofGenerationKey {
    fn serialize<W: Write>(&self, writer: &mut W) -> io::Result<()> {
        writer.write_all(&self.ak.to_bytes())?;
        writer.write_all(&self.nsk.to_repr())?;
        Ok(())
    }
}

impl BorshDeserialize for ProofGenerationKey {
    fn deserialize_reader<R: Read>(reader: &mut R) -> io::Result<Self> {
        let ak = {
            let mut buf = [0u8; 32];
            reader.read_exact(&mut buf)?;
            jubjub::SubgroupPoint::from_bytes(&buf)
        };
        if ak.is_none().into() {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                "ak not in prime-order subgroup",
            ));
        }
        let nsk_bytes = <[u8; 32]>::deserialize_reader(reader)?;
        let nsk = Option::from(jubjub::Fr::from_bytes(&nsk_bytes))
            .ok_or_else(|| io::Error::new(io::ErrorKind::InvalidData, "nsk not in field"))?;
        Ok(Self {
            ak: ak.unwrap(),
            nsk,
        })
    }
}

impl BorshSchema for ProofGenerationKey {
    fn add_definitions_recursively(definitions: &mut BTreeMap<Declaration, Definition>) {
        let definition = Definition::Struct {
            fields: Fields::NamedFields(vec![
                ("ak".into(), <[u8; 32]>::declaration()),
                ("nsk".into(), <[u8; 32]>::declaration()),
            ]),
        };
        add_definition(Self::declaration(), definition, definitions);
        <[u8; 32]>::add_definitions_recursively(definitions);
    }

    fn declaration() -> Declaration {
        "ProofGenerationKey".into()
    }
}

/// A key used to derive the nullifier for a Sapling note.
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "arbitrary", derive(arbitrary::Arbitrary))]
pub struct NullifierDerivingKey(pub jubjub::SubgroupPoint);

impl BorshSerialize for NullifierDerivingKey {
    fn serialize<W: Write>(&self, writer: &mut W) -> io::Result<()> {
        writer.write_all(&self.0.to_bytes())
    }
}

impl BorshDeserialize for NullifierDerivingKey {
    fn deserialize_reader<R: Read>(reader: &mut R) -> io::Result<Self> {
        let nk = {
            let mut buf = [0u8; 32];
            reader.read_exact(&mut buf)?;
            jubjub::SubgroupPoint::from_bytes(&buf)
        };
        if nk.is_none().into() {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                "nk not in prime-order subgroup",
            ));
        }
        Ok(Self(nk.unwrap()))
    }
}

impl BorshSchema for NullifierDerivingKey {
    fn add_definitions_recursively(definitions: &mut BTreeMap<Declaration, Definition>) {
        let definition = Definition::Struct {
            fields: Fields::UnnamedFields(vec![<[u8; 32]>::declaration()]),
        };
        add_definition(Self::declaration(), definition, definitions);
        <[u8; 32]>::add_definitions_recursively(definitions);
    }

    fn declaration() -> Declaration {
        "NullifierDerivingKey".into()
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
#[cfg_attr(feature = "arbitrary", derive(arbitrary::Arbitrary))]
pub struct ViewingKey {
    pub ak: jubjub::SubgroupPoint,
    pub nk: NullifierDerivingKey,
}

impl Hash for ViewingKey {
    fn hash<H>(&self, state: &mut H)
    where
        H: Hasher,
    {
        self.ak.to_bytes().hash(state);
        self.nk.0.to_bytes().hash(state);
    }
}

impl ViewingKey {
    pub fn rk(&self, ar: jubjub::Fr) -> jubjub::SubgroupPoint {
        self.ak + constants::SPENDING_KEY_GENERATOR * ar
    }

    pub fn ivk(&self) -> SaplingIvk {
        let mut h = [0; 32];
        h.copy_from_slice(
            Blake2sParams::new()
                .hash_length(32)
                .personal(constants::CRH_IVK_PERSONALIZATION)
                .to_state()
                .update(&self.ak.to_bytes())
                .update(&self.nk.0.to_bytes())
                .finalize()
                .as_bytes(),
        );

        // Drop the most significant five bits, so it can be interpreted as a scalar.
        h[31] &= 0b0000_0111;

        SaplingIvk(jubjub::Fr::from_repr(h).unwrap())
    }

    pub fn to_payment_address(&self, diversifier: Diversifier) -> Option<PaymentAddress> {
        self.ivk().to_payment_address(diversifier)
    }

    pub fn read<R: Read>(mut reader: R) -> io::Result<Self> {
        let ak = {
            let mut buf = [0u8; 32];
            reader.read_exact(&mut buf)?;
            jubjub::SubgroupPoint::from_bytes(&buf).and_then(|p| CtOption::new(p, !p.is_identity()))
        };
        let nk = {
            let mut buf = [0u8; 32];
            reader.read_exact(&mut buf)?;
            jubjub::SubgroupPoint::from_bytes(&buf)
        };
        if ak.is_none().into() {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                "ak not of prime order",
            ));
        }
        if nk.is_none().into() {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                "nk not in prime-order subgroup",
            ));
        }
        let ak = ak.unwrap();
        let nk = nk.unwrap();

        Ok(ViewingKey {
            ak,
            nk: NullifierDerivingKey(nk),
        })
    }

    pub fn write<W: Write>(&self, mut writer: W) -> io::Result<()> {
        writer.write_all(&self.ak.to_bytes())?;
        writer.write_all(&self.nk.0.to_bytes())?;

        Ok(())
    }

    pub fn to_bytes(&self) -> [u8; 64] {
        let mut result = [0u8; 64];
        self.write(&mut result[..])
            .expect("should be able to serialize a ViewingKey");
        result
    }
}

impl BorshSerialize for ViewingKey {
    fn serialize<W: Write>(&self, writer: &mut W) -> io::Result<()> {
        self.write(writer)
    }
}

impl BorshDeserialize for ViewingKey {
    fn deserialize_reader<R: Read>(reader: &mut R) -> io::Result<Self> {
        Self::read(reader)
    }
}

impl BorshSchema for ViewingKey {
    fn add_definitions_recursively(definitions: &mut BTreeMap<Declaration, Definition>) {
        let definition = Definition::Struct {
            fields: Fields::NamedFields(vec![
                ("ak".into(), <[u8; 32]>::declaration()),
                ("nk".into(), NullifierDerivingKey::declaration()),
            ]),
        };
        add_definition(Self::declaration(), definition, definitions);
        <[u8; 32]>::add_definitions_recursively(definitions);
        NullifierDerivingKey::add_definitions_recursively(definitions);
    }

    fn declaration() -> Declaration {
        "ViewingKey".into()
    }
}

impl PartialOrd for ViewingKey {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for ViewingKey {
    fn cmp(&self, other: &Self) -> Ordering {
        self.to_bytes().cmp(&other.to_bytes())
    }
}

#[derive(Debug, Clone)]
pub struct SaplingIvk(pub jubjub::Fr);

impl SaplingIvk {
    pub fn to_payment_address(&self, diversifier: Diversifier) -> Option<PaymentAddress> {
        diversifier.g_d().and_then(|g_d| {
            let pk_d = g_d * self.0;

            PaymentAddress::from_parts(diversifier, pk_d)
        })
    }

    pub fn to_repr(&self) -> [u8; 32] {
        self.0.to_repr()
    }
}

#[cfg_attr(feature = "arbitrary", derive(arbitrary::Arbitrary))]
#[derive(
    Copy, Clone, Debug, PartialEq, Eq, Hash, BorshSerialize, BorshDeserialize, BorshSchema,
)]
pub struct Diversifier(pub [u8; 11]);

impl Diversifier {
    pub fn g_d(&self) -> Option<jubjub::SubgroupPoint> {
        group_hash(&self.0, constants::KEY_DIVERSIFICATION_PERSONALIZATION)
    }
}

/// A Sapling payment address.
///
/// # Invariants
///
/// `pk_d` is guaranteed to be prime-order (i.e. in the prime-order subgroup of Jubjub,
/// and not the identity).
#[derive(Clone, Copy, Debug)]
pub struct PaymentAddress {
    pk_d: jubjub::SubgroupPoint,
    diversifier: Diversifier,
}

impl PartialEq for PaymentAddress {
    fn eq(&self, other: &Self) -> bool {
        self.pk_d == other.pk_d && self.diversifier == other.diversifier
    }
}

impl Eq for PaymentAddress {}

impl PaymentAddress {
    /// Constructs a PaymentAddress from a diversifier and a Jubjub point.
    ///
    /// Returns None if `pk_d` is the identity.
    pub fn from_parts(diversifier: Diversifier, pk_d: jubjub::SubgroupPoint) -> Option<Self> {
        if pk_d.is_identity().into() {
            None
        } else {
            Some(PaymentAddress { pk_d, diversifier })
        }
    }

    /// Constructs a PaymentAddress from a diversifier and a Jubjub point.
    ///
    /// Only for test code, as this explicitly bypasses the invariant.
    #[cfg(test)]
    #[allow(dead_code)]
    pub(crate) fn from_parts_unchecked(
        diversifier: Diversifier,
        pk_d: jubjub::SubgroupPoint,
    ) -> Self {
        PaymentAddress { pk_d, diversifier }
    }

    /// Parses a PaymentAddress from bytes.
    pub fn from_bytes(bytes: &[u8; 43]) -> Option<Self> {
        let diversifier = {
            let mut tmp = [0; 11];
            tmp.copy_from_slice(&bytes[0..11]);
            Diversifier(tmp)
        };
        // Check that the diversifier is valid
        diversifier.g_d()?;

        let pk_d = jubjub::SubgroupPoint::from_bytes(bytes[11..43].try_into().unwrap());
        if pk_d.is_some().into() {
            PaymentAddress::from_parts(diversifier, pk_d.unwrap())
        } else {
            None
        }
    }

    /// Returns the byte encoding of this `PaymentAddress`.
    pub fn to_bytes(&self) -> [u8; 43] {
        let mut bytes = [0; 43];
        bytes[0..11].copy_from_slice(&self.diversifier.0);
        bytes[11..].copy_from_slice(&self.pk_d.to_bytes());
        bytes
    }

    /// Returns the [`Diversifier`] for this `PaymentAddress`.
    pub fn diversifier(&self) -> &Diversifier {
        &self.diversifier
    }

    /// Returns `pk_d` for this `PaymentAddress`.
    pub fn pk_d(&self) -> &jubjub::SubgroupPoint {
        &self.pk_d
    }

    pub fn g_d(&self) -> Option<jubjub::SubgroupPoint> {
        self.diversifier.g_d()
    }

    pub fn create_note(&self, asset_type: AssetType, value: u64, rseed: Rseed) -> Option<Note> {
        self.g_d().map(|g_d| Note {
            asset_type,
            value,
            rseed,
            g_d,
            pk_d: self.pk_d,
        })
    }
}

impl Display for PaymentAddress {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), std::fmt::Error> {
        write!(f, "{}", hex::encode(self.to_bytes()))
    }
}

impl FromStr for PaymentAddress {
    type Err = io::Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let vec = hex::decode(s).map_err(|x| io::Error::new(io::ErrorKind::InvalidData, x))?;
        BorshDeserialize::try_from_slice(&vec)
    }
}

impl PartialOrd for PaymentAddress {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for PaymentAddress {
    fn cmp(&self, other: &Self) -> Ordering {
        self.to_bytes().cmp(&other.to_bytes())
    }
}
impl Hash for PaymentAddress {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.to_bytes().hash(state)
    }
}

impl BorshSerialize for PaymentAddress {
    fn serialize<W: Write>(&self, writer: &mut W) -> io::Result<()> {
        writer.write(self.to_bytes().as_ref()).and(Ok(()))
    }
}
impl BorshDeserialize for PaymentAddress {
    fn deserialize_reader<R: Read>(reader: &mut R) -> io::Result<Self> {
        let mut data = [0u8; 43];
        reader.read_exact(&mut data)?;
        let res = Self::from_bytes(&data);
        let pa = res.ok_or_else(|| io::Error::from(io::ErrorKind::InvalidData))?;
        Ok(pa)
    }
}
impl BorshSchema for PaymentAddress {
    fn add_definitions_recursively(definitions: &mut BTreeMap<Declaration, Definition>) {
        let definition = Definition::Struct {
            fields: Fields::NamedFields(vec![
                ("diversifier".into(), Diversifier::declaration()),
                ("pk_d".into(), <[u8; 32]>::declaration()),
            ]),
        };
        add_definition(Self::declaration(), definition, definitions);
        Diversifier::add_definitions_recursively(definitions);
        <[u8; 32]>::add_definitions_recursively(definitions);
    }

    fn declaration() -> Declaration {
        "PaymentAddress".into()
    }
}

/// Enum for note randomness before and after [ZIP 212](https://zips.z.cash/zip-0212).
///
/// Before ZIP 212, the note commitment trapdoor `rcm` must be a scalar value.
/// After ZIP 212, the note randomness `rseed` is a 32-byte sequence, used to derive
/// both the note commitment trapdoor `rcm` and the ephemeral private key `esk`.
#[cfg_attr(feature = "arbitrary", derive(arbitrary::Arbitrary))]
#[derive(Copy, Clone, Debug)]
pub enum Rseed {
    BeforeZip212(jubjub::Fr),
    AfterZip212([u8; 32]),
}

impl BorshSchema for Rseed {
    fn add_definitions_recursively(definitions: &mut BTreeMap<Declaration, Definition>) {
        let definition = Definition::Enum {
            tag_width: 1,
            variants: vec![
                (1, "BeforeZip212".into(), <[u8; 32]>::declaration()),
                (2, "AfterZip212".into(), <[u8; 32]>::declaration()),
            ],
        };
        add_definition(Self::declaration(), definition, definitions);
        <[u8; 32]>::add_definitions_recursively(definitions);
    }

    fn declaration() -> Declaration {
        "Rseed".into()
    }
}

impl BorshSerialize for Rseed {
    fn serialize<W: std::io::Write>(&self, writer: &mut W) -> io::Result<()> {
        match self {
            Rseed::BeforeZip212(rcm) => {
                // Write note plaintext lead byte
                writer.write_u8(1)?;
                // Write rseed
                writer.write_all(&rcm.to_repr())
            }
            Rseed::AfterZip212(rseed) => {
                // Write note plaintext lead byte
                writer.write_u8(2)?;
                // Write rseed
                writer.write_all(rseed)
            }
        }?;
        Ok(())
    }
}

impl BorshDeserialize for Rseed {
    fn deserialize_reader<R: Read>(reader: &mut R) -> io::Result<Self> {
        // Read note plaintext lead byte
        let rseed_type = reader.read_u8()?;
        // Read rseed
        let rseed_bytes = <[u8; 32]>::deserialize_reader(reader)?;
        let rseed = if rseed_type == 0x01 {
            let data = Option::from(jubjub::Fr::from_bytes(&rseed_bytes))
                .ok_or_else(|| io::Error::new(io::ErrorKind::InvalidData, "rseed not in field"))?;
            Rseed::BeforeZip212(data)
        } else {
            Rseed::AfterZip212(rseed_bytes)
        };
        Ok(rseed)
    }
}

/// Typesafe wrapper for nullifier values.
#[cfg_attr(feature = "arbitrary", derive(arbitrary::Arbitrary))]
#[derive(
    Copy,
    Clone,
    Debug,
    PartialEq,
    Eq,
    PartialOrd,
    Ord,
    Hash,
    BorshSerialize,
    BorshDeserialize,
    BorshSchema,
)]
pub struct Nullifier(pub [u8; 32]);

impl Nullifier {
    pub fn from_slice(bytes: &[u8]) -> Result<Nullifier, TryFromSliceError> {
        bytes.try_into().map(Nullifier)
    }

    pub fn to_vec(&self) -> Vec<u8> {
        self.0.to_vec()
    }
}
impl AsRef<[u8]> for Nullifier {
    fn as_ref(&self) -> &[u8] {
        &self.0
    }
}

impl ConstantTimeEq for Nullifier {
    fn ct_eq(&self, other: &Self) -> Choice {
        self.0.ct_eq(&other.0)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct NoteValue(u64);

impl TryFrom<u64> for NoteValue {
    type Error = ();

    fn try_from(value: u64) -> Result<Self, Self::Error> {
        if value <= MAX_MONEY {
            Ok(NoteValue(value))
        } else {
            Err(())
        }
    }
}

impl From<NoteValue> for u64 {
    fn from(value: NoteValue) -> u64 {
        value.0
    }
}

#[cfg_attr(feature = "arbitrary", derive(arbitrary::Arbitrary))]
#[derive(Clone, Debug, Copy)]
pub struct Note<R = Rseed> {
    /// The asset type that the note represents
    pub asset_type: AssetType,
    /// The value of the note
    pub value: u64,
    /// The diversified base of the address, GH(d)
    pub g_d: jubjub::SubgroupPoint,
    /// The public key of the address, g_d^ivk
    pub pk_d: jubjub::SubgroupPoint,
    /// rseed
    pub rseed: R,
}

impl PartialEq for Note {
    fn eq(&self, other: &Self) -> bool {
        self.value == other.value
            && self.asset_type == other.asset_type
            && self.g_d == other.g_d
            && self.pk_d == other.pk_d
            && self.rcm() == other.rcm()
    }
}

impl Note {
    pub fn uncommitted() -> bls12_381::Scalar {
        // The smallest u-coordinate that is not on the curve
        // is one.
        bls12_381::Scalar::one()
    }

    /// Computes the note commitment, returning the full point.
    fn cm_full_point(&self) -> jubjub::SubgroupPoint {
        // Calculate the note contents, as bytes
        let mut note_contents = vec![];

        // Write the asset generator, cofactor not cleared
        note_contents.extend_from_slice(&self.asset_type.asset_generator().to_bytes());

        // Writing the value in little endian
        note_contents.write_u64::<LittleEndian>(self.value).unwrap();

        // Write g_d
        note_contents.extend_from_slice(&self.g_d.to_bytes());

        // Write pk_d
        note_contents.extend_from_slice(&self.pk_d.to_bytes());

        assert_eq!(note_contents.len(), 32 + 32 + 32 + 8);

        // Compute the Pedersen hash of the note contents
        let hash_of_contents = pedersen_hash(
            Personalization::NoteCommitment,
            note_contents
                .into_iter()
                .flat_map(|byte| (0..8).map(move |i| ((byte >> i) & 1) == 1)),
        );

        // Compute final commitment
        (constants::NOTE_COMMITMENT_RANDOMNESS_GENERATOR * self.rcm()) + hash_of_contents
    }

    /// Computes the nullifier given the nullifier deriving key and
    /// note position
    pub fn nf(&self, nk: &NullifierDerivingKey, position: u64) -> Nullifier {
        // Compute rho = cm + position.G
        let rho = self.cm_full_point()
            + (constants::NULLIFIER_POSITION_GENERATOR * jubjub::Fr::from(position));

        // Compute nf = BLAKE2s(nk | rho)
        Nullifier::from_slice(
            Blake2sParams::new()
                .hash_length(32)
                .personal(constants::PRF_NF_PERSONALIZATION)
                .to_state()
                .update(&nk.0.to_bytes())
                .update(&rho.to_bytes())
                .finalize()
                .as_bytes(),
        )
        .unwrap()
    }

    /// Computes the note commitment
    pub fn cmu(&self) -> bls12_381::Scalar {
        // The commitment is in the prime order subgroup, so mapping the
        // commitment to the u-coordinate is an injective encoding.
        jubjub::ExtendedPoint::from(self.cm_full_point())
            .to_affine()
            .get_u()
    }

    pub fn rcm(&self) -> jubjub::Fr {
        match self.rseed {
            Rseed::BeforeZip212(rcm) => rcm,
            Rseed::AfterZip212(rseed) => {
                jubjub::Fr::from_bytes_wide(prf_expand(&rseed, &[0x04]).as_array())
            }
        }
    }

    pub fn generate_or_derive_esk<R: RngCore + CryptoRng>(&self, rng: &mut R) -> jubjub::Fr {
        self.generate_or_derive_esk_internal(rng)
    }

    pub(crate) fn generate_or_derive_esk_internal<R: RngCore>(&self, rng: &mut R) -> jubjub::Fr {
        match self.derive_esk() {
            None => jubjub::Fr::random(rng),
            Some(esk) => esk,
        }
    }

    /// Returns the derived `esk` if this note was created after ZIP 212 activated.
    pub fn derive_esk(&self) -> Option<jubjub::Fr> {
        match self.rseed {
            Rseed::BeforeZip212(_) => None,
            Rseed::AfterZip212(rseed) => Some(jubjub::Fr::from_bytes_wide(
                prf_expand(&rseed, &[0x05]).as_array(),
            )),
        }
    }

    /// Returns [`self.cmu`] in the correct representation for inclusion in the Sapling
    /// note commitment tree.
    pub fn commitment(&self) -> Node {
        Node {
            repr: self.cmu().to_repr(),
        }
    }
}

impl<T: BorshSchema> BorshSchema for Note<T> {
    fn add_definitions_recursively(definitions: &mut BTreeMap<Declaration, Definition>) {
        let definition = Definition::Struct {
            fields: Fields::NamedFields(vec![
                ("asset_type".into(), AssetType::declaration()),
                ("value".into(), u64::declaration()),
                ("g_d".into(), <[u8; 32]>::declaration()),
                ("pk_d".into(), <[u8; 32]>::declaration()),
                ("rseed".into(), T::declaration()),
            ]),
        };
        add_definition(Self::declaration(), definition, definitions);
        AssetType::add_definitions_recursively(definitions);
        u64::add_definitions_recursively(definitions);
        <[u8; 32]>::add_definitions_recursively(definitions);
        T::add_definitions_recursively(definitions);
    }

    fn declaration() -> Declaration {
        format!("Note<{}>", T::declaration())
    }
}

impl<T: BorshSerialize> BorshSerialize for Note<T> {
    fn serialize<W: std::io::Write>(&self, writer: &mut W) -> io::Result<()> {
        // Write asset type
        self.asset_type.serialize(writer)?;
        // Write note value
        writer.write_u64::<LittleEndian>(self.value)?;
        // Write diversified base
        writer.write_all(&self.g_d.to_bytes())?;
        // Write diversified transmission key
        writer.write_all(&self.pk_d.to_bytes())?;
        // Write the rseed
        self.rseed.serialize(writer)?;
        Ok(())
    }
}

impl<T: BorshDeserialize> BorshDeserialize for Note<T> {
    fn deserialize_reader<R: Read>(reader: &mut R) -> io::Result<Self> {
        // Read asset type
        let asset_type = AssetType::deserialize_reader(reader)?;
        // Read note value
        let value = reader.read_u64::<LittleEndian>()?;
        // Read diversified base
        let g_d_bytes = <[u8; 32]>::deserialize_reader(reader)?;
        let g_d = Option::from(jubjub::SubgroupPoint::from_bytes(&g_d_bytes))
            .ok_or_else(|| io::Error::new(io::ErrorKind::InvalidData, "g_d not in field"))?;
        // Read diversified transmission key
        let pk_d_bytes = <[u8; 32]>::deserialize_reader(reader)?;
        let pk_d = Option::from(jubjub::SubgroupPoint::from_bytes(&pk_d_bytes))
            .ok_or_else(|| io::Error::new(io::ErrorKind::InvalidData, "pk_d not in field"))?;
        // Read note plaintext lead byte
        let rseed = T::deserialize_reader(reader)?;
        // Finally construct note object
        Ok(Note {
            asset_type,
            value,
            g_d,
            pk_d,
            rseed,
        })
    }
}
#[cfg(any(test, feature = "test-dependencies"))]
pub mod testing {
    use proptest::prelude::*;
    use std::cmp::min;

    use crate::transaction::components::amount::MAX_MONEY;

    use super::{
        keys::testing::arb_full_viewing_key, Diversifier, Node, Note, NoteValue, PaymentAddress,
        Rseed, SaplingIvk,
    };

    prop_compose! {
        pub fn arb_note_value()(value in 0u64..=MAX_MONEY) -> NoteValue {
            NoteValue::try_from(value).unwrap()
        }
    }

    prop_compose! {
        /// The
        pub fn arb_positive_note_value(bound: u64)(
            value in 1u64..=(min(bound, MAX_MONEY))
        ) -> NoteValue {
            NoteValue::try_from(value).unwrap()
        }
    }

    prop_compose! {
        pub fn arb_incoming_viewing_key()(fvk in arb_full_viewing_key()) -> SaplingIvk {
            fvk.vk.ivk()
        }
    }

    pub fn arb_payment_address() -> impl Strategy<Value = PaymentAddress> {
        arb_incoming_viewing_key().prop_flat_map(|ivk: SaplingIvk| {
            any::<[u8; 11]>().prop_filter_map(
                "Sampled diversifier must generate a valid Sapling payment address.",
                move |d| ivk.to_payment_address(Diversifier(d)),
            )
        })
    }

    prop_compose! {
        pub fn arb_node()(value in prop::array::uniform32(prop::num::u8::ANY)) -> Node {
            Node {
                repr: value
            }
        }
    }

    prop_compose! {
        pub fn arb_note(value: NoteValue)(
            asset_type in crate::asset_type::testing::arb_asset_type(),
            addr in arb_payment_address(),
            rseed in prop::array::uniform32(prop::num::u8::ANY).prop_map(Rseed::AfterZip212)
                ) -> Note {
            Note {
                value: value.into(),
                g_d: addr.g_d().unwrap(), // this unwrap is safe because arb_payment_address always generates an address with a valid g_d
                pk_d: *addr.pk_d(),
                rseed,
                asset_type
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use std::cmp::Ordering;

    use bls12_381::Scalar;
    use borsh::BorshDeserialize;
    use ff::PrimeField;
    use proptest::prelude::*;

    use super::Node;
    use crate::{
        sapling::testing::{arb_note, arb_positive_note_value},
        sapling::Note,
        transaction::components::amount::MAX_MONEY,
    };

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(10))]
        #[test]
        fn note_serialization(note in arb_positive_note_value(MAX_MONEY).prop_flat_map(arb_note)) {
            // BorshSerialize
            let borsh = borsh::to_vec(&note).unwrap();
            // BorshDeserialize
            let de_note: Note = BorshDeserialize::deserialize(&mut borsh.as_ref()).unwrap();
            prop_assert_eq!(note, de_note);
        }

        #[test]
        fn node_cmp(
            x in proptest::num::u128::ANY,
            y in proptest::num::u128::ANY,
        ) {
            let x_bls = Scalar::from_u128(x);
            let y_bls = Scalar::from_u128(y);

            let x_node = Node::from_scalar(x_bls);
            let y_node = Node::from_scalar(y_bls);

            // NB: Big integer value less than or eq to modulus
            let big = Scalar::zero().sub(&Scalar::one());
            let big_node = Node::from_scalar(big);

            prop_assert!(big_node > x_node);
            prop_assert!(big_node > y_node);

            // NB: Negate the values, since we subtracted big with x/y
            let big_minus_x_neg = big.sub(&x_bls).neg();
            let big_minus_y_neg = big.sub(&y_bls).neg();

            let node_big_minus_x_neg = Node::from_scalar(big_minus_x_neg);
            let node_big_minus_y_neg = Node::from_scalar(big_minus_y_neg);

            match x.cmp(&y) {
                Ordering::Greater => {
                    prop_assert!(x_node > y_node);
                    prop_assert!(node_big_minus_x_neg > node_big_minus_y_neg);
                }
                Ordering::Less => {
                    prop_assert!(x_node < y_node);
                    prop_assert!(node_big_minus_x_neg < node_big_minus_y_neg);
                }
                Ordering::Equal => {
                    prop_assert!(x_node == y_node);
                    prop_assert!(node_big_minus_x_neg == node_big_minus_y_neg);
                }
            }
        }
    }
}
