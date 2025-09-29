use core::fmt::Debug;

use ff::PrimeField;
use group::GroupEncoding;
use memuse::DynamicUsage;

use std::collections::BTreeMap;
use std::convert::TryInto;
use std::hash::{Hash, Hasher};
use std::io::{self, Read, Write};

use masp_note_encryption::{
    COMPACT_NOTE_SIZE, ENC_CIPHERTEXT_SIZE, EphemeralKeyBytes, ShieldedOutput,
};

use borsh::schema::Definition;
use borsh::schema::Fields;
use borsh::schema::add_definition;
use borsh::{BorshDeserialize, BorshSchema, BorshSerialize};

use crate::{
    MaybeArbitrary, consensus,
    sapling::{
        Nullifier,
        note_encryption::SaplingDomain,
        redjubjub::{self, PublicKey, Signature},
    },
};

use super::{GROTH_PROOF_SIZE, amount::I128Sum};

pub type GrothProofBytes = [u8; GROTH_PROOF_SIZE];

pub mod builder;
pub mod fees;

pub trait Authorization: Debug {
    type Proof: Clone + Debug + PartialEq + Hash + for<'a> MaybeArbitrary<'a>;
    type AuthSig: Clone + Debug + PartialEq + for<'a> MaybeArbitrary<'a>;
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct Unproven;

impl Authorization for Unproven {
    type Proof = ();
    type AuthSig = ();
}

#[cfg_attr(feature = "arbitrary", derive(arbitrary::Arbitrary))]
#[derive(Debug, Copy, Clone, PartialEq, Eq, BorshSerialize, BorshDeserialize, BorshSchema)]
pub struct Authorized {
    pub binding_sig: redjubjub::Signature,
}

impl Authorization for Authorized {
    type Proof = GrothProofBytes;
    type AuthSig = redjubjub::Signature;
}

pub trait MapAuth<A: Authorization, B: Authorization> {
    fn map_proof(&self, p: A::Proof, pos: usize) -> B::Proof;
    fn map_auth_sig(&self, s: A::AuthSig, pos: usize) -> B::AuthSig;
    fn map_authorization(&self, a: A) -> B;
}

/// The identity map.
///
/// This can be used with [`TransactionData::map_authorization`] when you want to map the
/// authorization of a subset of the transaction's bundles.
///
/// [`TransactionData::map_authorization`]: crate::transaction::TransactionData::map_authorization
impl MapAuth<Authorized, Authorized> for () {
    fn map_proof(
        &self,
        p: <Authorized as Authorization>::Proof,
        _pos: usize,
    ) -> <Authorized as Authorization>::Proof {
        p
    }

    fn map_auth_sig(
        &self,
        s: <Authorized as Authorization>::AuthSig,
        _pos: usize,
    ) -> <Authorized as Authorization>::AuthSig {
        s
    }

    fn map_authorization(&self, a: Authorized) -> Authorized {
        a
    }
}

#[cfg_attr(feature = "arbitrary", derive(arbitrary::Arbitrary))]
#[derive(Clone, Debug, PartialEq)]
pub struct Bundle<A: Authorization + PartialEq + BorshSerialize + BorshDeserialize> {
    pub shielded_spends: Vec<SpendDescription<A>>,
    pub shielded_converts: Vec<ConvertDescription<A::Proof>>,
    pub shielded_outputs: Vec<OutputDescription<A::Proof>>,
    pub value_balance: I128Sum,
    pub authorization: A,
}

impl<A: Authorization + PartialEq + BorshSerialize + BorshDeserialize> Bundle<A> {
    pub fn map_authorization<
        B: Authorization + PartialEq + BorshSerialize + BorshDeserialize,
        F: MapAuth<A, B>,
    >(
        self,
        f: F,
    ) -> Bundle<B> {
        Bundle {
            shielded_spends: self
                .shielded_spends
                .into_iter()
                .enumerate()
                .map(|(pos, d)| SpendDescription {
                    cv: d.cv,
                    anchor: d.anchor,
                    nullifier: d.nullifier,
                    rk: d.rk,
                    zkproof: f.map_proof(d.zkproof, pos),
                    spend_auth_sig: f.map_auth_sig(d.spend_auth_sig, pos),
                })
                .collect(),
            shielded_converts: self
                .shielded_converts
                .into_iter()
                .enumerate()
                .map(|(pos, c)| ConvertDescription {
                    cv: c.cv,
                    anchor: c.anchor,
                    zkproof: f.map_proof(c.zkproof, pos),
                })
                .collect(),
            shielded_outputs: self
                .shielded_outputs
                .into_iter()
                .enumerate()
                .map(|(pos, o)| OutputDescription {
                    cv: o.cv,
                    cmu: o.cmu,
                    ephemeral_key: o.ephemeral_key,
                    enc_ciphertext: o.enc_ciphertext,
                    out_ciphertext: o.out_ciphertext,
                    zkproof: f.map_proof(o.zkproof, pos),
                })
                .collect(),
            value_balance: self.value_balance,
            authorization: f.map_authorization(self.authorization),
        }
    }
}

#[cfg_attr(feature = "arbitrary", derive(arbitrary::Arbitrary))]
#[derive(Clone, PartialEq, Eq)]
pub struct SpendDescription<A: Authorization + PartialEq> {
    pub cv: jubjub::ExtendedPoint,
    pub anchor: bls12_381::Scalar,
    pub nullifier: Nullifier,
    pub rk: PublicKey,
    pub zkproof: A::Proof,
    pub spend_auth_sig: A::AuthSig,
}

impl<A: Authorization + PartialEq> std::fmt::Debug for SpendDescription<A> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        write!(
            f,
            "SpendDescription(cv = {:?}, anchor = {:?}, nullifier = {:?}, rk = {:?}, spend_auth_sig = {:?})",
            self.cv, self.anchor, self.nullifier, self.rk, self.spend_auth_sig
        )
    }
}

/// Consensus rules (§4.4) & (§4.5):
/// - Canonical encoding is enforced here.
/// - "Not small order" is enforced in SaplingVerificationContext::(check_spend()/check_output())
///   (located in zcash_proofs::sapling::verifier).
pub fn read_point<R: Read>(mut reader: R, field: &str) -> io::Result<jubjub::ExtendedPoint> {
    let mut bytes = [0u8; 32];
    reader.read_exact(&mut bytes)?;
    let point = jubjub::ExtendedPoint::from_bytes(&bytes);

    if point.is_none().into() {
        Err(io::Error::new(
            io::ErrorKind::InvalidInput,
            format!("invalid {}", field),
        ))
    } else {
        Ok(point.unwrap())
    }
}

/// Consensus rules (§7.3) & (§7.4):
/// - Canonical encoding is enforced here
pub fn read_base<R: Read>(mut reader: R, field: &str) -> io::Result<bls12_381::Scalar> {
    let mut f = [0u8; 32];
    reader.read_exact(&mut f)?;
    Option::from(bls12_381::Scalar::from_repr(f)).ok_or_else(|| {
        io::Error::new(
            io::ErrorKind::InvalidInput,
            format!("{} not in field", field),
        )
    })
}

/// Consensus rules (§4.4) & (§4.5):
/// - Canonical encoding is enforced by the API of SaplingVerificationContext::check_spend()
///   and SaplingVerificationContext::check_output() due to the need to parse this into a
///   bellman::groth16::Proof.
/// - Proof validity is enforced in SaplingVerificationContext::check_spend()
///   and SaplingVerificationContext::check_output()
pub fn read_zkproof<R: Read>(mut reader: R) -> io::Result<GrothProofBytes> {
    let mut zkproof = [0u8; GROTH_PROOF_SIZE];
    reader.read_exact(&mut zkproof)?;
    Ok(zkproof)
}

impl SpendDescription<Authorized> {
    pub fn read_nullifier<R: Read>(mut reader: R) -> io::Result<Nullifier> {
        let mut nullifier = Nullifier([0u8; 32]);
        reader.read_exact(&mut nullifier.0)?;
        Ok(nullifier)
    }

    /// Consensus rules (§4.4):
    /// - Canonical encoding is enforced here.
    /// - "Not small order" is enforced in SaplingVerificationContext::check_spend()
    pub fn read_rk<R: Read>(mut reader: R) -> io::Result<PublicKey> {
        PublicKey::read(&mut reader)
    }

    /// Consensus rules (§4.4):
    /// - Canonical encoding is enforced here.
    /// - Signature validity is enforced in SaplingVerificationContext::check_spend()
    pub fn read_spend_auth_sig<R: Read>(mut reader: R) -> io::Result<Signature> {
        Signature::read(&mut reader)
    }

    pub fn write_v5_without_witness_data<W: Write>(&self, mut writer: W) -> io::Result<()> {
        writer.write_all(&self.cv.to_bytes())?;
        writer.write_all(&self.nullifier.0)?;
        self.rk.write(&mut writer)
    }
}

#[derive(Clone)]
pub struct SpendDescriptionV5 {
    pub cv: jubjub::ExtendedPoint,
    pub nullifier: Nullifier,
    pub rk: PublicKey,
}

impl SpendDescriptionV5 {
    pub fn read<R: Read>(mut reader: &mut R) -> io::Result<Self> {
        let cv = read_point(&mut reader, "cv")?;
        let nullifier = SpendDescription::read_nullifier(&mut reader)?;
        let rk = SpendDescription::read_rk(&mut reader)?;

        Ok(SpendDescriptionV5 { cv, nullifier, rk })
    }

    pub fn into_spend_description(
        self,
        anchor: bls12_381::Scalar,
        zkproof: GrothProofBytes,
        spend_auth_sig: Signature,
    ) -> SpendDescription<Authorized> {
        SpendDescription {
            cv: self.cv,
            anchor,
            nullifier: self.nullifier,
            rk: self.rk,
            zkproof,
            spend_auth_sig,
        }
    }
}

impl BorshDeserialize for SpendDescriptionV5 {
    fn deserialize_reader<R: Read>(reader: &mut R) -> io::Result<Self> {
        Self::read(reader)
    }
}

impl BorshSchema for SpendDescriptionV5 {
    fn add_definitions_recursively(
        definitions: &mut BTreeMap<borsh::schema::Declaration, borsh::schema::Definition>,
    ) {
        let definition = Definition::Struct {
            fields: Fields::NamedFields(vec![
                ("cv".into(), <[u8; 32]>::declaration()),
                ("nullifier".into(), Nullifier::declaration()),
                ("rk".into(), PublicKey::declaration()),
            ]),
        };
        add_definition(Self::declaration(), definition, definitions);
        <[u8; 32]>::add_definitions_recursively(definitions);
        Nullifier::add_definitions_recursively(definitions);
        PublicKey::add_definitions_recursively(definitions);
    }

    fn declaration() -> borsh::schema::Declaration {
        "SpendDescriptionV5".into()
    }
}

#[cfg_attr(feature = "arbitrary", derive(arbitrary::Arbitrary))]
#[derive(Clone, PartialEq, Eq)]
pub struct OutputDescription<Proof: Clone> {
    pub cv: jubjub::ExtendedPoint,
    pub cmu: bls12_381::Scalar,
    pub ephemeral_key: EphemeralKeyBytes,
    pub enc_ciphertext: [u8; 580 + 32],
    pub out_ciphertext: [u8; 80],
    pub zkproof: Proof,
}

impl<Proof: Clone + DynamicUsage> DynamicUsage for OutputDescription<Proof> {
    fn dynamic_usage(&self) -> usize {
        self.zkproof.dynamic_usage()
    }

    fn dynamic_usage_bounds(&self) -> (usize, Option<usize>) {
        self.zkproof.dynamic_usage_bounds()
    }
}

impl<P: consensus::Parameters, Proof: Clone> ShieldedOutput<SaplingDomain<P>, ENC_CIPHERTEXT_SIZE>
    for OutputDescription<Proof>
{
    fn ephemeral_key(&self) -> EphemeralKeyBytes {
        self.ephemeral_key.clone()
    }

    fn cmstar_bytes(&self) -> [u8; 32] {
        self.cmu.to_repr()
    }

    fn enc_ciphertext(&self) -> &[u8; ENC_CIPHERTEXT_SIZE] {
        &self.enc_ciphertext
    }
}

impl<Proof> std::fmt::Debug for OutputDescription<Proof>
where
    Proof: Clone + PartialEq,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        write!(
            f,
            "OutputDescription(cv = {:?}, cmu = {:?}, ephemeral_key = {:?})",
            self.cv, self.cmu, self.ephemeral_key
        )
    }
}

impl OutputDescription<GrothProofBytes> {
    pub fn write_v5_without_proof<W: Write>(&self, mut writer: W) -> io::Result<()> {
        writer.write_all(&self.cv.to_bytes())?;
        writer.write_all(self.cmu.to_repr().as_ref())?;
        writer.write_all(self.ephemeral_key.as_ref())?;
        writer.write_all(&self.enc_ciphertext)?;
        writer.write_all(&self.out_ciphertext)
    }
}

#[derive(Clone)]
pub struct OutputDescriptionV5 {
    pub cv: jubjub::ExtendedPoint,
    pub cmu: bls12_381::Scalar,
    pub ephemeral_key: EphemeralKeyBytes,
    pub enc_ciphertext: [u8; 580 + 32],
    pub out_ciphertext: [u8; 80],
}

memuse::impl_no_dynamic_usage!(OutputDescriptionV5);

impl OutputDescriptionV5 {
    pub fn read<R: Read>(mut reader: &mut R) -> io::Result<Self> {
        let cv = read_point(&mut reader, "cv")?;
        let cmu = read_base(&mut reader, "cmu")?;

        // Consensus rules (§4.5):
        // - Canonical encoding is enforced in librustzcash_sapling_check_output by zcashd
        // - "Not small order" is enforced in SaplingVerificationContext::check_output()
        let mut ephemeral_key = EphemeralKeyBytes([0u8; 32]);
        reader.read_exact(&mut ephemeral_key.0)?;

        let mut enc_ciphertext = [0u8; 580 + 32];
        let mut out_ciphertext = [0u8; 80];
        reader.read_exact(&mut enc_ciphertext)?;
        reader.read_exact(&mut out_ciphertext)?;

        Ok(OutputDescriptionV5 {
            cv,
            cmu,
            ephemeral_key,
            enc_ciphertext,
            out_ciphertext,
        })
    }

    pub fn into_output_description(
        self,
        zkproof: GrothProofBytes,
    ) -> OutputDescription<GrothProofBytes> {
        OutputDescription {
            cv: self.cv,
            cmu: self.cmu,
            ephemeral_key: self.ephemeral_key,
            enc_ciphertext: self.enc_ciphertext,
            out_ciphertext: self.out_ciphertext,
            zkproof,
        }
    }
}

impl BorshDeserialize for OutputDescriptionV5 {
    fn deserialize_reader<R: Read>(reader: &mut R) -> io::Result<Self> {
        Self::read(reader)
    }
}

impl BorshSchema for OutputDescriptionV5 {
    fn add_definitions_recursively(
        definitions: &mut BTreeMap<borsh::schema::Declaration, borsh::schema::Definition>,
    ) {
        let definition = Definition::Struct {
            fields: Fields::NamedFields(vec![
                ("cv".into(), <[u8; 32]>::declaration()),
                ("cmu".into(), <[u8; 32]>::declaration()),
                ("ephemeral_key".into(), EphemeralKeyBytes::declaration()),
                ("enc_ciphertext".into(), <[u8; 580 + 32]>::declaration()),
                ("out_ciphertext".into(), <[u8; 80]>::declaration()),
            ]),
        };
        add_definition(Self::declaration(), definition, definitions);
        <[u8; 32]>::add_definitions_recursively(definitions);
        EphemeralKeyBytes::add_definitions_recursively(definitions);
        <[u8; 580 + 32]>::add_definitions_recursively(definitions);
        <[u8; 80]>::add_definitions_recursively(definitions);
    }

    fn declaration() -> borsh::schema::Declaration {
        "OutputDescriptionV5".into()
    }
}

#[derive(Clone)]
pub struct CompactOutputDescription {
    pub ephemeral_key: EphemeralKeyBytes,
    pub cmu: bls12_381::Scalar,
    pub enc_ciphertext: [u8; COMPACT_NOTE_SIZE],
}

memuse::impl_no_dynamic_usage!(CompactOutputDescription);

impl<A: Clone> From<OutputDescription<A>> for CompactOutputDescription {
    fn from(out: OutputDescription<A>) -> CompactOutputDescription {
        CompactOutputDescription {
            ephemeral_key: out.ephemeral_key,
            cmu: out.cmu,
            enc_ciphertext: out.enc_ciphertext[..COMPACT_NOTE_SIZE].try_into().unwrap(),
        }
    }
}

impl<P: consensus::Parameters> ShieldedOutput<SaplingDomain<P>, COMPACT_NOTE_SIZE>
    for CompactOutputDescription
{
    fn ephemeral_key(&self) -> EphemeralKeyBytes {
        self.ephemeral_key.clone()
    }

    fn cmstar_bytes(&self) -> [u8; 32] {
        self.cmu.to_repr()
    }

    fn enc_ciphertext(&self) -> &[u8; COMPACT_NOTE_SIZE] {
        &self.enc_ciphertext
    }
}
impl<Proof: Clone + PartialOrd> PartialOrd for OutputDescription<Proof> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        (
            self.cv.to_bytes(),
            self.cmu.to_bytes_le(),
            self.ephemeral_key.clone(),
            self.enc_ciphertext,
            self.out_ciphertext,
            self.zkproof.clone(),
        )
            .partial_cmp(&(
                other.cv.to_bytes(),
                other.cmu.to_bytes_le(),
                other.ephemeral_key.clone(),
                other.enc_ciphertext,
                other.out_ciphertext,
                other.zkproof.clone(),
            ))
    }
}
impl<Proof: Clone + Hash> Hash for OutputDescription<Proof> {
    fn hash<H>(&self, state: &mut H)
    where
        H: Hasher,
    {
        self.cv.to_bytes().hash(state);
        self.cmu.to_bytes_le().hash(state);
        self.ephemeral_key.hash(state);
        self.enc_ciphertext.hash(state);
        self.out_ciphertext.hash(state);
        self.zkproof.hash(state);
    }
}

#[cfg_attr(feature = "arbitrary", derive(arbitrary::Arbitrary))]
#[derive(Clone, PartialEq, Eq)]
pub struct ConvertDescription<Proof: PartialEq> {
    pub cv: jubjub::ExtendedPoint,
    pub anchor: bls12_381::Scalar,
    pub zkproof: Proof,
}

impl<Proof: Clone + PartialOrd> PartialOrd for ConvertDescription<Proof> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        (
            self.cv.to_bytes(),
            self.anchor.to_bytes_le(),
            self.zkproof.clone(),
        )
            .partial_cmp(&(
                other.cv.to_bytes(),
                other.anchor.to_bytes_le(),
                other.zkproof.clone(),
            ))
    }
}

impl<Proof: PartialEq + Hash> Hash for ConvertDescription<Proof> {
    fn hash<H>(&self, state: &mut H)
    where
        H: Hasher,
    {
        self.cv.to_bytes().hash(state);
        self.anchor.to_bytes_le().hash(state);
        self.zkproof.hash(state);
    }
}
impl<Proof: PartialEq> std::fmt::Debug for ConvertDescription<Proof> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        write!(
            f,
            "ConvertDescription(cv = {:?}, anchor = {:?})",
            self.cv, self.anchor
        )
    }
}

impl ConvertDescription<GrothProofBytes> {
    pub fn write_v5_without_witness_data<W: Write>(&self, mut writer: W) -> io::Result<()> {
        writer.write_all(&self.cv.to_bytes())
    }
}

#[derive(Clone, PartialEq, Eq)]
pub struct ConvertDescriptionV5 {
    pub cv: jubjub::ExtendedPoint,
}

impl ConvertDescriptionV5 {
    pub fn read<R: Read>(reader: &mut R) -> io::Result<Self> {
        // Consensus rules (§4.4) & (§4.5):
        // - Canonical encoding is enforced here.
        // - "Not small order" is enforced in SaplingVerificationContext::(check_spend()/check_output())
        //   (located in zcash_proofs::sapling::verifier).
        let cv = read_point(reader, "cv")?;

        Ok(ConvertDescriptionV5 { cv })
    }
    pub fn into_convert_description(
        self,
        anchor: bls12_381::Scalar,
        zkproof: GrothProofBytes,
    ) -> ConvertDescription<GrothProofBytes> {
        ConvertDescription {
            cv: self.cv,
            anchor,
            zkproof,
        }
    }
}

impl BorshDeserialize for ConvertDescriptionV5 {
    fn deserialize_reader<R: Read>(reader: &mut R) -> io::Result<Self> {
        Self::read(reader)
    }
}

impl BorshSchema for ConvertDescriptionV5 {
    fn add_definitions_recursively(
        definitions: &mut BTreeMap<borsh::schema::Declaration, borsh::schema::Definition>,
    ) {
        let definition = Definition::Struct {
            fields: Fields::NamedFields(vec![("cv".into(), <[u8; 32]>::declaration())]),
        };
        add_definition(Self::declaration(), definition, definitions);
        <[u8; 32]>::add_definitions_recursively(definitions);
    }

    fn declaration() -> borsh::schema::Declaration {
        "ConvertDescriptionV5".into()
    }
}

#[cfg(any(test, feature = "test-dependencies"))]
pub mod testing {
    use ff::Field;
    use group::{Group, GroupEncoding};
    use proptest::collection::vec;
    use proptest::prelude::*;
    use rand::{SeedableRng, rngs::StdRng};

    use crate::{
        constants::{spending_key_generator, value_commitment_randomness_generator},
        sapling::{
            Nullifier,
            redjubjub::{PrivateKey, PublicKey},
        },
        transaction::{
            TxVersion,
            components::{GROTH_PROOF_SIZE, amount::testing::arb_i128_sum},
        },
    };

    use super::{
        Authorized, Bundle, ConvertDescription, GrothProofBytes, OutputDescription,
        SpendDescription,
    };

    prop_compose! {
        fn arb_extended_point()(rng_seed in prop::array::uniform32(any::<u8>())) -> jubjub::ExtendedPoint {
            let mut rng = StdRng::from_seed(rng_seed);
            let scalar = jubjub::Scalar::random(&mut rng);
            jubjub::ExtendedPoint::generator() * scalar
        }
    }

    prop_compose! {
        /// produce a spend description with invalid data (useful only for serialization
        /// roundtrip testing).
        pub fn arb_spend_description()(
            cv in arb_extended_point(),
            anchor in vec(any::<u8>(), 32)
                .prop_map(|v| <[u8;32]>::try_from(v.as_slice()).unwrap())
                .prop_map(|v| bls12_381::Scalar::from_bytes_le(&v).unwrap()),
            nullifier in prop::array::uniform32(any::<u8>())
                .prop_map(|v| Nullifier::from_slice(&v).unwrap()),
            zkproof in vec(any::<u8>(), GROTH_PROOF_SIZE)
                .prop_map(|v| <[u8;GROTH_PROOF_SIZE]>::try_from(v.as_slice()).unwrap()),
            rng_seed in prop::array::uniform32(prop::num::u8::ANY),
            fake_sighash_bytes in prop::array::uniform32(prop::num::u8::ANY),
        ) -> SpendDescription<Authorized> {
            let mut rng = StdRng::from_seed(rng_seed);
            let sk1 = PrivateKey(jubjub::Fr::random(&mut rng));
            let rk = PublicKey::from_private(&sk1, spending_key_generator());
            SpendDescription {
                cv,
                anchor,
                nullifier,
                rk,
                zkproof,
                spend_auth_sig: sk1.sign(&fake_sighash_bytes, &mut rng, spending_key_generator()),
            }
        }
    }

    prop_compose! {
        /// produce an output description with invalid data (useful only for serialization
        /// roundtrip testing).
        pub fn arb_output_description()(
            cv in arb_extended_point(),
            cmu in vec(any::<u8>(), 32)
                .prop_map(|v| <[u8;32]>::try_from(v.as_slice()).unwrap())
                .prop_map(|v| bls12_381::Scalar::from_bytes_le(&v).unwrap()),
            enc_ciphertext in vec(any::<u8>(), 580+32)
                .prop_map(|v| <[u8;580+32]>::try_from(v.as_slice()).unwrap()),
            epk in arb_extended_point(),
            out_ciphertext in vec(any::<u8>(), 80)
                .prop_map(|v| <[u8;80]>::try_from(v.as_slice()).unwrap()),
            zkproof in vec(any::<u8>(), GROTH_PROOF_SIZE)
                .prop_map(|v| <[u8;GROTH_PROOF_SIZE]>::try_from(v.as_slice()).unwrap()),
        ) -> OutputDescription<GrothProofBytes> {
            OutputDescription {
                cv,
                cmu,
                ephemeral_key: epk.to_bytes().into(),
                enc_ciphertext,
                out_ciphertext,
                zkproof,
            }
        }
    }

    prop_compose! {
        pub fn arb_bundle()(
            shielded_spends in vec(arb_spend_description(), 0..30),
            shielded_converts in vec(arb_convert_description(), 0..30),
            shielded_outputs in vec(arb_output_description(), 0..30),
            value_balance in arb_i128_sum(),
            rng_seed in prop::array::uniform32(prop::num::u8::ANY),
            fake_bvk_bytes in prop::array::uniform32(prop::num::u8::ANY),
        ) -> Option<Bundle<Authorized>> {
            if shielded_spends.is_empty() && shielded_outputs.is_empty() {
                None
            } else {
                let mut rng = StdRng::from_seed(rng_seed);
                let bsk = PrivateKey(jubjub::Fr::random(&mut rng));

                Some(
                    Bundle {
                        shielded_spends,
                        shielded_converts,
                        shielded_outputs,
                        value_balance,
                        authorization: Authorized { binding_sig: bsk.sign(&fake_bvk_bytes, &mut rng, value_commitment_randomness_generator()) },
                    }
                )
            }
        }
    }

    pub fn arb_bundle_for_version(
        _v: TxVersion,
    ) -> impl Strategy<Value = Option<Bundle<Authorized>>> {
        Strategy::boxed(arb_bundle())
    }

    prop_compose! {
        /// produce a convert description with invalid data (useful only for serialization
        /// roundtrip testing).
        pub fn arb_convert_description()(
            cv in arb_extended_point(),
            anchor in vec(any::<u8>(), 32)
                .prop_map(|v| <[u8;32]>::try_from(v.as_slice()).unwrap())
                .prop_map(|v| bls12_381::Scalar::from_bytes_le(&v).unwrap()),
            zkproof in vec(any::<u8>(), GROTH_PROOF_SIZE)
                .prop_map(|v| <[u8;GROTH_PROOF_SIZE]>::try_from(v.as_slice()).unwrap()),
        ) -> ConvertDescription<GrothProofBytes> {
            ConvertDescription {
                cv,
                anchor,
                zkproof,
            }
        }
    }
}
