//! Sapling key components.
//!
//! Implements [section 4.2.2] of the Zcash Protocol Specification.
//!
//! [section 4.2.2]: https://zips.z.cash/protocol/protocol.pdf#saplingkeycomponents

use crate::{
    constants::{proof_generation_key_generator, spending_key_generator},
    keys::prf_expand,
};
use borsh::BorshSchema;
use borsh::schema::Declaration;
use borsh::schema::Definition;
use borsh::schema::Fields;
use borsh::schema::add_definition;
use borsh::{BorshDeserialize, BorshSerialize};
use ff::PrimeField;
use group::{Group, GroupEncoding};
use std::collections::BTreeMap;
use std::{
    fmt::{Display, Formatter},
    hash::{Hash, Hasher},
    io::{self, Read, Write},
    str::FromStr,
};
use subtle::CtOption;

use super::{NullifierDerivingKey, ProofGenerationKey, ViewingKey};

/// Errors that can occur in the decoding of Sapling spending keys.
pub enum DecodingError {
    /// The length of the byte slice provided for decoding was incorrect.
    LengthInvalid { expected: usize, actual: usize },
    /// Could not decode the `ask` bytes to a jubjub field element.
    InvalidAsk,
    /// Could not decode the `nsk` bytes to a jubjub field element.
    InvalidNsk,
}

/// An outgoing viewing key
#[cfg_attr(feature = "arbitrary", derive(arbitrary::Arbitrary))]
#[derive(
    Clone, Copy, Debug, PartialEq, Eq, Hash, BorshSerialize, BorshDeserialize, BorshSchema,
)]
pub struct OutgoingViewingKey(pub [u8; 32]);

/// A Sapling expanded spending key
#[cfg_attr(feature = "arbitrary", derive(arbitrary::Arbitrary))]
#[derive(Clone, PartialEq, Eq, Copy)]
pub struct ExpandedSpendingKey {
    pub ask: jubjub::Fr,
    pub nsk: jubjub::Fr,
    pub ovk: OutgoingViewingKey,
}

impl Hash for ExpandedSpendingKey {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.ask.to_bytes().hash(state);
        self.nsk.to_bytes().hash(state);
        self.ovk.hash(state);
    }
}

impl ExpandedSpendingKey {
    pub fn from_spending_key(sk: &[u8]) -> Self {
        let ask = jubjub::Fr::from_bytes_wide(prf_expand(sk, &[0x00]).as_array());
        let nsk = jubjub::Fr::from_bytes_wide(prf_expand(sk, &[0x01]).as_array());
        let mut ovk = OutgoingViewingKey([0u8; 32]);
        ovk.0
            .copy_from_slice(&prf_expand(sk, &[0x02]).as_bytes()[..32]);
        ExpandedSpendingKey { ask, nsk, ovk }
    }

    pub fn proof_generation_key(&self) -> ProofGenerationKey {
        ProofGenerationKey {
            ak: spending_key_generator() * self.ask,
            nsk: self.nsk,
        }
    }

    /// Decodes the expanded spending key from its serialized representation
    /// as part of the encoding of the extended spending key as defined in
    /// [ZIP 32](https://zips.z.cash/zip-0032)
    pub fn from_bytes(b: &[u8]) -> Result<Self, DecodingError> {
        if b.len() != 96 {
            return Err(DecodingError::LengthInvalid {
                expected: 96,
                actual: b.len(),
            });
        }

        let ask = Option::from(jubjub::Fr::from_repr(b[0..32].try_into().unwrap()))
            .ok_or(DecodingError::InvalidAsk)?;
        let nsk = Option::from(jubjub::Fr::from_repr(b[32..64].try_into().unwrap()))
            .ok_or(DecodingError::InvalidNsk)?;
        let ovk = OutgoingViewingKey(b[64..96].try_into().unwrap());

        Ok(ExpandedSpendingKey { ask, nsk, ovk })
    }

    pub fn read<R: Read>(mut reader: R) -> io::Result<Self> {
        let mut repr = [0u8; 96];
        reader.read_exact(repr.as_mut())?;
        Self::from_bytes(&repr).map_err(|e| match e {
            DecodingError::InvalidAsk => {
                io::Error::new(io::ErrorKind::InvalidData, "ask not in field")
            }
            DecodingError::InvalidNsk => {
                io::Error::new(io::ErrorKind::InvalidData, "nsk not in field")
            }
            DecodingError::LengthInvalid { .. } => unreachable!(),
        })
    }

    pub fn write<W: Write>(&self, mut writer: W) -> io::Result<()> {
        writer.write_all(&self.to_bytes())
    }

    /// Encodes the expanded spending key to the its seralized representation
    /// as part of the encoding of the extended spending key as defined in
    /// [ZIP 32](https://zips.z.cash/zip-0032)
    pub fn to_bytes(&self) -> [u8; 96] {
        let mut result = [0u8; 96];
        result[0..32].copy_from_slice(&self.ask.to_repr());
        result[32..64].copy_from_slice(&self.nsk.to_repr());
        result[64..96].copy_from_slice(&self.ovk.0);
        result
    }
}

/// A Sapling key that provides the capability to view incoming and outgoing transactions.
#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash)]
#[cfg_attr(feature = "arbitrary", derive(arbitrary::Arbitrary))]
pub struct FullViewingKey {
    pub vk: ViewingKey,
    pub ovk: OutgoingViewingKey,
}

impl Display for FullViewingKey {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), std::fmt::Error> {
        write!(f, "{}", hex::encode(self.to_bytes()))
    }
}

impl FromStr for FullViewingKey {
    type Err = io::Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let vec = hex::decode(s).map_err(|x| io::Error::new(std::io::ErrorKind::InvalidData, x))?;
        let mut rdr = vec.as_slice();
        let res = Self::read(&mut rdr)?;
        if !rdr.is_empty() {
            Err(io::Error::from(std::io::ErrorKind::InvalidData))
        } else {
            Ok(res)
        }
    }
}

impl FullViewingKey {
    pub fn from_expanded_spending_key(expsk: &ExpandedSpendingKey) -> Self {
        FullViewingKey {
            vk: ViewingKey {
                ak: spending_key_generator() * expsk.ask,
                nk: NullifierDerivingKey(proof_generation_key_generator() * expsk.nsk),
            },
            ovk: expsk.ovk,
        }
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
        let nk = NullifierDerivingKey(nk.unwrap());

        let mut ovk = [0u8; 32];
        reader.read_exact(&mut ovk)?;

        Ok(FullViewingKey {
            vk: ViewingKey { ak, nk },
            ovk: OutgoingViewingKey(ovk),
        })
    }

    pub fn write<W: Write>(&self, mut writer: W) -> io::Result<()> {
        writer.write_all(&self.vk.ak.to_bytes())?;
        writer.write_all(&self.vk.nk.0.to_bytes())?;
        writer.write_all(&self.ovk.0)?;

        Ok(())
    }

    pub fn to_bytes(&self) -> [u8; 96] {
        let mut result = [0u8; 96];
        self.write(&mut result[..])
            .expect("should be able to serialize a FullViewingKey");
        result
    }
}

impl BorshSerialize for FullViewingKey {
    fn serialize<W: Write>(&self, writer: &mut W) -> io::Result<()> {
        self.write(writer)
    }
}

impl BorshDeserialize for FullViewingKey {
    fn deserialize_reader<R: Read>(reader: &mut R) -> io::Result<Self> {
        Self::read(reader)
    }
}

impl BorshSchema for FullViewingKey {
    fn add_definitions_recursively(definitions: &mut BTreeMap<Declaration, Definition>) {
        let definition = Definition::Struct {
            fields: Fields::NamedFields(vec![
                ("vk".into(), ViewingKey::declaration()),
                ("ovk".into(), OutgoingViewingKey::declaration()),
            ]),
        };
        add_definition(Self::declaration(), definition, definitions);
        ViewingKey::add_definitions_recursively(definitions);
        OutgoingViewingKey::add_definitions_recursively(definitions);
    }

    fn declaration() -> Declaration {
        "FullViewingKey".into()
    }
}

#[cfg(any(test, feature = "test-dependencies"))]
pub mod testing {
    use proptest::collection::vec;
    use proptest::prelude::{any, prop_compose};
    use std::fmt::{self, Debug, Formatter};

    use super::{ExpandedSpendingKey, FullViewingKey};

    impl Debug for ExpandedSpendingKey {
        fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
            write!(f, "Spending keys cannot be Debug-formatted.")
        }
    }

    use crate::sapling::PaymentAddress;
    use crate::zip32::ExtendedFullViewingKey;
    use crate::zip32::testing::arb_extended_spending_key;

    prop_compose! {
        pub fn arb_expanded_spending_key()(v in vec(any::<u8>(), 32..252)) -> ExpandedSpendingKey {
            ExpandedSpendingKey::from_spending_key(&v)
        }
    }

    prop_compose! {
        pub fn arb_full_viewing_key()(sk in arb_expanded_spending_key()) -> FullViewingKey {
            FullViewingKey::from_expanded_spending_key(&sk)
        }
    }

    prop_compose! {
        pub fn arb_shielded_addr()(extsk in arb_extended_spending_key()) -> PaymentAddress {
            let extfvk = ExtendedFullViewingKey::from(&extsk);
            extfvk.default_address().1
        }
    }
}

#[cfg(test)]
mod tests {
    use group::{Group, GroupEncoding};

    use super::FullViewingKey;
    use crate::constants::spending_key_generator;

    #[test]
    fn ak_must_be_prime_order() {
        let mut buf = [0; 96];
        let identity = jubjub::SubgroupPoint::identity();

        // Set both ak and nk to the identity.
        buf[0..32].copy_from_slice(&identity.to_bytes());
        buf[32..64].copy_from_slice(&identity.to_bytes());

        // ak is not allowed to be the identity.
        assert_eq!(
            FullViewingKey::read(&buf[..]).unwrap_err().to_string(),
            "ak not of prime order"
        );

        // Set ak to a basepoint.
        let basepoint = spending_key_generator();
        buf[0..32].copy_from_slice(&basepoint.to_bytes());

        // nk is allowed to be the identity.
        assert!(FullViewingKey::read(&buf[..]).is_ok());
    }
}
