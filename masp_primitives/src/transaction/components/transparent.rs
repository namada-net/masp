//! Structs representing the components within Zcash transactions.

use borsh::{BorshDeserialize, BorshSchema, BorshSerialize};
use std::fmt::{self, Debug};
use std::io::{self, Read, Write};

use crate::MaybeArbitrary;
use crate::asset_type::AssetType;
use crate::transaction::TransparentAddress;
use borsh::schema::Declaration;
use borsh::schema::Definition;
use borsh::schema::Fields;
use borsh::schema::add_definition;
use std::collections::BTreeMap;

use super::amount::{BalanceError, I128Sum, MAX_MONEY, ValueSum};

pub mod builder;
pub mod fees;

pub trait Authorization: fmt::Debug {
    type TransparentSig: fmt::Debug + Clone + PartialEq + for<'a> MaybeArbitrary<'a>;
}

#[cfg_attr(feature = "arbitrary", derive(arbitrary::Arbitrary))]
#[derive(Debug, Copy, Clone, PartialEq, Eq, BorshSerialize, BorshDeserialize)]
pub struct Authorized;

impl Authorization for Authorized {
    type TransparentSig = ();
}

pub trait MapAuth<A: Authorization, B: Authorization> {
    fn map_script_sig(&self, s: A::TransparentSig, pos: usize) -> B::TransparentSig;
    fn map_authorization(&self, s: A) -> B;
}

/// The identity map.
///
/// This can be used with [`TransactionData::map_authorization`] when you want to map the
/// authorization of a subset of the transaction's bundles.
///
/// [`TransactionData::map_authorization`]: crate::transaction::TransactionData::map_authorization
impl MapAuth<Authorized, Authorized> for () {
    fn map_script_sig(
        &self,
        s: <Authorized as Authorization>::TransparentSig,
        _pos: usize,
    ) -> <Authorized as Authorization>::TransparentSig {
        s
    }

    fn map_authorization(&self, a: Authorized) -> Authorized {
        a
    }
}

#[cfg_attr(feature = "arbitrary", derive(arbitrary::Arbitrary))]
#[derive(Debug, Clone, PartialEq)]
pub struct Bundle<A: Authorization> {
    pub vin: Vec<TxIn<A>>,
    pub vout: Vec<TxOut>,
    pub authorization: A,
}

impl<A: Authorization> Bundle<A> {
    pub fn map_authorization<B: Authorization, F: MapAuth<A, B>>(self, f: F) -> Bundle<B> {
        Bundle {
            vin: self
                .vin
                .into_iter()
                .enumerate()
                .map(|(pos, txin)| TxIn {
                    asset_type: txin.asset_type,
                    address: txin.address,
                    transparent_sig: f.map_script_sig(txin.transparent_sig, pos),
                    value: txin.value,
                })
                .collect(),
            vout: self.vout,
            authorization: f.map_authorization(self.authorization),
        }
    }

    /// The amount of value added to or removed from the transparent pool by the action of this
    /// bundle. A positive value represents that the containing transaction has funds being
    /// transferred out of the transparent pool into shielded pools or to fees; a negative value
    /// means that the containing transaction has funds being transferred into the transparent pool
    /// from the shielded pools.
    pub fn value_balance<E, F>(&self) -> I128Sum
    where
        E: From<BalanceError>,
    {
        let input_sum = self
            .vin
            .iter()
            .map(|p| ValueSum::from_pair(p.asset_type, p.value as i128))
            .sum::<I128Sum>();

        let output_sum = self
            .vout
            .iter()
            .map(|p| ValueSum::from_pair(p.asset_type, p.value as i128))
            .sum::<I128Sum>();

        // Cannot panic when subtracting two positive i64
        input_sum - output_sum
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "arbitrary", derive(arbitrary::Arbitrary))]
pub struct TxIn<A: Authorization> {
    pub asset_type: AssetType,
    pub value: u64,
    pub address: TransparentAddress,
    pub transparent_sig: A::TransparentSig,
}

impl TxIn<Authorized> {
    pub fn read<R: Read>(reader: &mut R) -> io::Result<Self> {
        let asset_type = AssetType::read(reader)?;
        let value = {
            let mut tmp = [0u8; 8];
            reader.read_exact(&mut tmp)?;
            u64::from_le_bytes(tmp)
        };
        if value > MAX_MONEY {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "value out of range",
            ));
        }
        let address = {
            let mut tmp = [0u8; 20];
            reader.read_exact(&mut tmp)?;
            TransparentAddress(tmp)
        };

        Ok(TxIn {
            asset_type,
            value,
            address,
            transparent_sig: (),
        })
    }

    pub fn write<W: Write>(&self, mut writer: W) -> io::Result<()> {
        writer.write_all(self.asset_type.get_identifier())?;
        writer.write_all(&self.value.to_le_bytes())?;
        writer.write_all(&self.address.0)
    }
}

impl BorshSerialize for TxIn<Authorized> {
    fn serialize<W: Write>(&self, writer: &mut W) -> io::Result<()> {
        self.write(writer)
    }
}

impl BorshDeserialize for TxIn<Authorized> {
    fn deserialize_reader<R: Read>(reader: &mut R) -> io::Result<Self> {
        Self::read(reader)
    }
}

impl BorshSchema for TxIn<Authorized> {
    fn add_definitions_recursively(
        definitions: &mut BTreeMap<borsh::schema::Declaration, borsh::schema::Definition>,
    ) {
        let definition = Definition::Struct {
            fields: Fields::NamedFields(vec![
                ("asset_type".into(), AssetType::declaration()),
                ("value".into(), u64::declaration()),
                ("address".into(), TransparentAddress::declaration()),
            ]),
        };
        add_definition(Self::declaration(), definition, definitions);
        AssetType::add_definitions_recursively(definitions);
        u64::add_definitions_recursively(definitions);
        TransparentAddress::add_definitions_recursively(definitions);
    }

    fn declaration() -> borsh::schema::Declaration {
        "TxIn<Authorized>".into()
    }
}

#[derive(Clone, Debug, Hash, PartialOrd, PartialEq, Ord, Eq)]
#[cfg_attr(feature = "arbitrary", derive(arbitrary::Arbitrary))]
pub struct TxOut {
    pub asset_type: AssetType,
    pub value: u64,
    pub address: TransparentAddress,
}

impl TxOut {
    pub fn read<R: Read>(reader: &mut R) -> io::Result<Self> {
        let asset_type = AssetType::read(reader)?;
        let value = {
            let mut tmp = [0u8; 8];
            reader.read_exact(&mut tmp)?;
            u64::from_le_bytes(tmp)
        };
        if value > MAX_MONEY {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "value out of range",
            ));
        }

        let address = {
            let mut tmp = [0u8; 20];
            reader.read_exact(&mut tmp)?;
            TransparentAddress(tmp)
        };

        Ok(TxOut {
            asset_type,
            value,
            address,
        })
    }

    pub fn write<W: Write>(&self, mut writer: W) -> io::Result<()> {
        writer.write_all(self.asset_type.get_identifier())?;
        writer.write_all(&self.value.to_le_bytes())?;
        writer.write_all(&self.address.0)
    }

    /// Returns the address to which the TxOut was sent, if this is a valid P2SH or P2PKH output.
    pub fn recipient_address(&self) -> TransparentAddress {
        self.address
    }
}

impl BorshDeserialize for TxOut {
    fn deserialize_reader<R: Read>(reader: &mut R) -> io::Result<Self> {
        Self::read(reader)
    }
}

impl BorshSerialize for TxOut {
    fn serialize<W: Write>(&self, writer: &mut W) -> io::Result<()> {
        self.write(writer)
    }
}

impl BorshSchema for TxOut {
    fn add_definitions_recursively(definitions: &mut BTreeMap<Declaration, Definition>) {
        let definition = Definition::Struct {
            fields: Fields::NamedFields(vec![
                ("asset_type".into(), AssetType::declaration()),
                ("value".into(), u64::declaration()),
                ("address".into(), TransparentAddress::declaration()),
            ]),
        };
        add_definition(Self::declaration(), definition, definitions);
        AssetType::add_definitions_recursively(definitions);
        u64::add_definitions_recursively(definitions);
        TransparentAddress::add_definitions_recursively(definitions);
    }

    fn declaration() -> Declaration {
        "TxOut".into()
    }
}

#[cfg(any(test, feature = "test-dependencies"))]
pub mod testing {
    use proptest::collection::vec;
    use proptest::prelude::*;

    use crate::transaction::TransparentAddress;
    use crate::transaction::components::amount::testing::arb_nonnegative_amount;

    use super::{Authorized, Bundle, TxIn, TxOut};

    prop_compose! {
        pub fn arb_transparent_address()(value in prop::array::uniform20(prop::num::u8::ANY)) -> TransparentAddress {
            TransparentAddress(value)
        }
    }

    prop_compose! {
        pub fn arb_txin()(amt in arb_nonnegative_amount(), addr in arb_transparent_address()) -> TxIn<Authorized> {
            let (asset_type, value) = amt.components().next().unwrap();
            TxIn { asset_type: *asset_type, value: *value, address: addr, transparent_sig: () }
        }
    }

    prop_compose! {
        pub fn arb_txout()(amt in arb_nonnegative_amount(), addr in arb_transparent_address()) -> TxOut {
            let (asset_type, value) = amt.components().next().unwrap();

            TxOut { asset_type: *asset_type, value: *value, address : addr }
        }
    }

    prop_compose! {
        pub fn arb_bundle()(
            vin in vec(arb_txin(), 0..10),
            vout in vec(arb_txout(), 0..10),
        ) -> Option<Bundle<Authorized>> {
            if vout.is_empty() {
                None
            } else {
                Some(Bundle {vin, vout, authorization: Authorized })
            }
        }
    }
}

#[cfg(test)]
mod test_serialization {
    use super::*;

    /// Simple test that a serialization round trip is the identity
    #[test]
    fn test_roundtrip_txin() {
        let asset_type = AssetType::new_with_nonce(&[1, 2, 3, 4], 1).expect("Test failed");
        let txin = TxIn::<Authorized> {
            asset_type,
            value: MAX_MONEY - 1,
            address: TransparentAddress([12u8; 20]),
            transparent_sig: (),
        };

        let mut buf = vec![];
        txin.write(&mut buf).expect("Test failed");
        let deserialized = TxIn::read::<&[u8]>(&mut buf.as_ref()).expect("Test failed");
        assert_eq!(deserialized, txin);
    }

    /// Simple test that a serialization round trip is the identity
    #[test]
    fn test_roundtrip_txout() {
        let asset_type = AssetType::new_with_nonce(&[1, 2, 3, 4], 1).expect("Test failed");
        let txout = TxOut {
            asset_type,
            value: MAX_MONEY - 1,
            address: TransparentAddress([12u8; 20]),
        };

        let mut buf = vec![];
        txout.write(&mut buf).expect("Test failed");
        let deserialized = TxOut::read::<&[u8]>(&mut buf.as_ref()).expect("Test failed");
        assert_eq!(deserialized, txout);
    }
}
