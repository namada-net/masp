use crate::{
    sapling::{
        Node, ValueCommitment,
        pedersen_hash::{Personalization, pedersen_hash},
    },
    transaction::components::amount::{I128Sum, ValueSum},
};
use borsh::BorshSchema;
use borsh::schema::Declaration;
use borsh::schema::Definition;
use borsh::schema::Fields;
use borsh::schema::add_definition;
use borsh::{BorshDeserialize, BorshSerialize};
use group::{Curve, GroupEncoding};
use std::collections::BTreeMap;
use std::{
    io::{self, Write},
    iter::Sum,
    ops::{Add, AddAssign, Neg, Sub, SubAssign},
};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AllowedConversion {
    /// The asset type that the note represents
    assets: I128Sum,
    /// Memorize generator because it's expensive to recompute
    generator: jubjub::ExtendedPoint,
}

impl AllowedConversion {
    pub fn uncommitted() -> bls12_381::Scalar {
        // The smallest u-coordinate that is not on the curve
        // is one.
        bls12_381::Scalar::one()
    }

    /// Computes the note commitment, returning the full point.
    fn cm_full_point(&self) -> jubjub::SubgroupPoint {
        // Calculate the note contents, as bytes
        let mut asset_generator_bytes = vec![];

        // Write the asset generator, cofactor not cleared
        asset_generator_bytes.extend_from_slice(&self.generator.to_bytes());

        assert_eq!(asset_generator_bytes.len(), 32);

        // Compute the Pedersen hash of the note contents
        pedersen_hash(
            Personalization::NoteCommitment,
            asset_generator_bytes
                .into_iter()
                .flat_map(|byte| (0..8).map(move |i| ((byte >> i) & 1) == 1)),
        )
    }

    /// Computes the note commitment
    pub fn cmu(&self) -> bls12_381::Scalar {
        // The commitment is in the prime order subgroup, so mapping the
        // commitment to the u-coordinate is an injective encoding.
        jubjub::ExtendedPoint::from(self.cm_full_point())
            .to_affine()
            .get_u()
    }

    /// Computes the value commitment for a given amount and randomness
    pub fn value_commitment(&self, value: u64, randomness: jubjub::Fr) -> ValueCommitment {
        ValueCommitment {
            asset_generator: self.generator,
            value,
            randomness,
        }
    }
    /// Returns [`self.cmu`] in the correct representation for inclusion in the MASP
    /// AllowedConversions commitment tree.
    pub fn commitment(&self) -> Node {
        Node::from_scalar(self.cmu())
    }
}

impl From<AllowedConversion> for I128Sum {
    fn from(allowed_conversion: AllowedConversion) -> I128Sum {
        allowed_conversion.assets
    }
}

impl From<I128Sum> for AllowedConversion {
    /// Produces an asset generator without cofactor cleared
    fn from(assets: I128Sum) -> Self {
        let mut asset_generator = jubjub::ExtendedPoint::identity();
        for (asset, value) in assets.components() {
            // Compute the absolute value (failing if -i64::MAX is
            // the value)
            let abs = match value.checked_abs() {
                Some(a) => a as u64,
                None => panic!("invalid conversion"),
            };

            // Is it negative? We'll have to negate later if so.
            let is_negative = value.is_negative();

            // Compute it in the exponent
            let mut value_balance = asset.asset_generator() * jubjub::Fr::from(abs);

            // Negate if necessary
            if is_negative {
                value_balance = -value_balance;
            }

            // Add to asset generator
            asset_generator += value_balance;
        }
        AllowedConversion {
            assets,
            generator: asset_generator,
        }
    }
}

impl BorshSchema for AllowedConversion {
    fn add_definitions_recursively(definitions: &mut BTreeMap<Declaration, Definition>) {
        let definition = Definition::Struct {
            fields: Fields::NamedFields(vec![
                ("assets".into(), I128Sum::declaration()),
                ("generator".into(), <[u8; 32]>::declaration()),
            ]),
        };
        add_definition(Self::declaration(), definition, definitions);
        I128Sum::add_definitions_recursively(definitions);
        <[u8; 32]>::add_definitions_recursively(definitions);
    }

    fn declaration() -> Declaration {
        "AllowedConversion".into()
    }
}

impl BorshSerialize for AllowedConversion {
    fn serialize<W: Write>(&self, writer: &mut W) -> io::Result<()> {
        self.assets.write(writer)?;
        writer.write_all(&self.generator.to_bytes())?;
        Ok(())
    }
}

impl BorshDeserialize for AllowedConversion {
    fn deserialize_reader<R: io::Read>(reader: &mut R) -> io::Result<Self> {
        // Use the unchecked reader to ensure that same format is supported
        let unchecked_conv = UncheckedAllowedConversion::deserialize_reader(reader)?.0;
        // Recompute the generator using only the value sum
        let safe_conv: AllowedConversion = unchecked_conv.assets.clone().into();
        // Check that the computed generator is identical to what was read
        if safe_conv.generator == unchecked_conv.generator {
            Ok(safe_conv)
        } else {
            // The generators do not match, so the bytes cannot be from Self::serialize
            Err(io::Error::from(io::ErrorKind::InvalidData))
        }
    }
}

impl Add for AllowedConversion {
    type Output = Self;

    fn add(self, rhs: Self) -> Self {
        Self {
            assets: self.assets + rhs.assets,
            generator: self.generator + rhs.generator,
        }
    }
}

impl AddAssign for AllowedConversion {
    fn add_assign(&mut self, rhs: Self) {
        self.assets += rhs.assets;
        self.generator += rhs.generator;
    }
}

impl Sub for AllowedConversion {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self {
        Self {
            assets: self.assets - rhs.assets,
            generator: self.generator - rhs.generator,
        }
    }
}

impl SubAssign for AllowedConversion {
    fn sub_assign(&mut self, rhs: Self) {
        self.assets -= rhs.assets;
        self.generator -= rhs.generator;
    }
}

impl Neg for AllowedConversion {
    type Output = Self;

    fn neg(self) -> Self {
        Self {
            assets: -self.assets,
            generator: -self.generator,
        }
    }
}

impl Sum for AllowedConversion {
    fn sum<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.fold(AllowedConversion::from(ValueSum::zero()), Add::add)
    }
}

/// A seprate type to allow unchecked deserializations of AllowedConversions
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct UncheckedAllowedConversion(pub AllowedConversion);

impl BorshDeserialize for UncheckedAllowedConversion {
    /// This deserialization is unchecked because it does not do the expensive
    /// computation of checking whether the asset generator corresponds to the
    /// deserialized amount.
    fn deserialize_reader<R: io::Read>(reader: &mut R) -> io::Result<Self> {
        let assets = I128Sum::read(reader)?;
        let gen_bytes =
            <<jubjub::ExtendedPoint as GroupEncoding>::Repr as BorshDeserialize>::deserialize_reader(reader)?;
        let generator = Option::from(jubjub::ExtendedPoint::from_bytes(&gen_bytes))
            .ok_or_else(|| io::Error::from(io::ErrorKind::InvalidData))?;
        // Assume that the generator just read corresponds to the value sum
        Ok(Self(AllowedConversion { assets, generator }))
    }
}

#[cfg(test)]
mod tests {
    use crate::asset_type::AssetType;
    use crate::convert::AllowedConversion;
    use crate::transaction::components::amount::ValueSum;

    /// Generate ZEC asset type
    fn zec() -> AssetType {
        AssetType::new(b"ZEC").unwrap()
    }
    /// Generate BTC asset type
    fn btc() -> AssetType {
        AssetType::new(b"BTC").unwrap()
    }
    /// Generate XAN asset type
    fn xan() -> AssetType {
        AssetType::new(b"XAN").unwrap()
    }
    #[test]
    fn test_homomorphism() {
        // Left operand
        let a = ValueSum::from_pair(zec(), 5i128)
            + ValueSum::from_pair(btc(), 6i128)
            + ValueSum::from_pair(xan(), 7i128);
        // Right operand
        let b = ValueSum::from_pair(zec(), 2i128) + ValueSum::from_pair(xan(), 10i128);
        // Test homomorphism
        assert_eq!(
            AllowedConversion::from(a.clone() + b.clone()),
            AllowedConversion::from(a) + AllowedConversion::from(b)
        );
    }
    #[test]
    fn test_serialization() {
        // Make conversion
        let a: AllowedConversion = (ValueSum::from_pair(zec(), 5i128)
            + ValueSum::from_pair(btc(), 6i128)
            + ValueSum::from_pair(xan(), 7i128))
        .into();
        // Serialize conversion
        let mut data = Vec::new();
        use borsh::BorshSerialize;
        a.serialize(&mut data).unwrap();
        // Deserialize conversion
        let mut ptr = &data[..];
        use borsh::BorshDeserialize;
        let b = AllowedConversion::deserialize(&mut ptr).unwrap();
        // Check that all bytes have been finished
        assert!(
            ptr.is_empty(),
            "AllowedConversion bytes should be exhausted"
        );
        // Test that serializing then deserializing produces same object
        assert_eq!(
            a, b,
            "serialization followed by deserialization changes value"
        );
    }
}
