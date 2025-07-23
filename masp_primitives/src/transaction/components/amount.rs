use crate::asset_type::AssetType;
use borsh::BorshSchema;
use borsh::schema::Fields;
use borsh::schema::add_definition;
use borsh::schema::{Declaration, Definition};
use borsh::{BorshDeserialize, BorshSerialize};
use num_traits::{CheckedAdd, CheckedMul, CheckedNeg, CheckedSub, ConstZero, One, Zero};
use std::cmp::Ordering;
use std::collections::BTreeMap;
use std::collections::btree_map::Keys;
use std::collections::btree_map::{IntoIter, Iter};
use std::hash::Hash;
use std::io::{Read, Write};
use std::iter::Sum;
use std::ops::{Add, AddAssign, Index, Mul, MulAssign, Neg, Sub, SubAssign};
use zcash_encoding::Vector;

pub const MAX_MONEY: u64 = u64::MAX;
lazy_static::lazy_static! {
pub static ref DEFAULT_FEE: U64Sum = ValueSum::from_pair(zec(), 1000);
}
pub type I8Sum = ValueSum<AssetType, i8>;

pub type U8Sum = ValueSum<AssetType, u8>;

pub type I16Sum = ValueSum<AssetType, i16>;

pub type U16Sum = ValueSum<AssetType, u16>;

pub type I32Sum = ValueSum<AssetType, i32>;

pub type U32Sum = ValueSum<AssetType, u32>;

pub type I64Sum = ValueSum<AssetType, i64>;

pub type U64Sum = ValueSum<AssetType, u64>;

pub type I128Sum = ValueSum<AssetType, i128>;

pub type U128Sum = ValueSum<AssetType, u128>;

/// A type-safe representation of some quantity of Zcash.
///
/// An ValueSum can only be constructed from an integer that is within the valid monetary
/// range of `{-MAX_MONEY..MAX_MONEY}` (where `MAX_MONEY` = i64::MAX).
/// However, this range is not preserved as an invariant internally; it is possible to
/// add two valid ValueSums together to obtain an invalid ValueSum. It is the user's
/// responsibility to handle the result of serializing potentially-invalid ValueSums. In
/// particular, a `Transaction` containing serialized invalid ValueSums will be rejected
/// by the network consensus rules.
#[cfg_attr(feature = "arbitrary", derive(arbitrary::Arbitrary))]
#[derive(Clone, Default, Debug, PartialEq, Eq, Hash)]
pub struct ValueSum<
    Unit: Hash + Ord + BorshSerialize + BorshDeserialize,
    Value: BorshSerialize + BorshDeserialize + PartialEq + Eq,
>(BTreeMap<Unit, Value>);

impl<Unit, Value> memuse::DynamicUsage for ValueSum<Unit, Value>
where
    Unit: Hash + Ord + BorshSerialize + BorshDeserialize + Clone,
    Value: BorshSerialize + BorshDeserialize + PartialEq + Eq + Copy + Default + PartialOrd,
{
    #[inline(always)]
    fn dynamic_usage(&self) -> usize {
        unimplemented!()
        //self.0.dynamic_usage()
    }

    #[inline(always)]
    fn dynamic_usage_bounds(&self) -> (usize, Option<usize>) {
        unimplemented!()
        //self.0.dynamic_usage_bounds()
    }
}

impl<Unit, Value> ValueSum<Unit, Value>
where
    Unit: Hash + Ord + BorshSerialize + BorshDeserialize + Clone,
    Value: BorshSerialize + BorshDeserialize + PartialEq + Eq + Copy + Zero + PartialOrd,
{
    /// Creates a non-negative ValueSum from a Value.
    pub fn from_nonnegative(atype: Unit, amount: Value) -> Result<Self, ()> {
        if amount.is_zero() {
            Ok(Self::zero())
        } else if Value::zero() <= amount {
            let mut ret = BTreeMap::new();
            ret.insert(atype, amount);
            Ok(ValueSum(ret))
        } else {
            Err(())
        }
    }

    /// Compute the infimum of two ValueSums
    pub fn inf(&self, rhs: &Self) -> Self {
        let mut comps = BTreeMap::new();
        for (atype, rhs_amount) in rhs.components() {
            let lhs_amount = self.get(atype);
            if lhs_amount <= *rhs_amount && !lhs_amount.is_zero() {
                comps.insert(atype.clone(), lhs_amount);
            } else if lhs_amount > *rhs_amount && !rhs_amount.is_zero() {
                comps.insert(atype.clone(), *rhs_amount);
            }
        }
        ValueSum(comps)
    }

    /// Compute the supremum of two ValueSums
    pub fn sup(&self, rhs: &Self) -> Self {
        let mut comps = BTreeMap::new();
        for (atype, rhs_amount) in rhs.components() {
            let lhs_amount = self.get(atype);
            if lhs_amount <= *rhs_amount && !rhs_amount.is_zero() {
                comps.insert(atype.clone(), *rhs_amount);
            } else if lhs_amount > *rhs_amount && !lhs_amount.is_zero() {
                comps.insert(atype.clone(), lhs_amount);
            }
        }
        ValueSum(comps)
    }
}

impl<Unit, Value> ValueSum<Unit, Value>
where
    Unit: Hash + Ord + BorshSerialize + BorshDeserialize + Clone,
    Value: BorshSerialize + BorshDeserialize + PartialEq + Eq + Copy + Zero,
{
    /// Creates an ValueSum from a Value.
    pub fn from_pair(atype: Unit, amount: Value) -> Self {
        if amount.is_zero() {
            Self::zero()
        } else {
            let mut ret = BTreeMap::new();
            ret.insert(atype, amount);
            ValueSum(ret)
        }
    }

    /// Filters out everything but the given AssetType from this ValueSum
    pub fn project(&self, index: Unit) -> Self {
        let val = self.0.get(&index).copied().unwrap_or(Value::zero());
        Self::from_pair(index, val)
    }

    /// Get the given AssetType within this ValueSum
    pub fn get(&self, index: &Unit) -> Value {
        *self.0.get(index).unwrap_or(&Value::zero())
    }
}

impl<Unit, Value> ValueSum<Unit, Value>
where
    Unit: Hash + Ord + BorshSerialize + BorshDeserialize + Clone,
    Value: BorshSerialize + BorshDeserialize + PartialEq + Eq + Copy,
{
    /// Returns a zero-valued ValueSum.
    pub fn zero() -> Self {
        ValueSum(BTreeMap::new())
    }

    /// Check if ValueSum is zero
    pub fn is_zero(&self) -> bool {
        self.0.is_empty()
    }

    /// Returns an iterator over the amount's non-zero asset-types
    pub fn asset_types(&self) -> Keys<'_, Unit, Value> {
        self.0.keys()
    }

    /// Returns an iterator over the amount's non-zero components
    pub fn components(&self) -> Iter<'_, Unit, Value> {
        self.0.iter()
    }

    /// Returns an iterator over the amount's non-zero components
    pub fn into_components(self) -> IntoIter<Unit, Value> {
        self.0.into_iter()
    }

    /// Filters out the given AssetType from this ValueSum
    pub fn reject(&self, index: Unit) -> Self {
        let mut val = self.clone();
        val.0.remove(&index);
        val
    }
}

impl<Unit, Value> Zero for ValueSum<Unit, Value>
where
    Unit: Hash + Ord + BorshSerialize + BorshDeserialize + Clone,
    Value: BorshSerialize + BorshDeserialize + PartialEq + Eq + Copy,
{
    fn zero() -> Self {
        Self(BTreeMap::new())
    }

    fn is_zero(&self) -> bool {
        self.0.is_empty()
    }
}

impl<Unit, Value> BorshSerialize for ValueSum<Unit, Value>
where
    Unit: Hash + Ord + BorshSerialize + BorshDeserialize + Clone,
    Value: BorshSerialize + BorshDeserialize + PartialEq + Eq + Copy,
{
    fn serialize<W: Write>(&self, writer: &mut W) -> std::io::Result<()> {
        let vec: Vec<_> = self.components().collect();
        Vector::write(writer, vec.as_ref(), |writer, elt| {
            elt.0.serialize(writer)?;
            elt.1.serialize(writer)?;
            Ok(())
        })
    }
}

impl<Unit, Value> BorshDeserialize for ValueSum<Unit, Value>
where
    Unit: Hash + Ord + BorshSerialize + BorshDeserialize,
    Value: BorshSerialize + BorshDeserialize + PartialEq + Eq,
{
    fn deserialize_reader<R: Read>(reader: &mut R) -> std::io::Result<Self> {
        let vec = Vector::read(reader, |reader| {
            let atype = Unit::deserialize_reader(reader)?;
            let value = Value::deserialize_reader(reader)?;
            Ok((atype, value))
        })?;
        Ok(Self(vec.into_iter().collect()))
    }
}

impl<Unit, Value> BorshSchema for ValueSum<Unit, Value>
where
    Unit: Hash + Ord + BorshSerialize + BorshDeserialize + BorshSchema,
    Value: BorshSerialize + BorshDeserialize + PartialEq + Eq + BorshSchema,
{
    fn add_definitions_recursively(definitions: &mut BTreeMap<Declaration, Definition>) {
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
        let definition = Definition::Sequence {
            length_width: 0,
            length_range: u64::MIN..=u64::MAX,
            elements: <(Unit, Value)>::declaration(),
        };
        add_definition(
            format!("{}::Sequence", Self::declaration()),
            definition,
            definitions,
        );
        let definition = Definition::Struct {
            fields: Fields::UnnamedFields(vec![
                format!("{}::CompactSize", Self::declaration()),
                format!("{}::Sequence", Self::declaration()),
            ]),
        };
        add_definition(Self::declaration(), definition, definitions);
        u16::add_definitions_recursively(definitions);
        u32::add_definitions_recursively(definitions);
        u64::add_definitions_recursively(definitions);
        <(Unit, Value)>::add_definitions_recursively(definitions);
    }

    fn declaration() -> Declaration {
        format!(
            r#"ValueSum<{}, {}>"#,
            Unit::declaration(),
            Value::declaration()
        )
    }
}

impl ValueSum<AssetType, i32> {
    /// Deserialize an ValueSum object from a list of amounts denominated by
    /// different assets
    pub fn read<R: Read>(reader: &mut R) -> std::io::Result<Self> {
        let vec = Vector::read(reader, |reader| {
            let atype = AssetType::read(reader)?;
            let mut value = [0; 4];
            reader.read_exact(&mut value)?;
            Ok((atype, i32::from_le_bytes(value)))
        })?;
        let mut ret = Self::zero();
        for (atype, amt) in vec {
            ret += Self::from_pair(atype, amt);
        }
        Ok(ret)
    }

    /// Serialize an ValueSum object into a list of amounts denominated by
    /// distinct asset types
    pub fn write<W: Write>(&self, writer: &mut W) -> std::io::Result<()> {
        let vec: Vec<_> = self.components().collect();
        Vector::write(writer, vec.as_ref(), |writer, elt| {
            writer.write_all(elt.0.get_identifier())?;
            writer.write_all(elt.1.to_le_bytes().as_ref())?;
            Ok(())
        })
    }
}

impl ValueSum<AssetType, i64> {
    /// Deserialize an ValueSum object from a list of amounts denominated by
    /// different assets
    pub fn read<R: Read>(reader: &mut R) -> std::io::Result<Self> {
        let vec = Vector::read(reader, |reader| {
            let atype = AssetType::read(reader)?;
            let mut value = [0; 8];
            reader.read_exact(&mut value)?;
            Ok((atype, i64::from_le_bytes(value)))
        })?;
        let mut ret = Self::zero();
        for (atype, amt) in vec {
            ret += Self::from_pair(atype, amt);
        }
        Ok(ret)
    }

    /// Serialize an ValueSum object into a list of amounts denominated by
    /// distinct asset types
    pub fn write<W: Write>(&self, writer: &mut W) -> std::io::Result<()> {
        let vec: Vec<_> = self.components().collect();
        Vector::write(writer, vec.as_ref(), |writer, elt| {
            writer.write_all(elt.0.get_identifier())?;
            writer.write_all(elt.1.to_le_bytes().as_ref())?;
            Ok(())
        })
    }
}

impl ValueSum<AssetType, i128> {
    /// Deserialize an ValueSum object from a list of amounts denominated by
    /// different assets
    pub fn read<R: Read>(reader: &mut R) -> std::io::Result<Self> {
        let vec = Vector::read(reader, |reader| {
            let atype = AssetType::read(reader)?;
            let mut value = [0; 16];
            reader.read_exact(&mut value)?;
            Ok((atype, i128::from_le_bytes(value)))
        })?;
        let mut ret = Self::zero();
        for (atype, amt) in vec {
            ret += Self::from_pair(atype, amt);
        }
        Ok(ret)
    }

    /// Serialize an ValueSum object into a list of amounts denominated by
    /// distinct asset types
    pub fn write<W: Write>(&self, writer: &mut W) -> std::io::Result<()> {
        let vec: Vec<_> = self.components().collect();
        Vector::write(writer, vec.as_ref(), |writer, elt| {
            writer.write_all(elt.0.get_identifier())?;
            writer.write_all(elt.1.to_le_bytes().as_ref())?;
            Ok(())
        })
    }
}

impl<Unit, Value> From<Unit> for ValueSum<Unit, Value>
where
    Unit: Hash + Ord + BorshSerialize + BorshDeserialize,
    Value: BorshSerialize + BorshDeserialize + PartialEq + Eq + Copy + One,
{
    fn from(atype: Unit) -> Self {
        let mut ret = BTreeMap::new();
        ret.insert(atype, Value::one());
        ValueSum(ret)
    }
}

impl<Unit, Value> PartialOrd for ValueSum<Unit, Value>
where
    Unit: Hash + Ord + BorshSerialize + BorshDeserialize + Clone,
    Value: BorshSerialize + BorshDeserialize + PartialEq + Eq + Copy + Zero + PartialOrd,
{
    /// One ValueSum is more than or equal to another if each corresponding
    /// coordinate is more than or equal to the other's.
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        let zero = Value::zero();
        let mut ordering = Some(Ordering::Equal);
        for k in self.0.keys().chain(other.0.keys()) {
            let v1 = self.0.get(k).unwrap_or(&zero);
            let v2 = other.0.get(k).unwrap_or(&zero);
            match (v1.partial_cmp(v2), ordering) {
                // Sums cannot be compared if even a single coordinate cannot be
                // compared
                (None, _) => ordering = None,
                // If sums are uncomparable, less, greater, or equal, another
                // equal coordinate will not change that
                (Some(Ordering::Equal), _) => {}
                // A lesser coordinate is inconsistent with the sum being
                // greater, and vice-versa
                (Some(Ordering::Less), Some(Ordering::Greater) | None) => ordering = None,
                (Some(Ordering::Greater), Some(Ordering::Less) | None) => ordering = None,
                // It only takes one lesser coordinate, to make a sum that
                // otherwise would have been equal, to be lesser
                (Some(Ordering::Less), Some(Ordering::Less | Ordering::Equal)) => {
                    ordering = Some(Ordering::Less)
                }
                (Some(Ordering::Greater), Some(Ordering::Greater | Ordering::Equal)) => {
                    ordering = Some(Ordering::Greater)
                }
            }
        }
        ordering
    }
}

macro_rules! impl_index {
    ($struct_type:ty) => {
        impl<Unit> Index<&Unit> for ValueSum<Unit, $struct_type>
        where
            Unit: Hash + Ord + BorshSerialize + BorshDeserialize,
        {
            type Output = $struct_type;
            /// Query how much of the given asset this amount contains
            fn index(&self, index: &Unit) -> &Self::Output {
                self.0
                    .get(index)
                    .unwrap_or(&<$struct_type as ConstZero>::ZERO)
            }
        }
    };
}

impl_index!(i8);

impl_index!(u8);

impl_index!(i16);

impl_index!(u16);

impl_index!(i32);

impl_index!(u32);

impl_index!(i64);

impl_index!(u64);

impl_index!(i128);

impl_index!(u128);

impl<Unit, Lhs, Rhs> MulAssign<Rhs> for ValueSum<Unit, Lhs>
where
    Unit: Hash + Ord + BorshSerialize + BorshDeserialize + Clone,
    Lhs: BorshSerialize
        + BorshDeserialize
        + PartialEq
        + Eq
        + Copy
        + Zero
        + CheckedMul<Rhs, Output = Lhs>,
    Rhs: Copy,
{
    fn mul_assign(&mut self, rhs: Rhs) {
        *self = self.clone() * &rhs;
    }
}

impl<Unit, Lhs, Rhs> Mul<&Rhs> for ValueSum<Unit, Lhs>
where
    Unit: Hash + Ord + BorshSerialize + BorshDeserialize + Clone,
    Lhs: BorshSerialize + BorshDeserialize + PartialEq + Eq + Copy + Zero + CheckedMul<Rhs>,
    Rhs: Copy,
    <Lhs as CheckedMul<Rhs>>::Output: Zero + BorshSerialize + BorshDeserialize + Eq,
{
    type Output = ValueSum<Unit, <Lhs as CheckedMul<Rhs>>::Output>;

    fn mul(self, rhs: &Rhs) -> Self::Output {
        self.checked_mul(rhs).expect("overflow detected")
    }
}

impl<Unit, Lhs, Rhs> CheckedMul<&Rhs> for ValueSum<Unit, Lhs>
where
    Unit: Hash + Ord + BorshSerialize + BorshDeserialize + Clone,
    Lhs: BorshSerialize + BorshDeserialize + PartialEq + Eq + Copy + Zero + CheckedMul<Rhs>,
    Rhs: Copy,
    <Lhs as CheckedMul<Rhs>>::Output: Zero + BorshSerialize + BorshDeserialize + Eq,
{
    type Output = ValueSum<Unit, <Lhs as CheckedMul<Rhs>>::Output>;

    fn checked_mul(self, rhs: &Rhs) -> Option<Self::Output> {
        let mut comps = BTreeMap::new();
        for (atype, amount) in self.0.iter() {
            comps.insert(atype.clone(), amount.checked_mul(*rhs)?);
        }
        comps.retain(|_, v| *v != <Lhs as CheckedMul<Rhs>>::Output::zero());
        Some(ValueSum(comps))
    }
}

impl<Unit, Lhs, Rhs> AddAssign<&ValueSum<Unit, Rhs>> for ValueSum<Unit, Lhs>
where
    Unit: Hash + Ord + BorshSerialize + BorshDeserialize + Clone,
    Lhs: BorshSerialize
        + BorshDeserialize
        + PartialEq
        + Eq
        + Copy
        + Zero
        + CheckedAdd<Rhs, Output = Lhs>,
    Rhs: BorshSerialize + BorshDeserialize + PartialEq + Eq + Copy + Zero,
{
    fn add_assign(&mut self, rhs: &ValueSum<Unit, Rhs>) {
        *self = self.clone() + rhs;
    }
}

impl<Unit, Lhs, Rhs> AddAssign<ValueSum<Unit, Rhs>> for ValueSum<Unit, Lhs>
where
    Unit: Hash + Ord + BorshSerialize + BorshDeserialize + Clone,
    Lhs: BorshSerialize
        + BorshDeserialize
        + PartialEq
        + Eq
        + Copy
        + Zero
        + CheckedAdd<Rhs, Output = Lhs>,
    Rhs: BorshSerialize + BorshDeserialize + PartialEq + Eq + Copy + Zero,
{
    fn add_assign(&mut self, rhs: ValueSum<Unit, Rhs>) {
        *self += &rhs
    }
}

impl<Unit, Lhs, Rhs> Add<&ValueSum<Unit, Rhs>> for ValueSum<Unit, Lhs>
where
    Unit: Hash + Ord + BorshSerialize + BorshDeserialize + Clone,
    Lhs: BorshSerialize + BorshDeserialize + PartialEq + Eq + Copy + Zero + CheckedAdd<Rhs>,
    Rhs: BorshSerialize + BorshDeserialize + PartialEq + Eq + Copy + Zero,
    <Lhs as CheckedAdd<Rhs>>::Output: BorshSerialize + BorshDeserialize + Eq + Zero,
{
    type Output = ValueSum<Unit, <Lhs as CheckedAdd<Rhs>>::Output>;

    fn add(self, rhs: &ValueSum<Unit, Rhs>) -> Self::Output {
        self.checked_add(rhs).expect("overflow detected")
    }
}

impl<Unit, Lhs, Rhs> Add<ValueSum<Unit, Rhs>> for ValueSum<Unit, Lhs>
where
    Unit: Hash + Ord + BorshSerialize + BorshDeserialize + Clone,
    Lhs: BorshSerialize + BorshDeserialize + PartialEq + Eq + Copy + Zero + CheckedAdd<Rhs>,
    Rhs: BorshSerialize + BorshDeserialize + PartialEq + Eq + Copy + Zero,
    <Lhs as CheckedAdd<Rhs>>::Output: BorshSerialize + BorshDeserialize + Eq + Zero,
{
    type Output = ValueSum<Unit, <Lhs as CheckedAdd<Rhs>>::Output>;

    fn add(self, rhs: ValueSum<Unit, Rhs>) -> Self::Output {
        self + &rhs
    }
}

impl<Unit, Lhs, Rhs> CheckedAdd<&ValueSum<Unit, Rhs>> for &ValueSum<Unit, Lhs>
where
    Unit: Hash + Ord + BorshSerialize + BorshDeserialize + Clone,
    Lhs: BorshSerialize + BorshDeserialize + PartialEq + Eq + Copy + Zero + CheckedAdd<Rhs>,
    Rhs: BorshSerialize + BorshDeserialize + PartialEq + Eq + Copy + Zero,
    <Lhs as CheckedAdd<Rhs>>::Output: BorshSerialize + BorshDeserialize + Eq + Zero,
{
    type Output = ValueSum<Unit, <Lhs as CheckedAdd<Rhs>>::Output>;

    fn checked_add(self, v: &ValueSum<Unit, Rhs>) -> Option<Self::Output> {
        let mut comps = BTreeMap::new();
        for (atype, amount) in self.components() {
            comps.insert(atype.clone(), amount.checked_add(Rhs::zero())?);
        }
        for (atype, amount) in v.components() {
            comps.insert(atype.clone(), self.get(atype).checked_add(*amount)?);
        }
        comps.retain(|_, v| *v != <Lhs as CheckedAdd<Rhs>>::Output::zero());
        Some(ValueSum(comps))
    }
}

impl<Unit, Lhs, Rhs> SubAssign<&ValueSum<Unit, Rhs>> for ValueSum<Unit, Lhs>
where
    Unit: Hash + Ord + BorshSerialize + BorshDeserialize + Clone,
    Lhs: BorshSerialize
        + BorshDeserialize
        + PartialEq
        + Eq
        + Copy
        + Zero
        + CheckedSub<Rhs, Output = Lhs>,
    Rhs: BorshSerialize + BorshDeserialize + PartialEq + Eq + Copy + Zero,
{
    fn sub_assign(&mut self, rhs: &ValueSum<Unit, Rhs>) {
        *self = self.clone() - rhs
    }
}

impl<Unit, Lhs, Rhs> SubAssign<ValueSum<Unit, Rhs>> for ValueSum<Unit, Lhs>
where
    Unit: Hash + Ord + BorshSerialize + BorshDeserialize + Clone,
    Lhs: BorshSerialize
        + BorshDeserialize
        + PartialEq
        + Eq
        + Copy
        + Zero
        + CheckedSub<Rhs, Output = Lhs>,
    Rhs: BorshSerialize + BorshDeserialize + PartialEq + Eq + Copy + Zero,
{
    fn sub_assign(&mut self, rhs: ValueSum<Unit, Rhs>) {
        *self -= &rhs
    }
}

impl<Unit, Value> Neg for ValueSum<Unit, Value>
where
    Unit: Hash + Ord + BorshSerialize + BorshDeserialize + Clone,
    Value:
        BorshSerialize + BorshDeserialize + PartialEq + Eq + Copy + Zero + PartialOrd + CheckedNeg,
    <Value as CheckedNeg>::Output: BorshSerialize + BorshDeserialize + Eq + Zero,
{
    type Output = ValueSum<Unit, <Value as CheckedNeg>::Output>;

    fn neg(self) -> Self::Output {
        self.checked_neg().expect("overflow detected")
    }
}

impl<Unit, Value> CheckedNeg for ValueSum<Unit, Value>
where
    Unit: Hash + Ord + BorshSerialize + BorshDeserialize + Clone,
    Value:
        BorshSerialize + BorshDeserialize + PartialEq + Eq + Copy + Zero + PartialOrd + CheckedNeg,
    <Value as CheckedNeg>::Output: BorshSerialize + BorshDeserialize + Eq + Zero,
{
    type Output = ValueSum<Unit, <Value as CheckedNeg>::Output>;

    fn checked_neg(mut self) -> Option<Self::Output> {
        let mut comps = BTreeMap::new();
        for (atype, amount) in self.0.iter_mut() {
            comps.insert(atype.clone(), amount.checked_neg()?);
        }
        comps.retain(|_, v| *v != <Value as CheckedNeg>::Output::zero());
        Some(ValueSum(comps))
    }
}

impl<Unit, Lhs, Rhs> Sub<&ValueSum<Unit, Rhs>> for ValueSum<Unit, Lhs>
where
    Unit: Hash + Ord + BorshSerialize + BorshDeserialize + Clone,
    Lhs: BorshSerialize + BorshDeserialize + PartialEq + Eq + Copy + Zero + CheckedSub<Rhs>,
    Rhs: BorshSerialize + BorshDeserialize + PartialEq + Eq + Copy + Zero,
    <Lhs as CheckedSub<Rhs>>::Output: BorshSerialize + BorshDeserialize + Eq + Zero,
{
    type Output = ValueSum<Unit, <Lhs as CheckedSub<Rhs>>::Output>;

    fn sub(self, rhs: &ValueSum<Unit, Rhs>) -> Self::Output {
        self.checked_sub(rhs).expect("underflow detected")
    }
}

impl<Unit, Lhs, Rhs> Sub<ValueSum<Unit, Rhs>> for ValueSum<Unit, Lhs>
where
    Unit: Hash + Ord + BorshSerialize + BorshDeserialize + Clone,
    Lhs: BorshSerialize + BorshDeserialize + PartialEq + Eq + Copy + Zero + CheckedSub<Rhs>,
    Rhs: BorshSerialize + BorshDeserialize + PartialEq + Eq + Copy + Zero,
    <Lhs as CheckedSub<Rhs>>::Output: BorshSerialize + BorshDeserialize + Eq + Zero,
{
    type Output = ValueSum<Unit, <Lhs as CheckedSub<Rhs>>::Output>;

    fn sub(self, rhs: ValueSum<Unit, Rhs>) -> Self::Output {
        self - &rhs
    }
}

impl<Unit, Lhs, Rhs> CheckedSub<&ValueSum<Unit, Rhs>> for &ValueSum<Unit, Lhs>
where
    Unit: Hash + Ord + BorshSerialize + BorshDeserialize + Clone,
    Lhs: BorshSerialize + BorshDeserialize + PartialEq + Eq + Copy + Zero + CheckedSub<Rhs>,
    Rhs: BorshSerialize + BorshDeserialize + PartialEq + Eq + Copy + Zero,
    <Lhs as CheckedSub<Rhs>>::Output: BorshSerialize + BorshDeserialize + Eq + Zero,
{
    type Output = ValueSum<Unit, <Lhs as CheckedSub<Rhs>>::Output>;

    fn checked_sub(self, v: &ValueSum<Unit, Rhs>) -> Option<Self::Output> {
        let mut comps = BTreeMap::new();
        for (atype, amount) in self.components() {
            comps.insert(atype.clone(), amount.checked_sub(Rhs::zero())?);
        }
        for (atype, amount) in v.components() {
            comps.insert(atype.clone(), self.get(atype).checked_sub(*amount)?);
        }
        comps.retain(|_, v| *v != <Lhs as CheckedSub<Rhs>>::Output::zero());
        Some(ValueSum(comps))
    }
}

impl<Unit, Value> Sum for ValueSum<Unit, Value>
where
    Unit: Hash + Ord + BorshSerialize + BorshDeserialize + Clone,
    Value: BorshSerialize + BorshDeserialize + PartialEq + Eq + Copy + Zero + PartialOrd,
    Self: Add<Output = Self>,
{
    fn sum<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.fold(Self::zero(), Add::add)
    }
}

impl<Unit, Output> ValueSum<Unit, Output>
where
    Unit: Hash + Ord + BorshSerialize + BorshDeserialize + Clone,
    Output: BorshSerialize + BorshDeserialize + PartialEq + Eq + Copy + Zero,
{
    pub fn try_from_sum<Value>(
        x: ValueSum<Unit, Value>,
    ) -> Result<Self, <Output as TryFrom<Value>>::Error>
    where
        Value: BorshSerialize + BorshDeserialize + PartialEq + Eq + Copy,
        Output: TryFrom<Value>,
    {
        let mut comps = BTreeMap::new();
        for (atype, amount) in x.0 {
            comps.insert(atype, amount.try_into()?);
        }
        comps.retain(|_, v| *v != Output::zero());
        Ok(Self(comps))
    }

    pub fn from_sum<Value>(x: ValueSum<Unit, Value>) -> Self
    where
        Value: BorshSerialize + BorshDeserialize + PartialEq + Eq + Copy,
        Output: From<Value>,
    {
        let mut comps = BTreeMap::new();
        for (atype, amount) in x.0 {
            comps.insert(atype, amount.into());
        }
        comps.retain(|_, v| *v != Output::zero());
        Self(comps)
    }
}

impl<Unit, Lhs, Rhs> CheckedMul<&ValueSum<Unit, Rhs>> for ValueSum<Unit, Lhs>
where
    Unit: Hash + Ord + BorshSerialize + BorshDeserialize + Clone,
    Lhs: BorshSerialize + BorshDeserialize + PartialEq + Eq + Copy + Zero + CheckedMul<Rhs>,
    Rhs: BorshSerialize + BorshDeserialize + PartialEq + Eq + Copy + Zero,
    <Lhs as CheckedMul<Rhs>>::Output: Zero
        + BorshSerialize
        + BorshDeserialize
        + Eq
        + CheckedAdd<Output = <Lhs as CheckedMul<Rhs>>::Output>,
{
    type Output = <Lhs as CheckedMul<Rhs>>::Output;

    fn checked_mul(self, rhs: &ValueSum<Unit, Rhs>) -> Option<Self::Output> {
        let mut product = Self::Output::zero();
        for (atype, amount) in rhs.components() {
            product = product.checked_add(self.get(atype).checked_mul(*amount)?)?;
        }
        Some(product)
    }
}

impl<Unit, Lhs, Rhs> Mul<&ValueSum<Unit, Rhs>> for ValueSum<Unit, Lhs>
where
    Unit: Hash + Ord + BorshSerialize + BorshDeserialize + Clone,
    Lhs: BorshSerialize + BorshDeserialize + PartialEq + Eq + Copy + Zero + CheckedMul<Rhs>,
    Rhs: BorshSerialize + BorshDeserialize + PartialEq + Eq + Copy + Zero,
    <Lhs as CheckedMul<Rhs>>::Output: Zero
        + BorshSerialize
        + BorshDeserialize
        + Eq
        + CheckedAdd<Output = <Lhs as CheckedMul<Rhs>>::Output>,
{
    type Output = <Lhs as CheckedMul<Rhs>>::Output;

    fn mul(self, rhs: &ValueSum<Unit, Rhs>) -> Self::Output {
        self.checked_mul(rhs).expect("overflow detected")
    }
}

impl<Unit, Lhs, Rhs> Mul<ValueSum<Unit, Rhs>> for ValueSum<Unit, Lhs>
where
    Unit: Hash + Ord + BorshSerialize + BorshDeserialize + Clone,
    Lhs: BorshSerialize + BorshDeserialize + PartialEq + Eq + Copy + Zero + CheckedMul<Rhs>,
    Rhs: BorshSerialize + BorshDeserialize + PartialEq + Eq + Copy + Zero,
    <Lhs as CheckedMul<Rhs>>::Output: Zero
        + BorshSerialize
        + BorshDeserialize
        + Eq
        + CheckedAdd<Output = <Lhs as CheckedMul<Rhs>>::Output>,
{
    type Output = <Lhs as CheckedMul<Rhs>>::Output;

    fn mul(self, rhs: ValueSum<Unit, Rhs>) -> Self::Output {
        self * &rhs
    }
}

/// A type for balance violations in amount addition and subtraction
/// (overflow and underflow of allowed ranges)
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum BalanceError {
    Overflow,
    Underflow,
}

impl std::fmt::Display for BalanceError {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match &self {
            BalanceError::Overflow => {
                write!(
                    f,
                    "ValueSum addition resulted in a value outside the valid range."
                )
            }
            BalanceError::Underflow => write!(
                f,
                "ValueSum subtraction resulted in a value outside the valid range."
            ),
        }
    }
}

pub fn zec() -> AssetType {
    AssetType::new(b"ZEC").unwrap()
}

pub fn default_fee() -> ValueSum<AssetType, i64> {
    ValueSum::from_pair(zec(), 10000)
}

#[cfg(any(test, feature = "test-dependencies"))]
pub mod testing {
    use proptest::prelude::prop_compose;

    use super::{I64Sum, I128Sum, MAX_MONEY, U64Sum, ValueSum};
    use crate::asset_type::testing::arb_asset_type;

    prop_compose! {
        pub fn arb_i64_sum()(asset_type in arb_asset_type(), amt in i64::MIN..i64::MAX) -> I64Sum {
            ValueSum::from_pair(asset_type, amt)
        }
    }

    prop_compose! {
        pub fn arb_i128_sum()(asset_type in arb_asset_type(), amt in i128::MIN..i128::MAX) -> I128Sum {
            ValueSum::from_pair(asset_type, amt)
        }
    }

    prop_compose! {
        pub fn arb_nonnegative_amount()(asset_type in arb_asset_type(), amt in 0u64..MAX_MONEY) -> U64Sum {
            ValueSum::from_pair(asset_type, amt)
        }
    }

    prop_compose! {
        pub fn arb_positive_amount()(asset_type in arb_asset_type(), amt in 1u64..MAX_MONEY) -> U64Sum {
            ValueSum::from_pair(asset_type, amt)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{I32Sum, I64Sum, I128Sum, MAX_MONEY, ValueSum, zec};

    #[test]
    fn amount_in_range() {
        let mut bytes = Vec::with_capacity(100);

        macro_rules! test_vector {
            ($amount:ident) => {{
                bytes.clear();
                $amount.write(&mut bytes).unwrap();
                format!(
                    "b\"{}\",\n",
                    std::str::from_utf8(
                        &bytes
                            .iter()
                            .flat_map(|b| std::ascii::escape_default(*b))
                            .collect::<Vec<_>>(),
                    )
                    .unwrap()
                )
            }};
        }
        macro_rules! value_amount {
            ($t:ty, $val:expr) => {{
                let mut amount = <$t>::from_pair(zec(), 1);
                *amount.0.get_mut(&zec()).unwrap() = $val;
                amount
            }};
        }

        let test_amounts_i32 = [
            value_amount!(I32Sum, 0), // zec() asset with value 0
            I32Sum::from_pair(zec(), -1),
            I32Sum::from_pair(zec(), i32::MAX),
            I32Sum::from_pair(zec(), -i32::MAX),
        ];

        let test_amounts_i64 = [
            value_amount!(I64Sum, 0), // zec() asset with value 0
            I64Sum::from_pair(zec(), -1),
            I64Sum::from_pair(zec(), i64::MAX),
            I64Sum::from_pair(zec(), -i64::MAX),
        ];

        let test_amounts_i128 = [
            value_amount!(I128Sum, 0), // zec() asset with value 0
            I128Sum::from_pair(zec(), MAX_MONEY as i128),
            value_amount!(I128Sum, MAX_MONEY as i128 + 1),
            I128Sum::from_pair(zec(), -(MAX_MONEY as i128)),
            value_amount!(I128Sum, -(MAX_MONEY as i128 - 1)),
        ];

        println!(
            "let test_vectors_i32 = [{}];",
            test_amounts_i32
                .iter()
                .map(|a| test_vector!(a))
                .collect::<String>()
        );
        println!(
            "let test_vectors_i64 = [{}];",
            test_amounts_i64
                .iter()
                .map(|a| test_vector!(a))
                .collect::<String>()
        );

        println!(
            "let test_vectors_i128 = [{}];",
            test_amounts_i128
                .iter()
                .map(|a| test_vector!(a))
                .collect::<String>()
        );

        let zero = b"\x00";
        let test_vectors_i32 = [b"\x01\x94\xf3O\xfdd\xef\n\xc3i\x08\xfd\xdf\xec\x05hX\x06)\xc4Vq\x0f\xa1\x86\x83\x12\xa8\x7f\xbf\n\xa5\t\x00\x00\x00\x00",
        b"\x01\x94\xf3O\xfdd\xef\n\xc3i\x08\xfd\xdf\xec\x05hX\x06)\xc4Vq\x0f\xa1\x86\x83\x12\xa8\x7f\xbf\n\xa5\t\xff\xff\xff\xff",
        b"\x01\x94\xf3O\xfdd\xef\n\xc3i\x08\xfd\xdf\xec\x05hX\x06)\xc4Vq\x0f\xa1\x86\x83\x12\xa8\x7f\xbf\n\xa5\t\xff\xff\xff\x7f",
        b"\x01\x94\xf3O\xfdd\xef\n\xc3i\x08\xfd\xdf\xec\x05hX\x06)\xc4Vq\x0f\xa1\x86\x83\x12\xa8\x7f\xbf\n\xa5\t\x01\x00\x00\x80",
        ];
        let test_vectors_i64 = [b"\x01\x94\xf3O\xfdd\xef\n\xc3i\x08\xfd\xdf\xec\x05hX\x06)\xc4Vq\x0f\xa1\x86\x83\x12\xa8\x7f\xbf\n\xa5\t\x00\x00\x00\x00\x00\x00\x00\x00",
        b"\x01\x94\xf3O\xfdd\xef\n\xc3i\x08\xfd\xdf\xec\x05hX\x06)\xc4Vq\x0f\xa1\x86\x83\x12\xa8\x7f\xbf\n\xa5\t\xff\xff\xff\xff\xff\xff\xff\xff",
        b"\x01\x94\xf3O\xfdd\xef\n\xc3i\x08\xfd\xdf\xec\x05hX\x06)\xc4Vq\x0f\xa1\x86\x83\x12\xa8\x7f\xbf\n\xa5\t\xff\xff\xff\xff\xff\xff\xff\x7f",
        b"\x01\x94\xf3O\xfdd\xef\n\xc3i\x08\xfd\xdf\xec\x05hX\x06)\xc4Vq\x0f\xa1\x86\x83\x12\xa8\x7f\xbf\n\xa5\t\x01\x00\x00\x00\x00\x00\x00\x80",
        ];
        let test_vectors_i128 = [b"\x01\x94\xf3O\xfdd\xef\n\xc3i\x08\xfd\xdf\xec\x05hX\x06)\xc4Vq\x0f\xa1\x86\x83\x12\xa8\x7f\xbf\n\xa5\t\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00",
        b"\x01\x94\xf3O\xfdd\xef\n\xc3i\x08\xfd\xdf\xec\x05hX\x06)\xc4Vq\x0f\xa1\x86\x83\x12\xa8\x7f\xbf\n\xa5\t\xff\xff\xff\xff\xff\xff\xff\xff\x00\x00\x00\x00\x00\x00\x00\x00",
        b"\x01\x94\xf3O\xfdd\xef\n\xc3i\x08\xfd\xdf\xec\x05hX\x06)\xc4Vq\x0f\xa1\x86\x83\x12\xa8\x7f\xbf\n\xa5\t\x00\x00\x00\x00\x00\x00\x00\x00\x01\x00\x00\x00\x00\x00\x00\x00",
        b"\x01\x94\xf3O\xfdd\xef\n\xc3i\x08\xfd\xdf\xec\x05hX\x06)\xc4Vq\x0f\xa1\x86\x83\x12\xa8\x7f\xbf\n\xa5\t\x01\x00\x00\x00\x00\x00\x00\x00\xff\xff\xff\xff\xff\xff\xff\xff",
        b"\x01\x94\xf3O\xfdd\xef\n\xc3i\x08\xfd\xdf\xec\x05hX\x06)\xc4Vq\x0f\xa1\x86\x83\x12\xa8\x7f\xbf\n\xa5\t\x02\x00\x00\x00\x00\x00\x00\x00\xff\xff\xff\xff\xff\xff\xff\xff",
        ];

        assert_eq!(
            I32Sum::read(&mut test_vectors_i32[0].as_ref()).unwrap(),
            ValueSum::zero()
        );
        assert_eq!(
            I64Sum::read(&mut test_vectors_i64[0].as_ref()).unwrap(),
            ValueSum::zero()
        );
        assert_eq!(
            I128Sum::read(&mut test_vectors_i128[0].as_ref()).unwrap(),
            ValueSum::zero()
        );

        assert_eq!(I32Sum::read(&mut zero.as_ref()).unwrap(), ValueSum::zero());
        assert_eq!(I64Sum::read(&mut zero.as_ref()).unwrap(), ValueSum::zero());
        assert_eq!(I128Sum::read(&mut zero.as_ref()).unwrap(), ValueSum::zero());

        test_vectors_i32
            .iter()
            .skip(1)
            .zip(test_amounts_i32.iter().skip(1))
            .for_each(|(tv, ta)| assert_eq!(I32Sum::read(&mut tv.as_ref()).unwrap(), *ta));
        test_vectors_i64
            .iter()
            .skip(1)
            .zip(test_amounts_i64.iter().skip(1))
            .for_each(|(tv, ta)| assert_eq!(I64Sum::read(&mut tv.as_ref()).unwrap(), *ta));
        test_vectors_i128
            .iter()
            .skip(1)
            .zip(test_amounts_i128.iter().skip(1))
            .for_each(|(tv, ta)| assert_eq!(I128Sum::read(&mut tv.as_ref()).unwrap(), *ta));
    }

    #[test]
    #[should_panic]
    fn add_panics_on_overflow() {
        let v = ValueSum::from_pair(zec(), MAX_MONEY);
        let _sum = v + ValueSum::from_pair(zec(), 1);
    }

    #[test]
    #[should_panic]
    fn add_assign_panics_on_overflow() {
        let mut a = ValueSum::from_pair(zec(), MAX_MONEY);
        a += ValueSum::from_pair(zec(), 1);
    }

    #[test]
    #[should_panic]
    fn sub_panics_on_underflow() {
        let v = ValueSum::from_pair(zec(), 0u64);
        let _diff = v - ValueSum::from_pair(zec(), 1);
    }

    #[test]
    #[should_panic]
    fn sub_assign_panics_on_underflow() {
        let mut a = ValueSum::from_pair(zec(), 0u64);
        a -= ValueSum::from_pair(zec(), 1);
    }
}
