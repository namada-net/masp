//! Consensus logic and parameters.

use borsh::schema::Definition;
use borsh::schema::add_definition;
use borsh::{BorshDeserialize, BorshSchema, BorshSerialize};
use memuse::DynamicUsage;
use std::cmp::{Ord, Ordering};
use std::collections::BTreeMap;
use std::convert::TryFrom;
use std::fmt;
use std::io::{Error, ErrorKind, Read, Write};
use std::ops::{Add, Bound, RangeBounds, Sub};

/// A wrapper type representing blockchain heights. Safe conversion from
/// various integer types, as well as addition and subtraction, are provided.
#[cfg_attr(feature = "arbitrary", derive(arbitrary::Arbitrary))]
#[repr(transparent)]
#[derive(
    Clone, Copy, Debug, PartialEq, Eq, Hash, BorshSerialize, BorshDeserialize, BorshSchema,
)]
pub struct BlockHeight(u32);

memuse::impl_no_dynamic_usage!(BlockHeight);

pub const H0: BlockHeight = BlockHeight(0);

impl BlockHeight {
    pub const fn from_u32(v: u32) -> BlockHeight {
        BlockHeight(v)
    }
}

impl fmt::Display for BlockHeight {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt(formatter)
    }
}

impl Ord for BlockHeight {
    fn cmp(&self, other: &Self) -> Ordering {
        self.0.cmp(&other.0)
    }
}

impl PartialOrd for BlockHeight {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl From<u32> for BlockHeight {
    fn from(value: u32) -> Self {
        BlockHeight(value)
    }
}

impl From<BlockHeight> for u32 {
    fn from(value: BlockHeight) -> u32 {
        value.0
    }
}

impl TryFrom<u64> for BlockHeight {
    type Error = std::num::TryFromIntError;

    fn try_from(value: u64) -> Result<Self, Self::Error> {
        u32::try_from(value).map(BlockHeight)
    }
}

impl From<BlockHeight> for u64 {
    fn from(value: BlockHeight) -> u64 {
        value.0 as u64
    }
}

impl TryFrom<i32> for BlockHeight {
    type Error = std::num::TryFromIntError;

    fn try_from(value: i32) -> Result<Self, Self::Error> {
        u32::try_from(value).map(BlockHeight)
    }
}

impl TryFrom<i64> for BlockHeight {
    type Error = std::num::TryFromIntError;

    fn try_from(value: i64) -> Result<Self, Self::Error> {
        u32::try_from(value).map(BlockHeight)
    }
}

impl From<BlockHeight> for i64 {
    fn from(value: BlockHeight) -> i64 {
        value.0 as i64
    }
}

impl Add<u32> for BlockHeight {
    type Output = Self;

    fn add(self, other: u32) -> Self {
        BlockHeight(self.0 + other)
    }
}

impl Add for BlockHeight {
    type Output = Self;

    fn add(self, other: Self) -> Self {
        self + other.0
    }
}

impl Sub<u32> for BlockHeight {
    type Output = Self;

    fn sub(self, other: u32) -> Self {
        if other > self.0 {
            panic!("Subtraction resulted in negative block height.");
        }

        BlockHeight(self.0 - other)
    }
}

impl Sub for BlockHeight {
    type Output = Self;

    fn sub(self, other: Self) -> Self {
        self - other.0
    }
}

/// MASP consensus parameters.
pub trait Parameters: Clone {
    /// Returns the activation height for a particular network upgrade,
    /// if an activation height has been set.
    fn activation_height(&self, nu: NetworkUpgrade) -> Option<BlockHeight>;

    /// Determines whether the specified network upgrade is active as of the
    /// provided block height on the network to which this Parameters value applies.
    fn is_nu_active(&self, nu: NetworkUpgrade, height: BlockHeight) -> bool {
        self.activation_height(nu).is_some_and(|h| h <= height)
    }
}

/// Marker struct for the production network.
#[derive(PartialEq, Eq, Copy, Clone, Debug)]
pub struct MainNetwork;

memuse::impl_no_dynamic_usage!(MainNetwork);

pub const MAIN_NETWORK: MainNetwork = MainNetwork;

impl Parameters for MainNetwork {
    fn activation_height(&self, nu: NetworkUpgrade) -> Option<BlockHeight> {
        match nu {
            NetworkUpgrade::MASP => Some(H0),
        }
    }
}

/// Marker struct for the test network.
#[derive(PartialEq, Eq, Copy, Clone, Debug)]
pub struct TestNetwork;

memuse::impl_no_dynamic_usage!(TestNetwork);

pub const TEST_NETWORK: TestNetwork = TestNetwork;

impl Parameters for TestNetwork {
    fn activation_height(&self, nu: NetworkUpgrade) -> Option<BlockHeight> {
        match nu {
            NetworkUpgrade::MASP => Some(BlockHeight(1)), // Activate MASP at height 1 so pre-ZIP 212 tests work at height 0
        }
    }
}

#[derive(PartialEq, Eq, Copy, Clone, Debug)]
pub enum Network {
    MainNetwork,
    TestNetwork,
}

memuse::impl_no_dynamic_usage!(Network);

impl Parameters for Network {
    fn activation_height(&self, nu: NetworkUpgrade) -> Option<BlockHeight> {
        match self {
            Network::MainNetwork => MAIN_NETWORK.activation_height(nu),
            Network::TestNetwork => TEST_NETWORK.activation_height(nu),
        }
    }
}

/// An event that occurs at a specified height on the Zcash chain, at which point the
/// consensus rules enforced by the network are altered.
///
/// See [ZIP 200](https://zips.z.cash/zip-0200) for more details.
#[derive(Clone, Copy, Debug)]
pub enum NetworkUpgrade {
    /// The [MASP] network upgrade.
    ///
    /// [MASP]: https://github.com/anoma/masp/
    MASP,
}

memuse::impl_no_dynamic_usage!(NetworkUpgrade);

impl fmt::Display for NetworkUpgrade {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            NetworkUpgrade::MASP => write!(f, "MASP"),
        }
    }
}

impl NetworkUpgrade {
    fn branch_id(self) -> BranchId {
        match self {
            NetworkUpgrade::MASP => BranchId::MASP,
        }
    }
}

/// The network upgrades on the Zcash chain in order of activation.
///
/// This order corresponds to the activation heights, but because Rust enums are
/// full-fledged algebraic data types, we need to define it manually.
const UPGRADES_IN_ORDER: &[NetworkUpgrade] = &[NetworkUpgrade::MASP];

pub const ZIP212_GRACE_PERIOD: u32 = 0;

/// A globally-unique identifier for a set of consensus rules within the Zcash chain.
///
/// Each branch ID in this enum corresponds to one of the epochs between a pair of Zcash
/// network upgrades. For example, `BranchId::Overwinter` corresponds to the blocks
/// starting at Overwinter activation, and ending the block before Sapling activation.
///
/// The main use of the branch ID is in signature generation: transactions commit to a
/// specific branch ID by including it as part of [`signature_hash`]. This ensures
/// two-way replay protection for transactions across network upgrades.
///
/// See [ZIP 200](https://zips.z.cash/zip-0200) for more details.
///
/// [`signature_hash`]: crate::transaction::sighash::signature_hash
#[cfg_attr(feature = "arbitrary", derive(arbitrary::Arbitrary))]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BranchId {
    /// The consensus rules deployed by [`NetworkUpgrade::MASP`].
    MASP,
}

memuse::impl_no_dynamic_usage!(BranchId);

impl TryFrom<u32> for BranchId {
    type Error = &'static str;

    fn try_from(value: u32) -> Result<Self, Self::Error> {
        match value {
            0xe9ff_75a6 => Ok(BranchId::MASP),
            _ => Err("Unknown consensus branch ID"),
        }
    }
}

impl From<BranchId> for u32 {
    fn from(consensus_branch_id: BranchId) -> u32 {
        match consensus_branch_id {
            BranchId::MASP => 0xe9ff_75a6,
        }
    }
}

impl BorshSerialize for BranchId {
    fn serialize<W: Write>(&self, writer: &mut W) -> std::io::Result<()> {
        u32::from(*self).serialize(writer)
    }
}

impl BorshDeserialize for BranchId {
    fn deserialize_reader<R: Read>(reader: &mut R) -> std::io::Result<Self> {
        u32::deserialize_reader(reader)?
            .try_into()
            .map_err(|x| Error::new(ErrorKind::InvalidInput, x))
    }
}

impl BorshSchema for BranchId {
    fn add_definitions_recursively(
        definitions: &mut BTreeMap<borsh::schema::Declaration, borsh::schema::Definition>,
    ) {
        let definition = Definition::Enum {
            tag_width: 4,
            variants: vec![(0xe9ff_75a6, "MASP".into(), <()>::declaration())],
        };
        add_definition(Self::declaration(), definition, definitions);
        <()>::add_definitions_recursively(definitions);
    }

    fn declaration() -> borsh::schema::Declaration {
        "BranchId".into()
    }
}

impl BranchId {
    /// Returns the branch ID corresponding to the consensus rule set that is active at
    /// the given height.
    ///
    /// This is the branch ID that should be used when creating transactions.
    pub fn for_height<P: Parameters>(parameters: &P, height: BlockHeight) -> Self {
        for nu in UPGRADES_IN_ORDER.iter().rev() {
            if parameters.is_nu_active(*nu, height) {
                return nu.branch_id();
            }
        }

        // Sapling rules apply before any network upgrade
        BranchId::MASP
    }

    /// Returns the range of heights for the consensus epoch associated with this branch id.
    ///
    /// The resulting tuple implements the [`RangeBounds<BlockHeight>`] trait.
    pub fn height_range<P: Parameters>(&self, params: &P) -> Option<impl RangeBounds<BlockHeight>> {
        self.height_bounds(params).map(|(lower, upper)| {
            (
                Bound::Included(lower),
                upper.map_or(Bound::Unbounded, Bound::Excluded),
            )
        })
    }

    /// Returns the range of heights for the consensus epoch associated with this branch id.
    ///
    /// The return type of this value is slightly more precise than [`Self::height_range`]:
    /// - `Some((x, Some(y)))` means that the consensus rules corresponding to this branch id
    ///   are in effect for the range `x..y`
    /// - `Some((x, None))` means that the consensus rules corresponding to this branch id are
    ///   in effect for the range `x..`
    /// - `None` means that the consensus rules corresponding to this branch id are never in effect.
    pub fn height_bounds<P: Parameters>(
        &self,
        params: &P,
    ) -> Option<(BlockHeight, Option<BlockHeight>)> {
        match self {
            BranchId::MASP => params.activation_height(NetworkUpgrade::MASP).map(|lower| {
                let upper = None;
                (lower, upper)
            }),
        }
    }
}

#[cfg(any(test, feature = "test-dependencies"))]
pub mod testing {
    use proptest::sample::select;
    use proptest::strategy::{Just, Strategy};

    use super::{BlockHeight, BranchId, Parameters};

    pub fn arb_branch_id() -> impl Strategy<Value = BranchId> {
        select(vec![BranchId::MASP])
    }

    pub fn arb_height<P: Parameters>(
        branch_id: BranchId,
        params: &P,
    ) -> impl Strategy<Value = Option<BlockHeight>> {
        branch_id
            .height_bounds(params)
            .map_or(Strategy::boxed(Just(None)), |(lower, upper)| {
                Strategy::boxed(
                    (lower.0..upper.map_or(u32::MAX, |u| u.0)).prop_map(|h| Some(BlockHeight(h))),
                )
            })
    }
}

#[cfg(test)]
mod tests {
    use std::convert::TryFrom;

    use super::{
        BlockHeight, BranchId, MAIN_NETWORK, NetworkUpgrade, Parameters, UPGRADES_IN_ORDER,
    };

    #[test]
    fn nu_ordering() {
        for i in 1..UPGRADES_IN_ORDER.len() {
            let nu_a = UPGRADES_IN_ORDER[i - 1];
            let nu_b = UPGRADES_IN_ORDER[i];
            match (
                MAIN_NETWORK.activation_height(nu_a),
                MAIN_NETWORK.activation_height(nu_b),
            ) {
                (Some(a), Some(b)) if a < b => (),
                (Some(_), None) => (),
                (None, None) => (),
                _ => panic!(
                    "{} should not be before {} in UPGRADES_IN_ORDER",
                    nu_a, nu_b
                ),
            }
        }
    }

    #[test]
    fn nu_is_active() {
        assert!(MAIN_NETWORK.is_nu_active(NetworkUpgrade::MASP, BlockHeight(0)));
    }

    #[test]
    fn branch_id_from_u32() {
        assert_eq!(BranchId::try_from(3925833126), Ok(BranchId::MASP));
        assert!(BranchId::try_from(1).is_err());
    }

    #[test]
    fn branch_id_for_height() {
        assert_eq!(
            BranchId::for_height(&MAIN_NETWORK, BlockHeight(0)),
            BranchId::MASP,
        );
    }
}
