//! *General MASP primitives.*
//!
//! `masp_primitives` is a library that provides the core structs and functions necessary
//! for working with MASP based on Zcash Sapling.

#![cfg_attr(docsrs, feature(doc_cfg))]
// Catch documentation errors caused by code changes.
#![deny(rustdoc::broken_intra_doc_links)]
// Temporary until we have addressed all Result<T, ()> cases.
#![allow(clippy::result_unit_err)]
// Allow absurd MAX_MONEY comparisons in case MAX_MONEY is ever changed
#![allow(clippy::absurd_extreme_comparisons)]
// Allow manual RangeIncludes for now
#![allow(clippy::manual_range_contains)]
// TODO
#![allow(clippy::derived_hash_with_manual_eq)]

pub mod asset_type;
pub mod consensus;
pub mod constants;
pub mod convert;
pub mod keys;
pub mod memo;
pub mod merkle_tree;
pub mod sapling;
pub mod transaction;
pub mod zip32;

pub use bls12_381;
pub use ff;
pub use group;
pub use jubjub;
pub use num_traits;

#[cfg(test)]
mod test_vectors;

#[cfg(not(feature = "arbitrary"))]
pub trait MaybeArbitrary<'a> {}

#[cfg(not(feature = "arbitrary"))]
impl<T> MaybeArbitrary<'_> for T {}

#[cfg(feature = "arbitrary")]
pub trait MaybeArbitrary<'a>: arbitrary::Arbitrary<'a> {}

#[cfg(feature = "arbitrary")]
impl<T: for<'b> arbitrary::Arbitrary<'b>> MaybeArbitrary<'_> for T {}
