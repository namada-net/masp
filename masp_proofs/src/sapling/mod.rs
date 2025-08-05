//! Helpers for creating MASP Sapling proofs.

use masp_primitives::asset_type::AssetType;

mod prover;
mod verifier;
mod translation;

pub use self::prover::SaplingProvingContext;
pub use self::verifier::{
    BatchValidator, SaplingVerificationContext, SaplingVerificationContextInner,
};

// This function computes `value` in the exponent of the value commitment base
fn masp_compute_value_balance(asset_type: AssetType, value: i128) -> Option<jubjub::ExtendedPoint> {
    // Compute the absolute value (failing if -i128::MAX is
    // the value)
    let abs = match value.checked_abs() {
        Some(a) => a as u128,
        None => return None,
    };

    // Is it negative? We'll have to negate later if so.
    let is_negative = value.is_negative();

    // Compute it in the exponent
    let mut abs_bytes = [0u8; 32];
    abs_bytes[0..16].copy_from_slice(&abs.to_le_bytes());
    let mut value_balance =
        asset_type.value_commitment_generator() * jubjub::Fr::from_bytes(&abs_bytes).unwrap();

    // Negate if necessary
    if is_negative {
        value_balance = -value_balance;
    }

    // Convert to unknown order point
    Some(value_balance.into())
}
