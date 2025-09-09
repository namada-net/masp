//! Various constants used for the MASP proofs.

use bls12_381::Scalar;
use group::{Curve, Group, ff::Field};
use jubjub::ExtendedPoint;
use lazy_static::lazy_static;
use masp_primitives::constants::{PEDERSEN_HASH_CHUNKS_PER_GENERATOR, pedersen_hash_generators};

/// The `d` constant of the twisted Edwards curve.
pub(crate) fn edward_d() -> Scalar {
    Scalar::from_u64s_le(&[
        0x0106_5fd6_d634_3eb1,
        0x292d_7f6d_3757_9d26,
        0xf5fd_9207_e6bd_7fd4,
        0x2a93_18e7_4bfa_2b48,
    ])
    .unwrap()
}

/// The `A` constant of the birationally equivalent Montgomery curve.
pub(crate) fn montgomery_a() -> Scalar {
    Scalar::from_u64s_le(&[
        0x0000_0000_0000_a002,
        0x0000_0000_0000_0000,
        0x0000_0000_0000_0000,
        0x0000_0000_0000_0000,
    ])
    .unwrap()
}

/// The scaling factor used for conversion to and from the Montgomery form.
pub(crate) fn montgomery_scale() -> Scalar {
    Scalar::from_u64s_le(&[
        0x8f45_35f7_cf82_b8d9,
        0xce40_6970_3da8_8abd,
        0x31de_341e_77d7_64e5,
        0x2762_de61_e862_645e,
    ])
    .unwrap()
}

/// The number of chunks needed to represent a full scalar during fixed-base
/// exponentiation.
const FIXED_BASE_CHUNKS_PER_GENERATOR: usize = 84;

/// Reference to a circuit version of a generator for fixed-base salar multiplication.
pub type FixedGenerator = &'static [Vec<(Scalar, Scalar)>];

/// Circuit version of a generator for fixed-base salar multiplication.
pub type FixedGeneratorOwned = Vec<Vec<(Scalar, Scalar)>>;

lazy_static! {
    pub static ref PROOF_GENERATION_KEY_GENERATOR: FixedGeneratorOwned =
        generate_circuit_generator(masp_primitives::constants::proof_generation_key_generator());

    pub static ref NOTE_COMMITMENT_RANDOMNESS_GENERATOR: FixedGeneratorOwned =
        generate_circuit_generator(masp_primitives::constants::note_commitment_randomness_generator());

    pub static ref NULLIFIER_POSITION_GENERATOR: FixedGeneratorOwned =
        generate_circuit_generator(masp_primitives::constants::nullifier_position_generator());

    pub static ref VALUE_COMMITMENT_RANDOMNESS_GENERATOR: FixedGeneratorOwned =
        generate_circuit_generator(masp_primitives::constants::value_commitment_randomness_generator());

    pub static ref SPENDING_KEY_GENERATOR: FixedGeneratorOwned =
        generate_circuit_generator(masp_primitives::constants::spending_key_generator());

    /// The pre-computed window tables `[-4, 3, 2, 1, 1, 2, 3, 4]` of different magnitudes
    /// of the Pedersen hash segment generators.
    pub static ref PEDERSEN_CIRCUIT_GENERATORS: Vec<Vec<Vec<(Scalar, Scalar)>>> =
        generate_pedersen_circuit_generators();
}

/// Creates the 3-bit window table `[0, 1, ..., 8]` for different magnitudes of a fixed
/// generator.
pub fn generate_circuit_generator(mut r#gen: jubjub::SubgroupPoint) -> FixedGeneratorOwned {
    let mut windows = vec![];

    for _ in 0..FIXED_BASE_CHUNKS_PER_GENERATOR {
        let mut coeffs = vec![(Scalar::ZERO, Scalar::ONE)];
        let mut g = r#gen;
        for _ in 0..7 {
            let g_affine = jubjub::ExtendedPoint::from(g).to_affine();
            coeffs.push((g_affine.get_u(), g_affine.get_v()));
            g += r#gen;
        }
        windows.push(coeffs);

        // r#gen = r#gen * 8
        r#gen = g;
    }

    windows
}

/// Returns the coordinates of this point's Montgomery curve representation, or `None` if
/// it is the point at infinity.
#[allow(clippy::many_single_char_names)]
pub(crate) fn to_montgomery_coords(g: ExtendedPoint) -> Option<(Scalar, Scalar)> {
    let g = g.to_affine();
    let (x, y) = (g.get_u(), g.get_v());

    if y == Scalar::ONE {
        // The only solution for y = 1 is x = 0. (0, 1) is the neutral element, so we map
        // this to the point at infinity.
        None
    } else {
        // The map from a twisted Edwards curve is defined as
        // (x, y) -> (u, v) where
        //      u = (1 + y) / (1 - y)
        //      v = u / x
        //
        // This mapping is not defined for y = 1 and for x = 0.
        //
        // We have that y != 1 above. If x = 0, the only
        // solutions for y are 1 (contradiction) or -1.
        if x.is_zero_vartime() {
            // (0, -1) is the point of order two which is not
            // the neutral element, so we map it to (0, 0) which is
            // the only affine point of order 2.
            Some((Scalar::ZERO, Scalar::ZERO))
        } else {
            // The mapping is defined as above.
            //
            // (x, y) -> (u, v) where
            //      u = (1 + y) / (1 - y)
            //      v = u / x

            let u = (Scalar::ONE + y) * (Scalar::ONE - y).invert().unwrap();
            let v = u * x.invert().unwrap();

            // Scale it into the correct curve constants
            // scaling factor = sqrt(4 / (a - d))
            Some((u, v * montgomery_scale()))
        }
    }
}

/// Creates the 2-bit window table lookups for each 4-bit "chunk" in each segment of the
/// Pedersen hash.
fn generate_pedersen_circuit_generators() -> Vec<Vec<Vec<(Scalar, Scalar)>>> {
    // Process each segment
    pedersen_hash_generators()
        .iter()
        .cloned()
        .map(|mut r#gen| {
            let mut windows = vec![];

            for _ in 0..PEDERSEN_HASH_CHUNKS_PER_GENERATOR {
                // Create (x, y) coeffs for this chunk
                let mut coeffs = vec![];
                let mut g = r#gen;

                // coeffs = g, g*2, g*3, g*4
                for _ in 0..4 {
                    coeffs.push(
                        to_montgomery_coords(g.into())
                            .expect("we never encounter the point at infinity"),
                    );
                    g += r#gen;
                }
                windows.push(coeffs);

                // Our chunks are separated by 2 bits to prevent overlap.
                for _ in 0..4 {
                    r#gen = r#gen.double();
                }
            }

            windows
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    /// The `d` constant of the twisted Edwards curve.
    pub(crate) fn edwards_d() -> Scalar {
        Scalar::from_u64s_le(&[
            0x0106_5fd6_d634_3eb1,
            0x292d_7f6d_3757_9d26,
            0xf5fd_9207_e6bd_7fd4,
            0x2a93_18e7_4bfa_2b48,
        ])
        .unwrap()
    }

    #[test]
    fn test_edwards_d() {
        // d = -(10240/10241)
        assert_eq!(
            -Scalar::from(10240) * Scalar::from(10241).invert().unwrap(),
            edwards_d()
        );
    }

    #[test]
    fn test_montgomery_scale() {
        // scaling factor = sqrt(4 / (a - d))
        assert_eq!(
            montgomery_scale().square() * (-Scalar::ONE - edwards_d()),
            Scalar::from(4),
        );
    }
}
