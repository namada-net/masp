//! Structs representing the components within Zcash transactions.

pub mod amount;
pub mod sapling;
pub mod transparent;
pub use self::{
    amount::{
        I8Sum, I16Sum, I32Sum, I64Sum, I128Sum, U8Sum, U16Sum, U32Sum, U64Sum, U128Sum, ValueSum,
    },
    sapling::{ConvertDescription, OutputDescription, SpendDescription},
    transparent::{TxIn, TxOut},
};

// π_A + π_B + π_C
pub const GROTH_PROOF_SIZE: usize = 48 + 96 + 48;
