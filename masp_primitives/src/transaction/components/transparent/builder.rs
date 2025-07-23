//! Types and functions for building transparent transaction components.

use std::fmt;

use crate::{
    asset_type::AssetType,
    transaction::{
        TransparentAddress,
        components::{
            amount::{I128Sum, MAX_MONEY, ValueSum},
            transparent::{self, Authorization, Authorized, Bundle, TxIn, TxOut, fees},
        },
        sighash::TransparentAuthorizingContext,
    },
};
use borsh::BorshSchema;
use borsh::{BorshDeserialize, BorshSerialize};

#[derive(Debug, PartialEq, Eq)]
pub enum Error {
    InvalidAddress,
    InvalidAmount,
    InvalidAsset,
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Error::InvalidAddress => write!(f, "Invalid address"),
            Error::InvalidAmount => write!(f, "Invalid amount"),
            Error::InvalidAsset => write!(f, "Invalid asset"),
        }
    }
}

/// An uninhabited type that allows the type of [`TransparentBuilder::inputs`]
/// to resolve when the transparent-inputs feature is not turned on.
#[cfg(not(feature = "transparent-inputs"))]
enum InvalidTransparentInput {}

#[cfg(not(feature = "transparent-inputs"))]
impl fees::InputView for InvalidTransparentInput {
    fn coin(&self) -> &TxOut {
        panic!("transparent-inputs feature flag is not enabled.");
    }
}

#[cfg_attr(feature = "arbitrary", derive(arbitrary::Arbitrary))]
#[cfg(feature = "transparent-inputs")]
#[derive(Debug, Clone, PartialEq, Eq, BorshSerialize, BorshDeserialize, BorshSchema)]
struct TransparentInputInfo {
    coin: TxOut,
}

#[cfg(feature = "transparent-inputs")]
impl fees::InputView for TransparentInputInfo {
    fn coin(&self) -> &TxOut {
        &self.coin
    }
}

#[derive(Clone, Debug, BorshSerialize, BorshDeserialize, BorshSchema)]
pub struct TransparentBuilder {
    #[cfg(feature = "transparent-inputs")]
    inputs: Vec<TransparentInputInfo>,
    vout: Vec<TxOut>,
}

#[cfg_attr(feature = "arbitrary", derive(arbitrary::Arbitrary))]
#[derive(Debug, Clone, PartialEq, Eq, BorshSerialize, BorshDeserialize)]
pub struct Unauthorized {
    #[cfg(feature = "transparent-inputs")]
    inputs: Vec<TransparentInputInfo>,
}

impl Authorization for Unauthorized {
    type TransparentSig = ();
}

impl TransparentBuilder {
    /// Constructs a new TransparentBuilder
    pub fn empty() -> Self {
        TransparentBuilder {
            #[cfg(feature = "transparent-inputs")]
            inputs: vec![],
            vout: vec![],
        }
    }

    /// Returns the list of transparent inputs that will be consumed by the transaction being
    /// constructed.
    pub fn inputs(&self) -> &[impl fees::InputView] {
        #[cfg(feature = "transparent-inputs")]
        return &self.inputs;

        #[cfg(not(feature = "transparent-inputs"))]
        {
            let invalid: &[InvalidTransparentInput] = &[];
            return invalid;
        }
    }

    /// Returns the transparent outputs that will be produced by the transaction being constructed.
    pub fn outputs(&self) -> &[impl fees::OutputView] {
        &self.vout
    }

    /// Adds a coin (the output of a previous transaction) to be spent to the transaction.
    #[cfg(feature = "transparent-inputs")]
    pub fn add_input(&mut self, coin: TxOut) -> Result<(), Error> {
        self.inputs.push(TransparentInputInfo { coin });

        Ok(())
    }

    pub fn add_output(
        &mut self,
        to: &TransparentAddress,
        asset_type: AssetType,
        value: u64,
    ) -> Result<(), Error> {
        if value > MAX_MONEY {
            return Err(Error::InvalidAmount);
        }

        self.vout.push(TxOut {
            asset_type,
            value,
            address: *to,
        });

        Ok(())
    }

    pub fn value_balance(&self) -> I128Sum {
        #[cfg(feature = "transparent-inputs")]
        let input_sum = self
            .inputs
            .iter()
            .map(|input| ValueSum::from_pair(input.coin.asset_type, input.coin.value as i128))
            .sum::<I128Sum>();

        #[cfg(not(feature = "transparent-inputs"))]
        let input_sum = ValueSum::zero();

        let output_sum = self
            .vout
            .iter()
            .map(|vo| ValueSum::from_pair(vo.asset_type, vo.value as i128))
            .sum::<I128Sum>();

        // Cannot panic when subtracting two positive i64
        input_sum - output_sum
    }

    pub fn build(self) -> Option<transparent::Bundle<Unauthorized>> {
        #[cfg(feature = "transparent-inputs")]
        let vin: Vec<TxIn<Unauthorized>> = self
            .inputs
            .iter()
            .map(|i| TxIn::<Unauthorized> {
                asset_type: i.coin.asset_type,
                value: i.coin.value,
                address: i.coin.address,
                transparent_sig: (),
            })
            .collect();

        #[cfg(not(feature = "transparent-inputs"))]
        let vin: Vec<TxIn> = vec![];

        if vin.is_empty() && self.vout.is_empty() {
            None
        } else {
            Some(transparent::Bundle {
                vin,
                vout: self.vout,
                authorization: Unauthorized {
                    #[cfg(feature = "transparent-inputs")]
                    inputs: self.inputs,
                },
            })
        }
    }
}

#[cfg(not(feature = "transparent-inputs"))]
impl TransparentAuthorizingContext for Unauthorized {
    fn input_amounts(&self) -> Vec<(AssetType, i64)> {
        vec![]
    }
}

#[cfg(feature = "transparent-inputs")]
impl TransparentAuthorizingContext for Unauthorized {
    fn input_amounts(&self) -> Vec<(AssetType, u64)> {
        return self
            .inputs
            .iter()
            .map(|txin| (txin.coin.asset_type, txin.coin.value))
            .collect();
    }
}

impl Bundle<Unauthorized> {
    pub fn apply_signatures(self) -> Bundle<Authorized> {
        transparent::Bundle {
            vin: self
                .vin
                .iter()
                .map(|txin| TxIn {
                    asset_type: txin.asset_type,
                    address: txin.address,
                    value: txin.value,
                    transparent_sig: (),
                })
                .collect(),
            vout: self.vout,
            authorization: Authorized,
        }
    }
}
