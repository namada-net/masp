//! Structs for handling encrypted memos.

use borsh::{BorshDeserialize, BorshSchema, BorshSerialize};
use std::cmp::Ordering;
use std::convert::{TryFrom, TryInto};
use std::error;
use std::fmt;
use std::ops::Deref;
use std::str;

/// Format a byte array as a colon-delimited hex string.
///
/// - Source: <https://github.com/tendermint/signatory>
/// - License: MIT / Apache 2.0
fn fmt_colon_delimited_hex<B>(f: &mut fmt::Formatter<'_>, bytes: B) -> fmt::Result
where
    B: AsRef<[u8]>,
{
    let len = bytes.as_ref().len();

    for (i, byte) in bytes.as_ref().iter().enumerate() {
        write!(f, "{:02x}", byte)?;

        if i != len - 1 {
            write!(f, ":")?;
        }
    }

    Ok(())
}

/// Errors that may result from attempting to construct an invalid memo.
#[derive(Debug, PartialEq, Eq)]
pub enum Error {
    InvalidUtf8(std::str::Utf8Error),
    TooLong(usize),
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Error::InvalidUtf8(e) => write!(f, "Invalid UTF-8: {}", e),
            Error::TooLong(n) => write!(f, "Memo length {} is larger than maximum of 512", n),
        }
    }
}

impl error::Error for Error {}

/// The unencrypted memo bytes received alongside a shielded note in a Zcash transaction.
#[derive(Clone, BorshSerialize, BorshDeserialize, BorshSchema)]
pub struct MemoBytes(pub(crate) Box<[u8; 512]>);

impl fmt::Debug for MemoBytes {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "MemoBytes(")?;
        fmt_colon_delimited_hex(f, &self.0[..])?;
        write!(f, ")")
    }
}

impl PartialEq for MemoBytes {
    fn eq(&self, rhs: &MemoBytes) -> bool {
        self.0[..] == rhs.0[..]
    }
}

impl Eq for MemoBytes {}

impl PartialOrd for MemoBytes {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for MemoBytes {
    fn cmp(&self, rhs: &Self) -> Ordering {
        self.0[..].cmp(&rhs.0[..])
    }
}

impl MemoBytes {
    /// Creates a `MemoBytes` indicating that no memo is present.
    pub fn empty() -> Self {
        let mut bytes = [0u8; 512];
        bytes[0] = 0xF6;
        MemoBytes(Box::new(bytes))
    }

    /// Creates a `MemoBytes` from a slice, exactly as provided.
    ///
    /// Returns an error if the provided slice is longer than 512 bytes. Slices shorter
    /// than 512 bytes are padded with null bytes.
    ///
    /// Note that passing an empty slice to this API (or an all-zeroes slice) will result
    /// in a memo representing an empty string. What you almost certainly want in this
    /// case is [`MemoBytes::empty`], which uses a specific encoding to indicate that no
    /// memo is present.
    pub fn from_bytes(bytes: &[u8]) -> Result<Self, Error> {
        if bytes.len() > 512 {
            return Err(Error::TooLong(bytes.len()));
        }

        let mut memo = [0u8; 512];
        memo[..bytes.len()].copy_from_slice(bytes);
        Ok(MemoBytes(Box::new(memo)))
    }

    /// Returns the raw byte array containing the memo bytes, including null padding.
    pub fn as_array(&self) -> &[u8; 512] {
        &self.0
    }

    /// Returns a slice of the raw bytes, excluding null padding.
    pub fn as_slice(&self) -> &[u8] {
        let first_null = self
            .0
            .iter()
            .enumerate()
            .rev()
            .find(|(_, b)| **b != 0)
            .map(|(i, _)| i + 1)
            .unwrap_or_default();

        &self.0[..first_null]
    }
}

/// Type-safe wrapper around String to enforce memo length requirements.
#[derive(Clone, PartialEq, Eq)]
pub struct TextMemo(String);

impl From<TextMemo> for String {
    fn from(memo: TextMemo) -> String {
        memo.0
    }
}

impl Deref for TextMemo {
    type Target = str;

    #[inline]
    fn deref(&self) -> &str {
        self.0.deref()
    }
}

/// An unencrypted memo received alongside a shielded note in a Zcash transaction.
#[derive(Clone, Default)]
pub enum Memo {
    /// An empty memo field.
    #[default]
    Empty,
    /// A memo field containing a UTF-8 string.
    Text(TextMemo),
    /// Some unknown memo format from ✨*the future*✨ that we can't parse.
    Future(MemoBytes),
    /// A memo field containing arbitrary bytes.
    Arbitrary(Box<[u8; 511]>),
}

impl fmt::Debug for Memo {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Memo::Empty => write!(f, "Memo::Empty"),
            Memo::Text(memo) => write!(f, "Memo::Text(\"{}\")", memo.0),
            Memo::Future(bytes) => write!(f, "Memo::Future({:0x})", bytes.0[0]),
            Memo::Arbitrary(bytes) => {
                write!(f, "Memo::Arbitrary(")?;
                fmt_colon_delimited_hex(f, &bytes[..])?;
                write!(f, ")")
            }
        }
    }
}

impl PartialEq for Memo {
    fn eq(&self, rhs: &Memo) -> bool {
        match (self, rhs) {
            (Memo::Empty, Memo::Empty) => true,
            (Memo::Text(a), Memo::Text(b)) => a == b,
            (Memo::Future(a), Memo::Future(b)) => a.0[..] == b.0[..],
            (Memo::Arbitrary(a), Memo::Arbitrary(b)) => a[..] == b[..],
            _ => false,
        }
    }
}

impl TryFrom<MemoBytes> for Memo {
    type Error = Error;

    /// Parses a `Memo` from its ZIP 302 serialization.
    ///
    /// Returns an error if the provided slice does not represent a valid `Memo` (for
    /// example, if the slice is not 512 bytes, or the encoded `Memo` is non-canonical).
    fn try_from(bytes: MemoBytes) -> Result<Self, Self::Error> {
        match bytes.0[0] {
            0xF6 if bytes.0.iter().skip(1).all(|&b| b == 0) => Ok(Memo::Empty),
            0xFF => Ok(Memo::Arbitrary(Box::new(bytes.0[1..].try_into().unwrap()))),
            b if b <= 0xF4 => str::from_utf8(bytes.as_slice())
                .map(|r| Memo::Text(TextMemo(r.to_owned())))
                .map_err(Error::InvalidUtf8),
            _ => Ok(Memo::Future(bytes)),
        }
    }
}

impl From<Memo> for MemoBytes {
    /// Serializes the `Memo` per ZIP 302.
    fn from(memo: Memo) -> Self {
        match memo {
            // Small optimisation to avoid a clone
            Memo::Future(memo) => memo,
            memo => (&memo).into(),
        }
    }
}

impl From<&Memo> for MemoBytes {
    /// Serializes the `Memo` per ZIP 302.
    fn from(memo: &Memo) -> Self {
        match memo {
            Memo::Empty => MemoBytes::empty(),
            Memo::Text(s) => {
                let mut bytes = [0u8; 512];
                let s_bytes = s.0.as_bytes();
                // s_bytes.len() is guaranteed to be <= 512
                bytes[..s_bytes.len()].copy_from_slice(s_bytes);
                MemoBytes(Box::new(bytes))
            }
            Memo::Future(memo) => memo.clone(),
            Memo::Arbitrary(arb) => {
                let mut bytes = [0u8; 512];
                bytes[0] = 0xFF;
                bytes[1..].copy_from_slice(arb.as_ref());
                MemoBytes(Box::new(bytes))
            }
        }
    }
}

impl Memo {
    /// Parses a `Memo` from its ZIP 302 serialization.
    ///
    /// Returns an error if the provided slice does not represent a valid `Memo` (for
    /// example, if the slice is not 512 bytes, or the encoded `Memo` is non-canonical).
    pub fn from_bytes(bytes: &[u8]) -> Result<Self, Error> {
        MemoBytes::from_bytes(bytes).and_then(TryFrom::try_from)
    }

    /// Serializes the `Memo` per ZIP 302.
    pub fn encode(&self) -> MemoBytes {
        self.into()
    }
}

impl str::FromStr for Memo {
    type Err = Error;

    /// Returns a `Memo` containing the given string, or an error if the string is too long.
    fn from_str(memo: &str) -> Result<Self, Self::Err> {
        if memo.is_empty() {
            Ok(Memo::Empty)
        } else if memo.len() <= 512 {
            Ok(Memo::Text(TextMemo(memo.to_owned())))
        } else {
            Err(Error::TooLong(memo.len()))
        }
    }
}

#[cfg(test)]
mod tests {
    use std::convert::TryInto;
    use std::str::FromStr;

    use super::{Error, Memo, MemoBytes};

    #[test]
    fn memo_from_str() {
        assert_eq!(
            Memo::from_str("").unwrap().encode(),
            MemoBytes(Box::new([
                0xf6, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00
            ]))
        );
        assert_eq!(
            Memo::from_str(
                "thiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiis \
                 iiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiis \
                 aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa \
                 veeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeryyyyyyyyyyyyyyyyyyyyyyyyyy \
                 looooooooooooooooooooooooooooooooooooooooooooooooooooooooooooooooooooooooooooong \
                 meeeeeeeeeeeeeeeeeeemooooooooooooooooooooooooooooooooooooooooooooooooooooooooooo \
                 but it's just short enough"
            )
            .unwrap()
            .encode(),
            MemoBytes(Box::new([
                0x74, 0x68, 0x69, 0x69, 0x69, 0x69, 0x69, 0x69, 0x69, 0x69, 0x69, 0x69, 0x69, 0x69,
                0x69, 0x69, 0x69, 0x69, 0x69, 0x69, 0x69, 0x69, 0x69, 0x69, 0x69, 0x69, 0x69, 0x69,
                0x69, 0x69, 0x69, 0x69, 0x69, 0x69, 0x69, 0x69, 0x69, 0x69, 0x69, 0x69, 0x69, 0x69,
                0x69, 0x69, 0x69, 0x69, 0x69, 0x69, 0x69, 0x69, 0x69, 0x69, 0x69, 0x69, 0x69, 0x69,
                0x69, 0x69, 0x69, 0x69, 0x69, 0x69, 0x69, 0x69, 0x69, 0x69, 0x69, 0x69, 0x69, 0x69,
                0x69, 0x69, 0x69, 0x69, 0x69, 0x69, 0x69, 0x69, 0x69, 0x73, 0x20, 0x69, 0x69, 0x69,
                0x69, 0x69, 0x69, 0x69, 0x69, 0x69, 0x69, 0x69, 0x69, 0x69, 0x69, 0x69, 0x69, 0x69,
                0x69, 0x69, 0x69, 0x69, 0x69, 0x69, 0x69, 0x69, 0x69, 0x69, 0x69, 0x69, 0x69, 0x69,
                0x69, 0x69, 0x69, 0x69, 0x69, 0x69, 0x69, 0x69, 0x69, 0x69, 0x69, 0x69, 0x69, 0x69,
                0x69, 0x69, 0x69, 0x69, 0x69, 0x69, 0x69, 0x69, 0x69, 0x69, 0x69, 0x69, 0x69, 0x69,
                0x69, 0x69, 0x69, 0x69, 0x69, 0x69, 0x69, 0x69, 0x69, 0x69, 0x69, 0x69, 0x69, 0x69,
                0x69, 0x69, 0x69, 0x69, 0x69, 0x69, 0x73, 0x20, 0x61, 0x61, 0x61, 0x61, 0x61, 0x61,
                0x61, 0x61, 0x61, 0x61, 0x61, 0x61, 0x61, 0x61, 0x61, 0x61, 0x61, 0x61, 0x61, 0x61,
                0x61, 0x61, 0x61, 0x61, 0x61, 0x61, 0x61, 0x61, 0x61, 0x61, 0x61, 0x61, 0x61, 0x61,
                0x61, 0x61, 0x61, 0x61, 0x61, 0x61, 0x61, 0x61, 0x61, 0x61, 0x61, 0x61, 0x61, 0x61,
                0x61, 0x61, 0x61, 0x61, 0x61, 0x61, 0x61, 0x61, 0x61, 0x61, 0x61, 0x61, 0x61, 0x61,
                0x61, 0x61, 0x61, 0x61, 0x61, 0x61, 0x61, 0x61, 0x61, 0x61, 0x61, 0x61, 0x61, 0x61,
                0x61, 0x61, 0x61, 0x61, 0x20, 0x76, 0x65, 0x65, 0x65, 0x65, 0x65, 0x65, 0x65, 0x65,
                0x65, 0x65, 0x65, 0x65, 0x65, 0x65, 0x65, 0x65, 0x65, 0x65, 0x65, 0x65, 0x65, 0x65,
                0x65, 0x65, 0x65, 0x65, 0x65, 0x65, 0x65, 0x65, 0x65, 0x65, 0x65, 0x65, 0x65, 0x65,
                0x65, 0x65, 0x65, 0x65, 0x65, 0x65, 0x65, 0x65, 0x65, 0x65, 0x65, 0x65, 0x65, 0x65,
                0x65, 0x65, 0x72, 0x79, 0x79, 0x79, 0x79, 0x79, 0x79, 0x79, 0x79, 0x79, 0x79, 0x79,
                0x79, 0x79, 0x79, 0x79, 0x79, 0x79, 0x79, 0x79, 0x79, 0x79, 0x79, 0x79, 0x79, 0x79,
                0x79, 0x20, 0x6c, 0x6f, 0x6f, 0x6f, 0x6f, 0x6f, 0x6f, 0x6f, 0x6f, 0x6f, 0x6f, 0x6f,
                0x6f, 0x6f, 0x6f, 0x6f, 0x6f, 0x6f, 0x6f, 0x6f, 0x6f, 0x6f, 0x6f, 0x6f, 0x6f, 0x6f,
                0x6f, 0x6f, 0x6f, 0x6f, 0x6f, 0x6f, 0x6f, 0x6f, 0x6f, 0x6f, 0x6f, 0x6f, 0x6f, 0x6f,
                0x6f, 0x6f, 0x6f, 0x6f, 0x6f, 0x6f, 0x6f, 0x6f, 0x6f, 0x6f, 0x6f, 0x6f, 0x6f, 0x6f,
                0x6f, 0x6f, 0x6f, 0x6f, 0x6f, 0x6f, 0x6f, 0x6f, 0x6f, 0x6f, 0x6f, 0x6f, 0x6f, 0x6f,
                0x6f, 0x6f, 0x6f, 0x6f, 0x6f, 0x6f, 0x6f, 0x6f, 0x6f, 0x6f, 0x6e, 0x67, 0x20, 0x6d,
                0x65, 0x65, 0x65, 0x65, 0x65, 0x65, 0x65, 0x65, 0x65, 0x65, 0x65, 0x65, 0x65, 0x65,
                0x65, 0x65, 0x65, 0x65, 0x65, 0x6d, 0x6f, 0x6f, 0x6f, 0x6f, 0x6f, 0x6f, 0x6f, 0x6f,
                0x6f, 0x6f, 0x6f, 0x6f, 0x6f, 0x6f, 0x6f, 0x6f, 0x6f, 0x6f, 0x6f, 0x6f, 0x6f, 0x6f,
                0x6f, 0x6f, 0x6f, 0x6f, 0x6f, 0x6f, 0x6f, 0x6f, 0x6f, 0x6f, 0x6f, 0x6f, 0x6f, 0x6f,
                0x6f, 0x6f, 0x6f, 0x6f, 0x6f, 0x6f, 0x6f, 0x6f, 0x6f, 0x6f, 0x6f, 0x6f, 0x6f, 0x6f,
                0x6f, 0x6f, 0x6f, 0x6f, 0x6f, 0x6f, 0x6f, 0x6f, 0x6f, 0x20, 0x62, 0x75, 0x74, 0x20,
                0x69, 0x74, 0x27, 0x73, 0x20, 0x6a, 0x75, 0x73, 0x74, 0x20, 0x73, 0x68, 0x6f, 0x72,
                0x74, 0x20, 0x65, 0x6e, 0x6f, 0x75, 0x67, 0x68
            ]))
        );
        assert_eq!(
            Memo::from_str(
                "thiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiis \
                 iiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiiis \
                 aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa \
                 veeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeryyyyyyyyyyyyyyyyyyyyyyyyyy \
                 looooooooooooooooooooooooooooooooooooooooooooooooooooooooooooooooooooooooooooong \
                 meeeeeeeeeeeeeeeeeeemooooooooooooooooooooooooooooooooooooooooooooooooooooooooooo \
                 but it's now a bit too long"
            ),
            Err(Error::TooLong(513))
        );
    }

    #[test]
    fn future_memo() {
        let bytes = [0xFE; 512];
        assert_eq!(
            MemoBytes::from_bytes(&bytes).unwrap().try_into(),
            Ok(Memo::Future(MemoBytes(Box::new(bytes))))
        );
    }

    #[test]
    fn arbitrary_memo() {
        let bytes = [42; 511];
        let memo = Memo::Arbitrary(Box::new(bytes));
        let raw = memo.encode();
        let encoded = raw.as_array();
        assert_eq!(encoded[0], 0xFF);
        assert_eq!(encoded[1..], bytes[..]);
        assert_eq!(MemoBytes::from_bytes(encoded).unwrap().try_into(), Ok(memo));
    }
}
