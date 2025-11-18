// This file is part of copy-stack-vec.
// SPDX-License-Identifier: MIT OR Apache-2.0

//! Error types for `CopyStackVec`.
//!
//! These errors represent capacity and bounds conditions.
//! They are `Copy` and implement `core::error::Error` (on recent toolchains).

// Core imports
use core::{error::Error as CoreError, fmt};

/// Errors returned by operations on [`CopyStackVec`](crate::CopyStackVec).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum Error {
    /// The operation would exceed the fixed capacity (`N`).
    Full,
    /// An index or position was out of the current logical bounds.
    OutOfBounds,
    /// An operation required `len == N`, which was not met.
    ///
    /// Currently used by [`CopyStackVec::try_into_array`] when the vector is not full.
    InvalidLen,
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Full => f.write_str("capacity exceeded"),
            Self::OutOfBounds => f.write_str("index out of bounds"),
            Self::InvalidLen => f.write_str("invalid length"),
        }
    }
}

impl CoreError for Error {}

#[cfg(test)]
mod tests {
    // Imports
    use crate::Error;
    use alloc::string::{String, ToString};
    use core::error::Error as CoreError;

    fn takes_error(e: &dyn CoreError) -> String {
        e.to_string()
    }

    #[test]
    fn test_error_is_core_error() {
        let s = takes_error(&Error::OutOfBounds);
        assert!(s.contains("out of bounds"));
    }
}
