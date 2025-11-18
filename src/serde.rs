// This file is part of copy-stack-vec.
// SPDX-License-Identifier: MIT OR Apache-2.0

//! `serde` support for [`CopyStackVec`](crate::CopyStackVec).
//!
//! - **Serialize**: as a sequence of elements (length `len`).
//! - **Deserialize**: from any sequence up to capacity `N`.
//!
//! ### Trait bounds
//!
//! `CopyStackVec<T, N>` is only defined for `T: Copy`. This module adds the
//! following *additional* requirements for `serde` integration:
//!
//! - In the default (safe) backend:
//!   - `CopyStackVec<T, N>: Deserialize` is implemented whenever
//!     `T: Deserialize<'de> + Default`.
//!   - `Default` is used to eagerly initialize the backing `[T; N]` buffer.
//!
//! - With the `unsafe-maybe-uninit` feature enabled:
//!   - `CopyStackVec<T, N>: Deserialize` is implemented whenever
//!     `T: Deserialize<'de>`.
//!   - The backing storage is `[MaybeUninit<T>; N]`; `Default`/`new` avoid
//!     constructing `N` copies of `T`, and elements are written into the
//!     uninitialized buffer as they are deserialized.
//!
//! # Remark
//! In both backends, `T: Copy` is always required because `CopyStackVec<T, N>` itself is
//! only defined for `T: Copy`.

// Crate imports
use crate::vec::CopyStackVec;

// Core imports
use core::fmt;

// External imports - serde
use serde::{Deserialize, Deserializer, Serialize, Serializer, de, ser};

impl<T: Copy + Serialize, const N: usize> Serialize for CopyStackVec<T, N> {
    fn serialize<S: Serializer>(&self, s: S) -> Result<S::Ok, S::Error> {
        use ser::SerializeSeq;
        let sl = self.as_slice();
        let mut seq = s.serialize_seq(Some(sl.len()))?;
        for item in sl {
            seq.serialize_element(item)?;
        }
        seq.end()
    }
}

struct VecVisitor<T, const N: usize>(core::marker::PhantomData<T>);

impl<'de, T, const N: usize> de::Visitor<'de> for VecVisitor<T, N>
where
    T: Deserialize<'de> + Copy,
    CopyStackVec<T, N>: Default,
{
    type Value = CopyStackVec<T, N>;

    fn expecting(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "array or sequence with at most {} elements", N)
    }

    fn visit_seq<A: de::SeqAccess<'de>>(self, mut a: A) -> Result<Self::Value, A::Error> {
        // Use Default, which is implemented differently in each backend.
        let mut out = CopyStackVec::<T, N>::default();
        while let Some(elem) = a.next_element::<T>()? {
            out.push(elem)
                .map_err(|_| de::Error::custom(format_args!("too many elements (capacity {N})")))?;
        }
        Ok(out)
    }
}

#[cfg(not(feature = "unsafe-maybe-uninit"))]
impl<'de, T, const N: usize> Deserialize<'de> for CopyStackVec<T, N>
where
    T: Deserialize<'de> + Copy + Default,
{
    fn deserialize<D: Deserializer<'de>>(d: D) -> Result<Self, D::Error> {
        d.deserialize_seq(VecVisitor::<T, N>(core::marker::PhantomData))
    }
}

#[cfg(feature = "unsafe-maybe-uninit")]
impl<'de, T, const N: usize> Deserialize<'de> for CopyStackVec<T, N>
where
    T: Deserialize<'de> + Copy,
{
    fn deserialize<D: Deserializer<'de>>(d: D) -> Result<Self, D::Error> {
        d.deserialize_seq(VecVisitor::<T, N>(core::marker::PhantomData))
    }
}

#[cfg(test)]
mod tests {
    // Imports
    use super::CopyStackVec;

    #[test]
    fn test_serde_roundtrip_json() {
        let v: CopyStackVec<i32, 5> = CopyStackVec::try_from(&[1, 2, 3][..]).unwrap();
        let s = serde_json::to_string(&v).unwrap();
        assert_eq!(s, "[1,2,3]");
        let back: CopyStackVec<i32, 5> = serde_json::from_str(&s).unwrap();
        assert_eq!(back.as_slice(), &[1, 2, 3]);
    }

    #[test]
    fn test_deserialize_over_capacity_errors() {
        let err = serde_json::from_str::<CopyStackVec<i32, 3>>("[1,2,3,4]").unwrap_err();
        let msg = err.to_string();
        assert!(
            msg.contains("too many elements") || msg.contains("capacity 3"),
            "msg: {msg}"
        );
    }

    #[test]
    fn test_serde_roundtrip_empty_json() {
        let v: CopyStackVec<i32, 4> = CopyStackVec::default();
        let s = serde_json::to_string(&v).unwrap();
        assert_eq!(s, "[]");
        let back: CopyStackVec<i32, 4> = serde_json::from_str(&s).unwrap();
        assert!(back.is_empty());
    }

    #[test]
    fn serde_zst_roundtrip() {
        // Build with length 2 but capacity 3
        let v: CopyStackVec<(), 3> = CopyStackVec::from_slice_truncated(&[(), ()]);
        let s = serde_json::to_string(&v).unwrap();
        assert_eq!(s, "[null,null]");
        let back: CopyStackVec<(), 3> = serde_json::from_str(&s).unwrap();
        assert_eq!(back.len(), 2);
    }

    #[test]
    fn test_vecvisitor_expecting_message() {
        // Try to deserialize from a JSON object instead of an array/sequence.
        let err =
            serde_json::from_str::<CopyStackVec<i32, 4>>(r#"{"not":"an array"}"#).unwrap_err();
        let msg = err.to_string();

        // This should include the string from VecVisitor::expecting.
        assert!(
            msg.contains("array or sequence with at most 4 elements"),
            "unexpected error message: {msg}"
        );
    }

    #[cfg(feature = "unsafe-maybe-uninit")]
    #[test]
    fn test_deserialize_non_default_type_in_maybe_uninit_backend() {
        use serde::{Deserialize, Serialize};

        #[derive(Copy, Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
        struct NoDefault(i32);

        // Intentionally do NOT implement Default for NoDefault.

        let json = "[1,2,3]";
        let v: CopyStackVec<NoDefault, 4> =
            serde_json::from_str(json).expect("should deserialize under maybe_uninit backend");
        assert_eq!(v.len(), 3);
        assert_eq!(v.as_slice(), &[NoDefault(1), NoDefault(2), NoDefault(3)]);
    }
}
