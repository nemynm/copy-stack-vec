// This file is part of copy-stack-vec.
// SPDX-License-Identifier: MIT OR Apache-2.0

// Crate imports
use crate::vec::CopyStackVec;

impl<T: Copy, const N: usize> CopyStackVec<T, N> {
    /// Tries to construct from an iterator, erroring with [`Error::Full`] if it would overflow.
    ///
    /// Semantics:
    /// - Elements are pushed in iterator order.
    /// - On the first element that would exceed capacity `N`, this returns `Err(Error::Full)`.
    /// - Any elements pushed before the overflow are discarded; the returned `Err` does *not*
    ///   include the partially filled vector.
    /// - The source iterator may be left partially consumed (it stops at the first overflow).
    #[inline]
    pub fn try_from_iter<I: IntoIterator<Item = T>>(iter: I) -> Result<Self, crate::Error> {
        let mut v = Self::default();
        for item in iter {
            v.push(item)?; // returns Err(Full) on overflow → we bail out immediately
        }
        Ok(v)
    }
}

#[cfg(test)]
mod tests {
    use crate::vec::CopyStackVec;

    // NOTE: NoDefault does NOT implement Default on purpose.
    #[derive(Copy, Clone, PartialEq, Eq, Debug)]
    struct NoDefault(u8);

    #[test]
    fn test_try_from_iter_non_default_type_in_maybe_uninit_backend() {
        let items = [NoDefault(1), NoDefault(2), NoDefault(3)];
        let v: CopyStackVec<NoDefault, 4> =
            CopyStackVec::try_from_iter(items).expect("should not overflow");
        assert_eq!(v.len(), 3);
        assert_eq!(v.as_slice(), &items);

        // Overflow case
        let overflow_items = [
            NoDefault(1),
            NoDefault(2),
            NoDefault(3),
            NoDefault(4),
            NoDefault(5),
        ];
        let err = CopyStackVec::<NoDefault, 3>::try_from_iter(overflow_items).unwrap_err();
        assert_eq!(err, crate::Error::Full);
    }
    #[test]
    fn test_collect_non_default_type_in_maybe_uninit_backend() {
        let items = [NoDefault(1), NoDefault(2), NoDefault(3)];
        let v: CopyStackVec<NoDefault, 4> = items.into_iter().collect();
        assert_eq!(v.len(), 3);
        assert_eq!(v.as_slice(), &items);
    }
}
