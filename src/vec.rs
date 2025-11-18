// This file is part of copy-stack-vec.
// SPDX-License-Identifier: MIT OR Apache-2.0

//! The `CopyStackVec` type and its inherent API.
//!
//! `CopyStackVec<T, N>` is a fixed-capacity vector specialized for `Copy` types.
//! It stores elements inline in a fixed-size backing buffer and tracks a logical length.
//! Methods generally mirror slice/vector semantics, with explicit capacity checks and
//! fallible variants where appropriate.
//!
//! No heap allocations are performed.

#[cfg(not(feature = "unsafe-maybe-uninit"))]
mod array;
#[cfg(feature = "unsafe-maybe-uninit")]
mod maybe_uninit;

// Crate imports
use crate::{error::Error, iter::IntoIter};

// Core imports
use core::{
    borrow::{Borrow, BorrowMut},
    fmt,
    hash::{Hash, Hasher},
    ops::{Deref, DerefMut},
};

/// A fixed-capacity, stack-allocated vector for `Copy` types.
///
/// `CopyStackVec<T, N>` stores its elements inline in a buffer of capacity `N`
/// and tracks a logical length `len ∈ 0..=N`. Conceptually, it is a slice-like
/// view into a fixed-capacity backing array:
///
/// - capacity is known at compile time (`N`);
/// - the buffer is stored inline (typically on the stack);
/// - `T: Copy` is required, and the vector itself is `Copy`;
/// - many methods mirror `Vec`/slice semantics where they make sense;
/// - no heap allocations are performed.
///
/// This type is intended for **small capacities** (e.g. `N <= 256`) and small
/// `Copy` element types, used mostly as a local scratch buffer passed by
/// reference (`&CopyStackVec` / `&mut CopyStackVec`).
///
/// # Layout and invariants
///
/// Internally, `CopyStackVec<T, N>` maintains:
///
/// - a backing buffer of capacity `N` (either `[T; N]` or `[MaybeUninit<T>; N]`,
///   depending on the backend); and
/// - a logical length `len` with `0 <= len <= N`.
///
/// Only the prefix `buf[..len]` is considered initialized and visible through
/// safe APIs. Methods such as [`as_slice`], [`as_mut_slice`], indexing, and
/// iteration are all restricted to this prefix.
///
/// # Complexity characteristics
///
/// - The type size is roughly `N * size_of::<T>() + O(1)`.
/// - Moving or copying a `CopyStackVec<T, N>` copies the entire backing buffer,
///   not just the initialized prefix. This is `O(N)` in the capacity, *not* in
///   `len`, so you generally want to pass it by reference in hot code.
/// - In the default backend:
///   - [`Default::default`] / [`CopyStackVec::new`] initialize all `N` elements
///     with `T::default()`, which is `O(N)` and requires `T: Default`.
/// - With the `unsafe-maybe-uninit` backend enabled:
///   - [`Default::default`] / [`new`] no longer require `T: Default` and avoid
///     constructing `N` copies of `T`. The backing buffer is
///     `[MaybeUninit<T>; N]`, which is typically cheap to initialize, but still
///     conceptually `O(N)` in `N`.
/// - Most mutating operations (`push`, `pop`, `insert`, `remove`,
///   `swap_remove`, `retain`, `truncate`, `resize`) are `O(1)` or `O(len)`,
///   as you would expect from a small Vec-like container.
///
/// # Fallible vs truncating operations
///
/// Capacity-sensitive operations come in two styles:
///
/// - **Fallible** (error on overflow, no changes on error):
///
///   - [`push`](CopyStackVec::push)
///   - [`extend_from_slice`](CopyStackVec::extend_from_slice)
///   - [`resize`](CopyStackVec::resize)
///   - [`TryFrom<&[T]>`](TryFrom)
///   - [`try_from_iter`](CopyStackVec::try_from_iter)
///   - [`try_extend_from_iter`](CopyStackVec::try_extend_from_iter)
///   - [`insert`](CopyStackVec::insert)
///   - [`try_remove`](CopyStackVec::try_remove)
///   - [`try_swap_remove`](CopyStackVec::try_swap_remove)
///
///   These return [`crate::Error::Full`] when the operation would exceed
///   capacity and leave the vector unchanged.
///
/// - **Truncating** (silently drop extra elements):
///
///   - [`push_truncated`](CopyStackVec::push_truncated)
///   - [`extend_from_slice_truncated`](CopyStackVec::extend_from_slice_truncated)
///   - [`from_slice_truncated`](CopyStackVec::from_slice_truncated)
///   - [`from_array_truncated`](CopyStackVec::from_array_truncated)
///   - [`Extend<T>`](core::iter::Extend) and
///     [`FromIterator<T>`](core::iter::FromIterator):
///     collecting into `CopyStackVec<T, N>` takes the first `N` elements and
///     ignores the rest.
///
/// Choose the variant that matches your error-handling strategy: fail-fast with
/// an explicit `Error::Full`, or truncate when you only care about the prefix.
///
/// # Element and trait bounds
///
/// - `CopyStackVec<T, N>` is only defined for `T: Copy`.
/// - In the **default backend**, constructors and helpers that create a fresh buffer
///   (`Default` / `new`, `from_slice_truncated`, `FromIterator<T>`, `try_from_iter`,
///   and `drain`) additionally require `T: Default`.
/// - With the `unsafe-maybe-uninit` backend enabled, [`Default`] / [`new`]
///   only require `T: Copy`.
/// - The type implements `Copy`, `Clone`, `Deref<Target = [T]>`, `Borrow<[T]>`,
///   `AsRef<[T]>`, and `AsMut<[T]>`, so it can be used wherever a slice is
///   expected.
///
/// For `T: Copy` but not `Default`, you can still construct an empty vector
/// with a pre-filled backing buffer using [`CopyStackVec::new_with`]:
///
/// # Examples
///
/// ```rust
/// use copy_stack_vec::CopyStackVec;
///
/// let mut v: CopyStackVec<u8, 4> = CopyStackVec::default();
/// v.push(1).unwrap();
/// v.extend_from_slice(&[2, 3]).unwrap();
/// assert_eq!(v.as_slice(), &[1, 2, 3]);
///
/// #[cfg(feature = "unsafe-maybe-uninit")]
/// {
/// use copy_stack_vec::CopyStackVec;
///
/// #[derive(Copy, Clone)]
/// struct NoDefault(u8);
///
/// let mut v: CopyStackVec<NoDefault, 4> = CopyStackVec::new_with(NoDefault(0));
/// assert!(v.is_empty());
/// v.push(NoDefault(1)).unwrap();
/// v.push(NoDefault(2)).unwrap();
/// assert_eq!(v.len(), 2);
/// }
/// ```
///
/// # Limitations and trade-offs
///
/// - Moving or copying a `CopyStackVec` is `O(N)` in the capacity, not in the
///   current length.
/// - Elements must be `Copy`; this type is not suitable for non-`Copy` data
///   that needs drop semantics.
/// - Capacity is compile-time fixed. If you need dynamic growth, prefer `Vec`
///   (in `std`) or another growable container.
/// - In the default backend, some constructors require `T: Default` to be able
///   to eagerly initialize the backing buffer.
///
/// For a higher-level overview and feature discussion, see the crate-level
/// documentation in [`lib`](crate).
#[cfg(not(feature = "unsafe-maybe-uninit"))]
pub struct CopyStackVec<T: Copy, const N: usize> {
    pub(crate) buf: [T; N],
    pub(crate) len: usize,
}
#[cfg(feature = "unsafe-maybe-uninit")]
pub struct CopyStackVec<T: Copy, const N: usize> {
    pub(crate) buf: [core::mem::MaybeUninit<T>; N],
    pub(crate) len: usize,
}

impl<T: Copy, const N: usize> CopyStackVec<T, N> {
    /// The fixed capacity of this vector.
    pub const CAPACITY: usize = N;

    /// Returns the capacity of this vector (always `N`).
    #[inline]
    pub const fn capacity(&self) -> usize {
        N
    }

    /// Returns the current logical length (`0..=N`).
    #[inline]
    pub const fn len(&self) -> usize {
        self.len
    }

    /// Returns `true` if `len == 0`.
    #[inline]
    pub const fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// Returns `true` if `len == N`.
    #[inline]
    pub const fn is_full(&self) -> bool {
        self.len == N
    }

    /// Returns `N - len`, the number of additional elements that can be pushed.
    #[inline]
    pub const fn spare_capacity(&self) -> usize {
        N - self.len
    }

    /// Returns `Some(&T)` if `i < len`, otherwise `None`.
    #[inline]
    pub fn get(&self, i: usize) -> Option<&T> {
        (i < self.len).then(|| &self.as_slice()[i])
    }

    /// Returns `Some(&mut T)` if `i < len`, otherwise `None`.
    #[inline]
    pub fn get_mut(&mut self, i: usize) -> Option<&mut T> {
        (i < self.len).then(|| &mut self.as_mut_slice()[i])
    }

    // iterators
    /// Shorthand for `self.as_slice().iter()`.
    #[inline]
    pub fn iter(&self) -> core::slice::Iter<'_, T> {
        self.as_slice().iter()
    }

    /// Shorthand for `self.as_mut_slice().iter_mut()`.
    #[inline]
    pub fn iter_mut(&mut self) -> core::slice::IterMut<'_, T> {
        self.as_mut_slice().iter_mut()
    }

    /// Returns the first element, if any.
    #[inline]
    pub fn first(&self) -> Option<&T> {
        self.as_slice().first()
    }

    /// Returns the last element, if any.
    #[inline]
    pub fn last(&self) -> Option<&T> {
        self.as_slice().last()
    }

    /// Returns the first element mutably, if any.
    #[inline]
    pub fn first_mut(&mut self) -> Option<&mut T> {
        self.as_mut_slice().first_mut()
    }

    /// Returns the last element mutably, if any.
    #[inline]
    pub fn last_mut(&mut self) -> Option<&mut T> {
        self.as_mut_slice().last_mut()
    }
}

impl<T: Copy + fmt::Debug, const N: usize> fmt::Debug for CopyStackVec<T, N> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("CopyStackVec")
            .field("len", &self.len)
            .field("elements", &self.as_slice())
            .finish()
    }
}

impl<T: Copy + PartialEq, const N: usize> PartialEq for CopyStackVec<T, N> {
    fn eq(&self, other: &Self) -> bool {
        self.as_slice() == other.as_slice()
    }
}
impl<T: Copy + Eq, const N: usize> Eq for CopyStackVec<T, N> {}
impl<T: Copy + Ord, const N: usize> Ord for CopyStackVec<T, N> {
    fn cmp(&self, other: &Self) -> core::cmp::Ordering {
        self.as_slice().cmp(other.as_slice())
    }
}
impl<T: Copy + PartialOrd, const N: usize> PartialOrd for CopyStackVec<T, N> {
    fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
        self.as_slice().partial_cmp(other.as_slice())
    }
}
impl<T: Copy + Hash, const N: usize> Hash for CopyStackVec<T, N> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.as_slice().hash(state)
    }
}

impl<T: Copy, const N: usize> Copy for CopyStackVec<T, N> {}
impl<T: Copy, const N: usize> Clone for CopyStackVec<T, N> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<T: Copy, const N: usize> CopyStackVec<T, N> {
    /// Sets `len = 0` without altering the underlying values.
    #[inline]
    pub fn clear(&mut self) {
        self.len = 0;
    }

    /// Overwrites the initialized prefix with `value` and then clears the vector (`len = 0`).
    #[inline]
    pub fn clear_to(&mut self, value: T) {
        for x in self.as_mut_slice() {
            *x = value;
        }
        self.len = 0;
    }

    /// Shrinks to `new_len` if `new_len < len`; otherwise a no-op.
    #[inline]
    pub fn truncate(&mut self, new_len: usize) {
        if new_len < self.len {
            self.len = new_len;
        }
    }

    /// Resizes to `new_len`, filling with `value` when growing.
    ///
    /// Returns [`Error::Full`] if `new_len > N`.
    #[inline]
    pub fn resize(&mut self, new_len: usize, value: T) -> Result<(), Error> {
        if new_len <= self.len {
            self.len = new_len;
            return Ok(());
        }
        if new_len > N {
            return Err(Error::Full);
        }
        while self.len < new_len {
            // This cannot fail because we already checked new_len <= N.
            self.push(value)?;
        }
        Ok(())
    }

    /// Fallible variant of [`remove`], returning [`Error::OutOfBounds`] when `index >= len`.
    #[inline]
    pub fn try_remove(&mut self, index: usize) -> Result<T, Error> {
        self.remove(index).ok_or(Error::OutOfBounds)
    }

    /// Fallible variant of [`swap_remove`], returning [`Error::OutOfBounds`] when `index >= len`.
    #[inline]
    pub fn try_swap_remove(&mut self, index: usize) -> Result<T, Error> {
        self.swap_remove(index).ok_or(Error::OutOfBounds)
    }

    /// Returns `true` if the vector contains `x` (linear search on the initialized prefix).
    #[inline]
    pub fn contains(&self, x: &T) -> bool
    where
        T: PartialEq,
    {
        self.as_slice().contains(x)
    }
}

impl<T: Copy, const N: usize> Deref for CopyStackVec<T, N> {
    type Target = [T];
    fn deref(&self) -> &Self::Target {
        self.as_slice()
    }
}
impl<T: Copy, const N: usize> DerefMut for CopyStackVec<T, N> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.as_mut_slice()
    }
}

impl<T: Copy, const N: usize> CopyStackVec<T, N> {
    /// Returns an iterator over the current contents **and clears `self`**.
    ///
    /// - Items are yielded in order from front to back.
    /// - O(N) in the capacity to create (copies the backing buffer);
    ///   overall O(len) to iterate.
    /// - After calling, `self.len() == 0`.
    #[inline]
    pub fn drain_all(&mut self) -> IntoIter<T, N> {
        let len = self.len;
        let v = *self;

        // Logically clear self (we ignore what is left in buf)
        self.len = 0;

        IntoIter {
            v,
            front: 0,
            back: len,
        }
    }
}

impl<T: Copy, const N: usize> AsRef<[T]> for CopyStackVec<T, N> {
    fn as_ref(&self) -> &[T] {
        self.as_slice()
    }
}
impl<T: Copy, const N: usize> AsMut<[T]> for CopyStackVec<T, N> {
    fn as_mut(&mut self) -> &mut [T] {
        self.as_mut_slice()
    }
}

// Borrow ergonomics (treat as a slice)
impl<T: Copy, const N: usize> Borrow<[T]> for CopyStackVec<T, N> {
    fn borrow(&self) -> &[T] {
        self.as_slice()
    }
}
impl<T: Copy, const N: usize> BorrowMut<[T]> for CopyStackVec<T, N> {
    fn borrow_mut(&mut self) -> &mut [T] {
        self.as_mut_slice()
    }
}

#[cfg(test)]
mod tests {
    // Imports
    use super::CopyStackVec;

    #[test]
    fn test_push_pop() {
        let mut v: CopyStackVec<u8, 2> = CopyStackVec::default();
        v.push(1).unwrap();
        v.push(2).unwrap();
        assert!(v.push(9).is_err());
        assert_eq!(v.pop(), Some(2));
        assert_eq!(v.pop(), Some(1));
        assert_eq!(v.pop(), None);
    }

    #[test]
    fn test_default_and_capacity_full_suite() {
        let v: CopyStackVec<i32, 4> = CopyStackVec::default();
        assert_eq!(v.len(), 0);
        assert_eq!(v.capacity(), 4);
        assert!(v.is_empty());
        assert_eq!(v.spare_capacity(), 4);

        let v2: CopyStackVec<i32, 4> = CopyStackVec::new();
        assert_eq!(v2.len(), 0);
        assert_eq!(CopyStackVec::<i32, 4>::CAPACITY, 4);
    }

    #[test]
    fn test_new_with_and_clear_variants() {
        let mut v: CopyStackVec<u8, 3> = CopyStackVec::new_with(7);
        assert_eq!(v.len(), 0);
        v.push(1).unwrap();
        v.push(2).unwrap();
        v.push(3).unwrap();
        assert_eq!(v.as_slice(), &[1, 2, 3]);

        v.clear_to(9);
        assert_eq!(v.len(), 0);
        v.push(4).unwrap();
        assert_eq!(v.as_slice(), &[4]);

        v.clear();
        assert!(v.is_empty());
        assert_eq!(v.spare_capacity(), 3);
    }

    #[test]
    fn test_push_pop_and_full_error_full_suite() {
        let mut v: CopyStackVec<i32, 2> = CopyStackVec::default();
        assert_eq!(v.push(10), Ok(()));
        assert_eq!(v.push(20), Ok(()));
        assert_eq!(v.push(30), Err(crate::Error::Full));
        assert!(v.is_full());
        assert_eq!(v.pop(), Some(20));
        assert_eq!(v.pop(), Some(10));
        assert_eq!(v.pop(), None);
        assert!(v.is_empty());
        assert_eq!(v.spare_capacity(), 2);
    }

    #[test]
    fn test_push_truncated() {
        let mut v: CopyStackVec<i32, 2> = CopyStackVec::default();
        assert!(v.push_truncated(1));
        assert!(v.push_truncated(2));
        assert!(!v.push_truncated(3));
        assert_eq!(v.as_slice(), &[1, 2]);
    }

    #[test]
    fn test_extend_from_slice_and_truncated() {
        let mut v: CopyStackVec<u8, 5> = CopyStackVec::default();
        assert_eq!(v.extend_from_slice(&[1, 2, 3]), Ok(()));
        assert_eq!(v.as_slice(), &[1, 2, 3]);
        assert_eq!(v.extend_from_slice(&[4, 5, 6]), Err(crate::Error::Full));
        let pushed = v.extend_from_slice_truncated(&[4, 5, 6]);
        assert_eq!(pushed, 2);
        assert_eq!(v.as_slice(), &[1, 2, 3, 4, 5]);
        assert!(v.is_full());
    }

    #[test]
    fn test_extend_from_slice_err_is_noop() {
        let mut v: CopyStackVec<i32, 3> = CopyStackVec::try_from(&[1, 2][..]).unwrap();
        let before = v.as_slice().to_vec();
        let res = v.extend_from_slice(&[3, 4]); // needs 2, spare 1 -> Err
        assert_eq!(res, Err(crate::Error::Full));
        assert_eq!(v.as_slice(), &before[..]); // unchanged
    }

    #[test]
    fn test_truncate_and_resize() {
        let mut v: CopyStackVec<i32, 5> = CopyStackVec::default();
        v.extend_from_slice(&[1, 2, 3, 4]).unwrap();
        v.truncate(2);
        assert_eq!(v.as_slice(), &[1, 2]);
        v.resize(5, 9).unwrap();
        assert_eq!(v.as_slice(), &[1, 2, 9, 9, 9]);
        v.resize(3, 0).unwrap();
        assert_eq!(v.as_slice(), &[1, 2, 9]);
        let mut w: CopyStackVec<i32, 3> = CopyStackVec::default();
        assert_eq!(w.resize(4, 7), Err(crate::Error::Full));
    }

    #[test]
    fn test_retain_is_stable() {
        let mut v: CopyStackVec<i32, 10> = CopyStackVec::default();
        v.extend_from_slice(&[1, 2, 3, 4, 5, 6]).unwrap();
        v.retain(|x| x % 2 == 0);
        assert_eq!(v.as_slice(), &[2, 4, 6]);
    }

    #[test]
    fn test_insert_remove_and_swap_remove() {
        let mut v: CopyStackVec<i32, 5> = CopyStackVec::default();
        v.extend_from_slice(&[10, 20, 30]).unwrap();
        v.insert(1, 15).unwrap();
        assert_eq!(v.as_slice(), &[10, 15, 20, 30]);
        v.insert(4, 35).unwrap();
        assert_eq!(v.as_slice(), &[10, 15, 20, 30, 35]);
        assert_eq!(v.insert(0, 0), Err(crate::Error::Full));

        let mut w: CopyStackVec<i32, 3> = CopyStackVec::default();
        w.extend_from_slice(&[1, 2]).unwrap();
        assert_eq!(w.insert(3, 9), Err(crate::Error::OutOfBounds));

        let mut r: CopyStackVec<i32, 5> = CopyStackVec::from([1, 2, 3, 4, 5]);
        assert_eq!(r.remove(2), Some(3));
        assert_eq!(r.as_slice(), &[1, 2, 4, 5]);
        assert_eq!(r.try_remove(8), Err(crate::Error::OutOfBounds));

        let mut s: CopyStackVec<i32, 5> = CopyStackVec::from([1, 2, 3, 4, 5]);
        assert_eq!(s.swap_remove(1), Some(2));
        assert_eq!(s.as_slice(), &[1, 5, 3, 4]);
        assert_eq!(s.try_swap_remove(10), Err(crate::Error::OutOfBounds));
    }

    #[test]
    fn test_insert_err_is_noop() {
        let mut v: CopyStackVec<i32, 2> = CopyStackVec::try_from(&[10, 20][..]).unwrap();
        let before = v.as_slice().to_vec();
        assert_eq!(v.insert(3, 99), Err(crate::Error::OutOfBounds));
        assert_eq!(v.as_slice(), &before[..]);
        assert_eq!(v.insert(0, 1), Err(crate::Error::Full));
        assert_eq!(v.as_slice(), &before[..]);
    }

    #[test]
    fn test_contains_and_getters() {
        let mut v: CopyStackVec<i32, 4> = CopyStackVec::default();
        v.extend_from_slice(&[7, 8, 9]).unwrap();
        assert!(v.contains(&7));
        assert!(!v.contains(&10));
        assert_eq!(v.first(), Some(&7));
        assert_eq!(v.last(), Some(&9));
        assert_eq!(v.get(1), Some(&8));
        assert_eq!(v.get(3), None);
        *v.get_mut(1).unwrap() = 80;
        assert_eq!(v.as_slice(), &[7, 80, 9]);
        let len = v.len();
        assert_eq!(v.get(len), None);
        assert!(v.get_mut(len - 1).is_some());
    }

    #[test]
    fn test_deref_and_as_ref() {
        let mut v: CopyStackVec<i32, 3> = CopyStackVec::default();
        v.extend_from_slice(&[1, 2]).unwrap();
        let s: &[i32] = &v;
        assert_eq!(s, &[1, 2]);
        let smut: &mut [i32] = &mut v;
        smut[1] = 22;
        assert_eq!(v.as_slice(), &[1, 22]);
        let aref: &[i32] = v.as_ref();
        assert_eq!(aref, &[1, 22]);
        let amut: &mut [i32] = v.as_mut();
        amut[0] = 11;
        assert_eq!(v.as_slice(), &[11, 22]);
    }

    #[test]
    fn test_try_into_array_and_conversions() {
        let v_full: CopyStackVec<u8, 3> = [7, 8, 9].into();
        let arr = v_full.try_into_array().unwrap();
        assert_eq!(arr, [7, 8, 9]);

        let v_not_full: CopyStackVec<u8, 3> = CopyStackVec::from_slice_truncated(&[1, 2]);
        assert_eq!(v_not_full.try_into_array(), Err(crate::Error::InvalidLen));

        let v2 = <CopyStackVec<u8, 4>>::try_from(&[1, 2, 3][..]).unwrap();
        assert_eq!(v2.as_slice(), &[1, 2, 3]);

        let v3 = <CopyStackVec<u8, 3>>::try_from_iter([10, 11, 12]).unwrap();
        assert_eq!(v3.as_slice(), &[10, 11, 12]);

        let err = <CopyStackVec<u8, 2>>::try_from_iter([1, 2, 3]).unwrap_err();
        assert_eq!(err, crate::Error::Full);
    }

    #[test]
    fn test_eq_ord_partial_ord_hash_via_slice() {
        use core::cmp::Ordering;
        use core::hash::{Hash, Hasher};
        use std::collections::hash_map::DefaultHasher;

        let a: CopyStackVec<i32, 4> = CopyStackVec::try_from(&[1, 2, 3][..]).unwrap();
        let b: CopyStackVec<i32, 4> = CopyStackVec::try_from(&[1, 2, 3][..]).unwrap();
        let c: CopyStackVec<i32, 4> = CopyStackVec::try_from(&[1, 2, 4][..]).unwrap();

        assert_eq!(a, b);
        assert_ne!(a, c);
        assert_eq!(a.cmp(&b), Ordering::Equal);
        assert_eq!(a.partial_cmp(&c), Some(Ordering::Less));

        let mut ha = DefaultHasher::new();
        a.hash(&mut ha);
        let mut hb = DefaultHasher::new();
        [1, 2, 3][..].hash(&mut hb);
        assert_eq!(ha.finish(), hb.finish());
    }

    #[test]
    fn test_debug_structure_and_error_display() {
        use alloc::format;
        let v: CopyStackVec<i32, 5> = CopyStackVec::try_from(&[1, 2][..]).unwrap();
        let dbg = format!("{v:?}");
        assert!(dbg.contains("CopyStackVec"));
        assert!(dbg.contains("len"));
        assert!(dbg.contains("elements"));
        assert!(dbg.contains("[1, 2]"));
        assert_eq!(crate::Error::Full.to_string(), "capacity exceeded");
        assert_eq!(crate::Error::OutOfBounds.to_string(), "index out of bounds");
        assert_eq!(crate::Error::InvalidLen.to_string(), "invalid length");
    }

    #[test]
    fn test_as_ptr_and_as_mut_ptr() {
        let mut v: CopyStackVec<u16, 4> = CopyStackVec::try_from(&[10, 20][..]).unwrap();
        // Compare raw pointers against slice pointers (safe).
        let p_const = v.as_ptr();
        let p_slice = v.as_slice().as_ptr();
        assert_eq!(p_const, p_slice);

        // For mut ptr, compare addresses and also mutate via safe APIs to ensure view is live.
        let p_mut = v.as_mut_ptr();
        let p_mut_slice = v.as_mut_slice().as_mut_ptr();
        assert_eq!(p_mut, p_mut_slice);

        // Mutate safely through the slice and verify contents.
        {
            let s = v.as_mut_slice();
            s[1] = 21;
        }
        assert_eq!(v.as_slice(), &[10, 21]);
    }

    #[test]
    fn zero_capacity_vec_behaves() {
        let mut v: CopyStackVec<u8, 0> = CopyStackVec::default();
        assert_eq!(v.capacity(), 0);
        assert!(v.is_empty());
        assert!(v.is_full());

        assert_eq!(v.push(1), Err(crate::Error::Full));
        assert_eq!(v.extend_from_slice(&[1, 2]), Err(crate::Error::Full));
        assert_eq!(v.extend_from_slice_truncated(&[1, 2, 3]), 0);

        assert_eq!(v.resize(0, 9), Ok(()));
        assert_eq!(v.resize(1, 9), Err(crate::Error::Full));
        assert_eq!(v.pop(), None);

        // try_into_array must succeed for N=0 when len==0
        let arr = v.try_into_array().unwrap();
        assert_eq!(arr.len(), 0);
    }

    #[test]
    fn test_zero_sized_type_supports_capacity() {
        // ZST like () should work; capacity N, len arithmetic should still be correct.
        let mut v: CopyStackVec<(), 4> = CopyStackVec::default();
        assert_eq!(v.len(), 0);
        v.push(()).unwrap();
        v.push(()).unwrap();
        assert_eq!(v.len(), 2);
        v.truncate(1);
        assert_eq!(v.len(), 1);
        v.resize(4, ()).unwrap();
        assert!(v.is_full());
        assert_eq!(v.try_into_array().unwrap().len(), 4);
    }

    #[test]
    fn test_insert_at_bounds_and_shift_correctly() {
        let mut v: CopyStackVec<i32, 4> = CopyStackVec::default();
        v.insert(0, 1).unwrap(); // insert at front into empty
        v.insert(1, 3).unwrap(); // tail
        v.insert(1, 2).unwrap(); // middle, shifts right
        assert_eq!(v.as_slice(), &[1, 2, 3]);
        v.insert(3, 4).unwrap(); // exactly at len
        assert_eq!(v.as_slice(), &[1, 2, 3, 4]);
        assert_eq!(v.insert(0, 9), Err(crate::Error::Full)); // full
    }

    #[test]
    fn test_swap_remove_last_index_is_o1() {
        let mut v: CopyStackVec<i32, 4> = CopyStackVec::try_from(&[10, 20, 30][..]).unwrap();
        assert_eq!(v.swap_remove(2), Some(30)); // removing last should not do a swap
        assert_eq!(v.as_slice(), &[10, 20]);
    }

    #[test]
    fn test_retain_all_and_retain_none() {
        let mut v: CopyStackVec<i32, 5> = CopyStackVec::try_from(&[1, 2, 3][..]).unwrap();
        v.retain(|_| true);
        assert_eq!(v.as_slice(), &[1, 2, 3]);
        v.retain(|_| false);
        assert!(v.is_empty());
    }

    #[test]
    fn test_resize_to_same_len_is_noop() {
        let mut v: CopyStackVec<i32, 3> = CopyStackVec::try_from(&[1, 2, 3][..]).unwrap();
        assert!(v.is_full());
        v.resize(3, 9).unwrap(); // no-op
        assert_eq!(v.as_slice(), &[1, 2, 3]);
    }

    #[test]
    fn test_resize_err_is_noop() {
        let mut v: CopyStackVec<i32, 2> = CopyStackVec::try_from(&[1][..]).unwrap();
        let before = v.as_slice().to_vec();
        assert_eq!(v.resize(3, 9), Err(crate::Error::Full));
        assert_eq!(v.as_slice(), &before[..]);
    }

    #[test]
    fn test_from_slice_truncated_really_truncates() {
        let v: CopyStackVec<i32, 3> = CopyStackVec::from_slice_truncated(&[5, 6, 7, 8, 9]);
        assert_eq!(v.as_slice(), &[5, 6, 7]);
        assert!(v.is_full());
    }

    #[test]
    fn test_extend_and_resize_with_empty_input_are_no_ops() {
        let mut v: CopyStackVec<i32, 3> = CopyStackVec::try_from(&[1, 2][..]).unwrap();
        assert_eq!(v.extend_from_slice(&[]), Ok(()));
        assert_eq!(v.as_slice(), &[1, 2]);
        let before = v.len();
        v.truncate(before); // no-op truncate path
        assert_eq!(v.len(), before);
    }

    #[test]
    fn test_try_from_iter_over_capacity_errors() {
        let res = <CopyStackVec<i32, 3>>::try_from_iter([1, 2, 3, 4]);
        assert_eq!(res.unwrap_err(), crate::Error::Full);
    }

    #[test]
    fn test_extend_trait_truncates() {
        let mut v: CopyStackVec<i32, 3> = CopyStackVec::default();
        v.extend([1, 2, 3, 4, 5]);
        assert_eq!(v.as_slice(), &[1, 2, 3]);
        assert!(v.is_full());
    }

    #[test]
    fn test_extend_preserves_prefix_and_truncates_tail() {
        let mut v: CopyStackVec<i32, 4> = CopyStackVec::try_from(&[1, 2][..]).unwrap();
        v.extend([3, 4, 5]);
        assert_eq!(v.as_slice(), &[1, 2, 3, 4]);
    }

    #[test]
    fn test_extend_does_not_overconsume() {
        struct ExtendTestIter {
            remaining: usize,
            next_calls: usize,
        }

        impl Iterator for ExtendTestIter {
            type Item = u8;
            fn next(&mut self) -> Option<u8> {
                if self.remaining == 0 {
                    return None;
                }
                self.remaining -= 1;
                self.next_calls += 1;
                Some(1)
            }
        }
        let mut it = ExtendTestIter {
            remaining: 10,
            next_calls: 0,
        };
        let mut vec: CopyStackVec<u8, 4> = CopyStackVec::default();

        // Note: &mut it implements IntoIterator via &mut MyIter → Iterator
        vec.extend(&mut it);

        assert_eq!(vec.len(), 4);
        assert_eq!(it.next_calls, 4); // must not be 5
    }

    #[test]
    fn test_drain_all_yields_all_and_clears() {
        let mut v: CopyStackVec<i32, 4> = CopyStackVec::try_from(&[10, 20, 30][..]).unwrap();
        let drained: alloc::vec::Vec<_> = v.drain_all().collect();
        assert_eq!(drained, [10, 20, 30]);
        assert!(v.is_empty());
    }

    #[test]
    fn test_remove_and_swap_remove_oob_return_none() {
        let mut v: CopyStackVec<i32, 2> = CopyStackVec::from_slice_truncated(&[1, 2]);
        assert_eq!(v.remove(5), None);
        assert_eq!(v.swap_remove(5), None);
    }

    #[test]
    fn test_must_use_push_truncated() {
        let mut v: CopyStackVec<i32, 1> = Default::default();
        let _ = v.push_truncated(1);
        // compile-fail tests would be ideal, but at least we can assert behavior
        assert!(!v.push_truncated(2)); // returns false
    }

    #[test]
    fn test_retain_keeps_edges() {
        let mut v: CopyStackVec<i32, 8> = CopyStackVec::try_from(&[1, 2, 3, 4][..]).unwrap();
        v.retain(|x| *x == 1 || *x == 4);
        assert_eq!(v.as_slice(), &[1, 4]);
    }

    #[test]
    fn test_remove_first_and_last() {
        let mut v: CopyStackVec<i32, 5> = [1, 2, 3, 4, 5].into();
        assert_eq!(v.remove(0), Some(1));
        assert_eq!(v.remove(v.len() - 1), Some(5));
        assert_eq!(v.as_slice(), &[2, 3, 4]);
    }

    #[test]
    fn test_swap_remove_first_and_last() {
        let mut v: CopyStackVec<i32, 4> = [10, 20, 30, 40].into();

        assert_eq!(v.swap_remove(0), Some(10));
        assert!(v.contains(&20) && v.contains(&30) && v.contains(&40));

        let last = v.len() - 1;
        let expected = v.as_slice()[last]; // capture before mutation
        assert_eq!(v.swap_remove(last), Some(expected));

        // (optional) sanity: now only two remain, and neither is the removed `expected`
        assert_eq!(v.len(), 2);
        assert!(!v.contains(&expected));
    }

    #[test]
    fn test_drain_all_then_reuse() {
        let mut v: CopyStackVec<i32, 4> = CopyStackVec::try_from(&[1, 2, 3][..]).unwrap();
        let collected: alloc::vec::Vec<_> = v.drain_all().collect();
        assert_eq!(collected, [1, 2, 3]);
        assert!(v.is_empty());
        v.extend_from_slice(&[9, 9]).unwrap();
        assert_eq!(v.as_slice(), &[9, 9]);
    }

    #[test]
    fn test_from_iterator_truncates_at_capacity() {
        let v: CopyStackVec<u8, 3> = [10, 20, 30, 40, 50].into_iter().collect();
        // Should take only the first 3 items
        assert_eq!(v.as_slice(), &[10, 20, 30]);
        assert!(v.is_full());
    }

    #[test]
    fn test_from_iterator_zero_capacity() {
        let v: CopyStackVec<u8, 0> = [1, 2, 3].into_iter().collect();
        assert_eq!(v.len(), 0);
        assert!(v.is_full());
    }

    #[test]
    fn test_from_iterator_zst() {
        let v: CopyStackVec<(), 2> = core::iter::repeat_n((), 5).collect();
        // capacity 2, but all elements are ()
        assert_eq!(v.len(), 2);
        let slice = v.as_slice();
        assert_eq!(slice.len(), 2);
    }

    #[test]
    fn test_from_array_ref_fills_full_capacity() {
        let arr = [1, 2, 3];
        let v: CopyStackVec<i32, 3> = (&arr).into();
        assert_eq!(v.len(), 3);
        assert_eq!(v.as_slice(), &[1, 2, 3]);
        assert!(v.is_full());
    }

    #[test]
    fn test_drain_middle_range() {
        // Build from slice; works in both backends.
        let mut v: CopyStackVec<i32, 8> = CopyStackVec::try_from(&[1, 2, 3, 4, 5][..]).unwrap();

        let drained: CopyStackVec<i32, 8> = v.drain(1..4).collect();
        assert_eq!(drained.as_slice(), &[2, 3, 4]);
        assert_eq!(v.as_slice(), &[1, 5]);
        assert_eq!(v.len(), 2);
    }

    #[test]
    fn test_drain_full_range() {
        let mut v: CopyStackVec<i32, 4> = CopyStackVec::try_from(&[10, 20, 30, 40][..]).unwrap();

        let drained: CopyStackVec<i32, 4> = v.drain(..).collect();
        assert_eq!(drained.as_slice(), &[10, 20, 30, 40]);
        assert!(v.is_empty());
        assert_eq!(v.len(), 0);
    }

    #[test]
    fn test_drain_empty_range_is_noop_on_data() {
        let mut v: CopyStackVec<i32, 5> = CopyStackVec::try_from(&[1, 2, 3, 4, 5][..]).unwrap();
        let before = v.as_slice().to_vec();
        let len_before = v.len();

        let drained: CopyStackVec<i32, 5> = v.drain(2..2).collect();
        assert!(drained.is_empty());
        assert_eq!(v.as_slice(), &before[..]);
        assert_eq!(v.len(), len_before);
    }

    #[test]
    fn test_drain_prefix_and_suffix() {
        let mut v: CopyStackVec<i32, 6> = CopyStackVec::try_from(&[1, 2, 3, 4, 5][..]).unwrap();

        // Drain prefix [1, 2]
        let drained_prefix: CopyStackVec<i32, 6> = v.drain(..2).collect();
        assert_eq!(drained_prefix.as_slice(), &[1, 2]);
        assert_eq!(v.as_slice(), &[3, 4, 5]);

        // Drain suffix [4, 5] from the updated vec
        let drained_suffix: CopyStackVec<i32, 6> = v.drain(1..).collect();
        assert_eq!(drained_suffix.as_slice(), &[4, 5]);
        assert_eq!(v.as_slice(), &[3]);
    }

    #[test]
    fn test_drain_double_ended_iteration() {
        let mut v: CopyStackVec<i32, 8> = CopyStackVec::try_from(&[1, 2, 3, 4, 5][..]).unwrap();
        {
            let mut it = v.drain(1..4); // should drain [2,3,4]

            // Use both ends of the iterator.
            assert_eq!(it.next_back(), Some(4));
            assert_eq!(it.next(), Some(2));
            assert_eq!(it.next(), Some(3));
            assert_eq!(it.next_back(), None);
        }
        // Remaining vector should be [1,5].
        assert_eq!(v.as_slice(), &[1, 5]);
    }

    #[test]
    fn test_drain_size_hint_tracks_consumption() {
        let mut v: CopyStackVec<i32, 8> = CopyStackVec::try_from(&[1, 2, 3, 4, 5][..]).unwrap();

        {
            let mut it = v.drain(1..4); // draining 3 elements

            assert_eq!(it.size_hint(), (3, Some(3)));
            assert_eq!(it.next(), Some(2));
            assert_eq!(it.size_hint(), (2, Some(2)));
            assert_eq!(it.next_back(), Some(4));
            assert_eq!(it.size_hint(), (1, Some(1)));
            assert_eq!(it.next(), Some(3));
            assert_eq!(it.size_hint(), (0, Some(0)));
            assert_eq!(it.next(), None);
        }
        // Remaining elements in vec: [1,5]
        assert_eq!(v.as_slice(), &[1, 5]);
    }

    #[test]
    #[should_panic]
    fn test_drain_end_out_of_bounds_panics() {
        let mut v: CopyStackVec<i32, 4> = CopyStackVec::try_from(&[1, 2, 3, 4][..]).unwrap();
        // end > len should panic
        let _ = v.drain(2..10);
    }

    #[test]
    #[should_panic]
    #[allow(clippy::reversed_empty_ranges)]
    fn test_drain_start_greater_than_end_panics() {
        let mut v: CopyStackVec<i32, 4> = CopyStackVec::try_from(&[1, 2, 3, 4][..]).unwrap();
        // inverted range should panic
        let _ = v.drain(3..1);
    }

    #[test]
    fn test_drain_zero_capacity_vec() {
        let mut v: CopyStackVec<u8, 0> = CopyStackVec::default();
        assert_eq!(v.len(), 0);
        assert!(v.is_full());

        {
            let mut it = v.drain(..);
            assert_eq!(it.size_hint(), (0, Some(0)));
            assert_eq!(it.next(), None);
        }

        // Still zero-length and zero-capacity.
        assert_eq!(v.len(), 0);
        assert!(v.is_full());
    }

    #[test]
    fn test_drain_zst() {
        let mut v: CopyStackVec<(), 4> = CopyStackVec::from([(), (), (), ()]);

        let drained: CopyStackVec<(), 4> = v.drain(1..3).collect();
        assert_eq!(drained.len(), 2);

        // Remaining 2 elements: positions [0] and [3] collapsed to [0] and [1]
        assert_eq!(v.len(), 2);
    }

    #[test]
    fn test_first_and_last_mut() {
        let mut v: CopyStackVec<i32, 4> = CopyStackVec::try_from(&[1, 2, 3][..]).unwrap();

        // Mutate first via first_mut
        if let Some(first) = v.first_mut() {
            *first = 10;
        }
        // Mutate last via last_mut
        if let Some(last) = v.last_mut() {
            *last = 30;
        }

        assert_eq!(v.as_slice(), &[10, 2, 30]);

        // Empty vector: both should be None
        let mut empty: CopyStackVec<i32, 4> = CopyStackVec::default();
        assert!(empty.first_mut().is_none());
        assert!(empty.last_mut().is_none());
    }

    #[test]
    fn test_iter_and_iter_mut() {
        let mut v: CopyStackVec<i32, 4> = CopyStackVec::try_from(&[1, 2, 3, 4][..]).unwrap();

        // iter() should yield all elements by shared reference in order
        let collected: alloc::vec::Vec<_> = v.iter().copied().collect();
        assert_eq!(collected, alloc::vec![1, 2, 3, 4]);

        // iter_mut() should allow in-place mutation
        for x in v.iter_mut() {
            *x *= 2;
        }
        assert_eq!(v.as_slice(), &[2, 4, 6, 8]);

        // After iter_mut, length and contents are still consistent
        assert_eq!(v.len(), 4);
    }

    #[test]
    fn test_borrow_and_borrow_mut_behave_like_slice() {
        use core::borrow::{Borrow, BorrowMut};

        let mut v: CopyStackVec<i32, 3> = CopyStackVec::try_from(&[1, 2, 3][..]).unwrap();

        // Borrow<[T]> should give us the same view as as_slice()
        let b: &[i32] = Borrow::<[i32]>::borrow(&v);
        assert_eq!(b, &[1, 2, 3]);
        assert_eq!(b, v.as_slice());

        // BorrowMut<[T]> should give a mutable slice into the same data
        {
            let bm: &mut [i32] = BorrowMut::<[i32]>::borrow_mut(&mut v);
            bm[1] = 20;
        }

        // Mutations through BorrowMut are visible on the vector
        assert_eq!(v.as_slice(), &[1, 20, 3]);
    }

    #[test]
    fn test_into_iter_shared_ref() {
        let v: CopyStackVec<i32, 4> = CopyStackVec::try_from(&[1, 2, 3][..]).unwrap();

        let mut collected = alloc::vec::Vec::new();
        for x in &v {
            // uses IntoIterator for &CopyStackVec
            collected.push(*x);
        }

        assert_eq!(collected, alloc::vec![1, 2, 3]);

        // original must remain unchanged
        assert_eq!(v.as_slice(), &[1, 2, 3]);
    }

    #[test]
    fn test_into_iter_mutable_ref() {
        let mut v: CopyStackVec<i32, 4> = CopyStackVec::try_from(&[1, 2, 3][..]).unwrap();

        for x in &mut v {
            // uses IntoIterator for &mut CopyStackVec
            *x *= 10;
        }

        assert_eq!(v.as_slice(), &[10, 20, 30]);
    }

    #[test]
    fn test_into_iter_refs_empty() {
        let mut v: CopyStackVec<i32, 4> = CopyStackVec::default();

        assert_eq!((&v).into_iter().count(), 0);
        assert_eq!((&mut v).into_iter().count(), 0);
    }

    #[test]
    #[allow(clippy::clone_on_copy)]
    fn test_clone_copies_len_and_elements() {
        let mut v: CopyStackVec<i32, 4> = CopyStackVec::default();
        v.extend_from_slice(&[1, 2, 3]).unwrap();

        let c = v.clone();

        // Clone should have same length and contents
        assert_eq!(c.len(), v.len());
        assert_eq!(c.as_slice(), v.as_slice());
    }

    #[test]
    #[allow(clippy::clone_on_copy)]
    fn test_clone_is_independent_copy() {
        let mut v: CopyStackVec<i32, 4> = CopyStackVec::default();
        v.extend_from_slice(&[1, 2, 3]).unwrap();

        let mut c = v.clone();

        // Mutate original
        v[1] = 20;
        // Mutate clone
        c[2] = 30;

        // Changes must not leak across copies
        assert_eq!(v.as_slice(), &[1, 20, 3]);
        assert_eq!(c.as_slice(), &[1, 2, 30]);
    }

    #[test]
    #[allow(clippy::clone_on_copy)]
    fn test_clone_zero_capacity_vec() {
        let v: CopyStackVec<u8, 0> = CopyStackVec::default();
        let c = v.clone();

        assert_eq!(v.len(), 0);
        assert_eq!(c.len(), 0);
        assert!(v.is_full());
        assert!(c.is_full());
    }

    #[test]
    fn test_drain_inclusive_end_uses_bound_included_branch() {
        let mut v: CopyStackVec<i32, 8> = CopyStackVec::try_from(&[1, 2, 3, 4, 5][..]).unwrap();

        // ..=2 corresponds to end Bound::Included(2) → end = 2 + 1 = 3
        let drained: CopyStackVec<i32, 8> = v.drain(..=2).collect();

        // Drained indices [0, 1, 2] → [1, 2, 3]
        assert_eq!(drained.as_slice(), &[1, 2, 3]);
        // Remaining should be [4, 5]
        assert_eq!(v.as_slice(), &[4, 5]);
    }

    #[test]
    fn test_drain_excluded_start_uses_bound_excluded_branch() {
        use core::ops::{Bound, RangeBounds};
        struct ExcludedStartRange {
            start: usize,
            end: usize,
        }

        impl RangeBounds<usize> for ExcludedStartRange {
            fn start_bound(&self) -> Bound<&usize> {
                // This hits: Bound::Excluded(&i) => i + 1
                Bound::Excluded(&self.start)
            }

            fn end_bound(&self) -> Bound<&usize> {
                // Use Included here so we also exercise the included-end path in one go.
                Bound::Included(&self.end)
            }
        }

        // Indexes: 0  1  2  3  4
        // Values:  10 20 30 40 50
        let mut v: CopyStackVec<i32, 8> =
            CopyStackVec::try_from(&[10, 20, 30, 40, 50][..]).unwrap();

        // start = Excluded(1) → start = 1 + 1 = 2
        // end   = Included(3) → end   = 3 + 1 = 4
        // So we drain indices [2, 3] => [30, 40].
        let drained: CopyStackVec<i32, 8> =
            v.drain(ExcludedStartRange { start: 1, end: 3 }).collect();

        assert_eq!(drained.as_slice(), &[30, 40]);
        // Remaining elements should be [10, 20, 50]
        assert_eq!(v.as_slice(), &[10, 20, 50]);
    }

    #[test]
    fn test_drain_nth_and_nth_back() {
        // Original: [1, 2, 3, 4, 5]
        let mut v: CopyStackVec<i32, 8> = CopyStackVec::try_from(&[1, 2, 3, 4, 5][..]).unwrap();

        {
            // Drain the middle three: [2, 3, 4]
            let mut it = v.drain(1..4);

            // Drain iterator contents: [2, 3, 4]
            // nth(1) should skip 2 and yield 3
            assert_eq!(it.nth(1), Some(3));

            // Now only [4] remains in the drain iterator
            // nth_back(0) should yield 4
            assert_eq!(it.nth_back(0), Some(4));

            // Fully consumed
            assert_eq!(it.next(), None);
        }

        // Parent vector should now contain [1, 5]
        assert_eq!(v.as_slice(), &[1, 5]);
    }

    #[test]
    fn test_drain_nth_and_nth_back_overflow() {
        let mut v: CopyStackVec<i32, 8> = CopyStackVec::try_from(&[10, 20, 30, 40][..]).unwrap();

        {
            // Drain all 4 elements
            let mut it = v.drain(..);

            // Remaining = 4; nth(4) should return None and fully exhaust
            assert_eq!(it.nth(4), None);
            assert_eq!(it.next(), None);
        }

        {
            // Another drain on the now-empty vec still works and is empty
            let mut it2 = v.drain(..);
            assert_eq!(it2.nth_back(0), None);
            assert_eq!(it2.next_back(), None);
        }

        // Parent vec should be empty after draining everything
        assert!(v.is_empty());
        assert_eq!(v.len(), 0);
    }

    #[test]
    fn test_try_extend_from_iter_all_or_nothing() {
        // Success: everything fits
        let mut v: CopyStackVec<i32, 5> = CopyStackVec::try_from(&[1, 2][..]).unwrap();
        v.try_extend_from_iter([3, 4]).unwrap();
        assert_eq!(v.as_slice(), &[1, 2, 3, 4]);

        // Error: iterator yields more than spare_capacity()
        let mut w: CopyStackVec<i32, 4> = CopyStackVec::try_from(&[10, 20][..]).unwrap();
        let before = w.as_slice().to_vec();

        let err = w.try_extend_from_iter([30, 40, 50]).unwrap_err();
        assert_eq!(err, crate::Error::Full);

        // Vector unchanged on error
        assert_eq!(w.as_slice(), &before[..]);
    }

    #[test]
    fn test_try_extend_from_iter_zero_spare_capacity() {
        let mut v: CopyStackVec<i32, 2> = CopyStackVec::try_from(&[1, 2][..]).unwrap();
        assert!(v.is_full());

        // Any element at all should cause Error::Full
        let err = v.try_extend_from_iter([3]).unwrap_err();
        assert_eq!(err, crate::Error::Full);

        // Empty iterator is fine and leaves vector unchanged
        v.try_extend_from_iter(core::iter::empty()).unwrap();
        assert_eq!(v.as_slice(), &[1, 2]);
    }

    #[test]
    fn test_split_off_basic() {
        let mut v: CopyStackVec<i32, 5> = CopyStackVec::try_from(&[10, 20, 30, 40][..]).unwrap();
        let tail = v.split_off(2).unwrap();

        assert_eq!(v.as_slice(), &[10, 20]);
        assert_eq!(tail.as_slice(), &[30, 40]);
    }

    #[test]
    fn test_split_off_at_len_and_empty() {
        // Split at len → empty tail
        let mut v: CopyStackVec<i32, 4> = CopyStackVec::try_from(&[1, 2, 3][..]).unwrap();
        let tail = v.split_off(v.len()).unwrap();
        assert_eq!(v.as_slice(), &[1, 2, 3]);
        assert!(tail.is_empty());

        // Split an empty vec → both sides empty
        let mut empty: CopyStackVec<i32, 4> = CopyStackVec::default();
        let tail2 = empty.split_off(0).unwrap();
        assert!(empty.is_empty());
        assert!(tail2.is_empty());
    }

    #[test]
    fn test_split_off_out_of_bounds_errors_and_is_noop() {
        let mut v: CopyStackVec<i32, 3> = CopyStackVec::try_from(&[1, 2][..]).unwrap();
        let before = v.as_slice().to_vec();

        let err = v.split_off(3).unwrap_err();
        assert_eq!(err, crate::Error::OutOfBounds);

        // Vector unchanged on error
        assert_eq!(v.as_slice(), &before[..]);
    }

    #[test]
    fn test_from_array_truncated() {
        // M > N: should truncate
        let arr = [1, 2, 3, 4];
        let v: CopyStackVec<i32, 2> = CopyStackVec::from_array_truncated(&arr);
        assert_eq!(v.as_slice(), &[1, 2]);
        assert!(v.is_full());

        // M == N: should take all
        let arr2 = [10, 20, 30];
        let v2: CopyStackVec<i32, 3> = CopyStackVec::from_array_truncated(&arr2);
        assert_eq!(v2.as_slice(), &[10, 20, 30]);
        assert!(v2.is_full());

        // M < N: should just fill len = M
        let arr3 = [7, 8];
        let v3: CopyStackVec<i32, 4> = CopyStackVec::from_array_truncated(&arr3);
        assert_eq!(v3.as_slice(), &[7, 8]);
        assert_eq!(v3.len(), 2);
        assert!(!v3.is_full());
    }
}
