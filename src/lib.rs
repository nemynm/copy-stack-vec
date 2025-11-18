// This file is part of copy-stack-vec.
// SPDX-License-Identifier: MIT OR Apache-2.0

//! # `copy-stack-vec`
//!
//! A `no_std`, fixed-capacity, stack-based vector type for `Copy` elements,
//! **with no `unsafe` by default**.
//!
//! The core type, [`CopyStackVec<T, N>`], stores `N` elements inline on the stack
//! and tracks a logical length `len ∈ 0..=N`. It provides
//! a small, predictable, allocation-free buffer with familiar slice/`Vec`-like
//! semantics where they make sense.
//!
//! ## When to use this crate
//!
//! This crate may be useful when:
//!
//! - You are in a `no_std` or embedded environment.
//! - You know capacities at compile time.
//! - Elements are small and `Copy`.
//! - You want predictable, allocation-free behavior and can work with a fixed
//!   maximum length.
//!
//! It may not be the best fit if:
//!
//! - You need very large capacities or large element types.
//! - You frequently pass vectors by value (moving a `CopyStackVec` copies the
//!   entire `[T; N]` buffer, not just the initialized prefix).
//! - You don't want to constrain elements to `Copy`.
//!
//! See [`CopyStackVec`] for detailed semantics, complexity, and limitations.
//!
//! ## Backends and safety
//!
//! Two internal backends are selected by the `unsafe-maybe-uninit`
//! feature flag:
//!
//! - **Default backend (safe)**:
//!   - Storage is `[T; N]`.
//!   - The crate is `no_std` and `#![forbid(unsafe_code)]` (outside tests).
//!   - [`Default::default`] / [`CopyStackVec::new`] initialize all `N` elements
//!     with `T::default()`, which is `O(N)` and requires `T: Default`.
//!
//! - **`unsafe-maybe-uninit` backend**:
//!   - Storage is `[core::mem::MaybeUninit<T>; N]`.
//!   - A small amount of internal `unsafe` is used to treat only the
//!     `[0..len)` prefix as initialized.
//!   - [`Default::default`] / [`CopyStackVec::new`] avoid constructing `N`
//!     copies of `T` and no longer require `T: Default`. They still conceptually
//!     scale with the capacity `N`, but typically compile down to cheap bulk
//!     initialization of the `MaybeUninit` buffer.
//!
//! In both backends, the **public API is fully safe**. The feature only affects
//! internal representation and trait bounds on some constructors.
//!
//! ## Features
//!
//! - `serde`
//!   - Enables `Serialize` / `Deserialize` for `CopyStackVec<T, N>`.
//!   - In the safe backend: `T: Deserialize<'de> + Copy + Default`.
//!   - In the `unsafe-maybe-uninit` backend: `T: Deserialize<'de> + Copy`.
//!
//! - `unsafe-maybe-uninit`
//!   - Switches the internal storage to `[MaybeUninit<T>; N]`.
//!   - Relaxes some `T: Default` requirements (e.g. `Default` / `try_from_iter`).
//!   - Allows a small amount of internal `unsafe` to avoid touching the
//!     uninitialized tail.
//!
//! ## High-level semantics
//!
//! - Capacity is fixed at compile time (`CopyStackVec::<T, N>::CAPACITY == N`).
//! - Length is a logical prefix: only indices `< len` are considered initialized.
//! - No heap allocations are performed.
//! - Operations that may exceed capacity come in two flavors:
//!   - **Fallible**: return [`Error::Full`] on overflow and leave the
//!     vector unchanged (e.g. [`CopyStackVec::push`], [`CopyStackVec::extend_from_slice`],
//!     [`CopyStackVec::resize`], [`TryFrom<&[T]>`], [`CopyStackVec::try_from_iter`],
//!     [`CopyStackVec::try_extend_from_iter`], [`CopyStackVec::insert`],
//!     [`CopyStackVec::try_remove`], [`CopyStackVec::try_swap_remove`]).
//!   - **Truncating**: silently ignore extra elements (e.g.
//!     [`CopyStackVec::push_truncated`], [`CopyStackVec::extend_from_slice_truncated`],
//!     [`CopyStackVec::from_slice_truncated`], [`CopyStackVec::from_array_truncated`], [`FromIterator<T>`], and
//!     [`Extend<T>`]).
//!
//! ## Range and indexing behavior
//!
//! `CopyStackVec` intentionally follows Rust slice and `Vec` semantics for all
//! **indexing** and **range-based** operations:
//!
//! - Indexing (`v[i]`, `v[start..end]`, …) **panics** on out-of-bounds or
//!   inverted ranges, exactly like built-in slices.
//!
//! - [`CopyStackVec::drain`](CopyStackVec::drain) behaves like
//!   [`Vec::drain`](alloc::vec::Vec::drain):
//!     - `start > end` or `end > len()` → **panic**
//!     - `start == end` → empty iterator, no change
//!     - valid ranges remove the elements immediately and shift the tail left
//!
//! Only **range/index errors** panic.
//! Capacity-related failures never panic: they return [`Error::Full`] or
//! silently truncate (depending on the method, see above).
//!
//! Collecting into `CopyStackVec<T, N>` (via `FromIterator` / `collect`) takes at most the
//! first `N` elements from the iterator and stops there, leaving any remaining items
//! unconsumed.
//!
//! ## Example
//!
//! ```rust
//! use copy_stack_vec::CopyStackVec;
//!
//! let mut v: CopyStackVec<u8, 4> = CopyStackVec::default();
//! v.push(1).unwrap();
//! v.extend_from_slice(&[2, 3]).unwrap();
//! assert_eq!(v.as_slice(), &[1, 2, 3]);
//! ```
//!
//! See [`CopyStackVec`] for detailed behavior, including indexing semantics,
//! iterator behavior, and complexity notes.

#![cfg_attr(not(feature = "unsafe-maybe-uninit"), forbid(unsafe_code))]
#![cfg_attr(not(test), no_std)]

#[cfg(test)]
extern crate alloc;

// Modules
mod error;
mod index;
mod iter;
#[cfg(feature = "serde")]
mod serde;
mod vec;

// Public exports (crate API surface)
pub use error::Error;
pub use iter::IntoIter;
pub use vec::CopyStackVec;
