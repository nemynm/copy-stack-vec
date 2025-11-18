# copy-stack-vec

A `no_std`, fixed-capacity, stack-allocated vector type for `Copy` elements, **with no unsafe code by default**.

`CopyStackVec<T, N>` stores up to `N` elements inline and provides familiar slice/Vec-like ergonomics without heap
allocation or runtime growth. In the default backend, many constructors require `T: Copy + Default`,
while some helpers (like `new_with` and `From<[T; N]>`) only need `T: Copy`. With the
`unsafe-maybe-uninit` backend, only `T: Copy` is required.

- `no_std` compatible.
- no internal `unsafe` in the default backend (`#![forbid(unsafe_code)]`).
- stack-allocated, fixed capacity (`N` known at compile time).
- the container itself is `Copy` (value semantics; moving copies the whole buffer).
- optional `unsafe-maybe-uninit` backend.
- separation between **fallible** and **truncating** operations.
- optional `serde` support.

## Using copy-stack-vec

Add the crate to your project
```
cargo add copy-stack-vec
```

## Example

```rust
use copy_stack_vec::CopyStackVec;

let mut v: CopyStackVec<u8, 4> = CopyStackVec::default();
v.extend_from_slice(&[1, 2, 3]).unwrap();
assert_eq!(v.as_slice(), &[1, 2, 3]);

let mut w: CopyStackVec<u8, 4> = CopyStackVec::default();
w.push(1).unwrap();
w.extend_from_slice(&[2, 3]).unwrap();
assert_eq!(w.as_slice(), &[1, 2, 3]);
```

## Crate usage

The `copy-stack-vec` crate can be a good fit when:

- you need a small fixed-capacity buffer on the stack;
- you prefer value semantics (the container itself is `Copy`) and your element type is `Copy`;
- you want a crate that defaults to no unsafe code;
- you want deterministic, heap-allocation-free behavior.


It may not be the best tool if:

- you need large capacities or large element types;
- you frequently move the vector by value (moving copies the entire [T; N] buffer);
- you need non-Copy elements or drop semantics;
- you need dynamically growing capacity.

## Alternatives

Well-established alternatives exist already (`arrayvec`, `heapless`, `smallvec`, or `tinyvec` to name a few).
`copy-stack-vec` is a focused option built around **value semantics** (the container itself is `Copy`) and
**safe-by-default internals** for `Copy` element types.

## Backends

### Default backend (safe)

- storage is `[T; N]`.
- requires `T: Copy + Default` for most constructors that build a fresh buffer [1]
- all internal code is safe (`#![forbid(unsafe_code)]`).
- initialization cost is `O(N)` when constructing a new vector (eager initialization).

[1] some helpers like `CopyStackVec::new_with` and `From<[T; N]>` only require `T: Copy`. See method documentation.

### `unsafe-maybe-uninit` backend (optional)

- storage is `[MaybeUninit<T>; N]`
- only requires `T: Copy`
- avoids eager initialization of all `N` elements
- uses minimal, well-scoped internal `unsafe`


## Range and indexing behavior

`CopyStackVec` follows Rust slice and `Vec` semantics for **indexing** and **range-based** operations:

- Indexing (`v[i]`, `v[start..end]`, etc.) **panics** on out-of-bounds
  or inverted ranges - just like slices.
- `drain(range)` behaves the same as `Vec::drain(range)`:
    - `start > end` or `end > len()`-> **panic**
    - `start == end` -> empty iterator, no changes
    - valid ranges remove the elements immediately and shift the tail left

Capacity errors never panic; only range / indexing violations do.

## Fallible vs truncating operations

The API explicitly distinguishes two behaviors for capacity-sensitive operations.

### Fallible (error if it doesn't fit; no partial writes)

- `push`
- `extend_from_slice`
- `resize`
- `try_from`
- `insert`
- `try_from_iter`
- `try_remove`
- `try_swap_remove`

### Truncating (take as much as fits; ignore the rest)

These take up to capacity and do not consume further items once the vector is full:
- `push_truncated`
- `extend_from_slice_truncated`
- `from_slice_truncated`
- `from_array_truncated`
- `Extend<T>`
- `FromIterator<T>`

Note: unlike `Vec`, collecting into `CopyStackVec` (via `FromIterator` / `collect::<CopyStackVec<_, N>>()`)
takes at most the first `N` elements from the iterator and stops there, leaving the remaining items unconsumed.

## Features

- `serde` - enable `Serialize` / `Deserialize`
- `unsafe-maybe-uninit` - switch to the `MaybeUninit` backend and relax `T: Default` requirements

## Minimum Supported Rust Version (MSRV)

This crate is tested on and supports Rust **1.85** and newer.

MSRV policy:

- The MSRV will not be increased in a patch release.
- The MSRV may be increased in a minor release (e.g. `0.3.x` -> `0.4.0`).

## License

MIT OR Apache-2.0