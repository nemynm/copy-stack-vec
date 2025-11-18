// Invariants for the `unsafe-maybe-uninit` backend:
// - `0 <= len <= N` always holds.
// - Elements in `buf[..len]` are initialized `T` values.
// - Elements in `buf[len..N]` are logically uninitialized and must never be
//   read as `T`.
// - All public methods maintain these invariants.

mod as_ptr;
mod default;
mod drain;
mod extend;
mod from;
mod insert;
mod into_array;
mod new;
mod pop;
mod push;
mod remove;
mod retain;
mod slice;
mod split_off;
mod try_from;
mod try_from_iter;
