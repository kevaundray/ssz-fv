#![no_std]

//! Allocation-free SSZ operations over borrowed schemas and caller-owned arenas.
//!
//! Covers the pinned specification's scalar, byte/bit collection, vector/list,
//! container, progressive, and compatible-union families; codecs, JSON mapping,
//! defaults/compatibility, SHA-256 roots, generalized indices, and Merkle proofs.
//! Numeric metadata uses arbitrary-precision `Nat`, not host-sized capacities.
//!
//! Validate raw descriptors with `schema::validate` before value operations.
//! `descriptor::read_descriptor` parses declarations but does not validate them.
//! Arena storage is `MaybeUninit<u8>` and remains live and immutable wherever a
//! returned value borrows it. Serialization accepts uninitialized output and
//! initializes the returned prefix without touching its suffix.
//!
//! This implementation is distinct from the ISA-verified uint64 kernels. Native
//! compilation does not establish its machine-code refinement to the Lean model.

pub mod arena;
pub mod nat;
pub mod types;
pub mod schema;
pub mod codec;
pub mod hash;
pub mod merkle;

pub mod layout;
pub mod indices;
pub mod json;
pub mod descriptor;
pub mod proof;
pub mod verify;

pub use arena::Arena;
pub use nat::Nat;
pub use types::{Bits, ChunkPosition, Desc, Error, Field, Json, PathStep, Reason, Result, Spelling, Value, Variant};

#[cfg(test)]
extern crate std;
