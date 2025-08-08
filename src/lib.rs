//! `#![no_std]` bindings to Lua 5.4.

#![no_std]
#![allow(clippy::tabs_in_doc_comments)]

#[cfg(feature = "alloc")]
extern crate alloc;

#[cfg(any(doc, doctest))]
#[allow(rustdoc::redundant_explicit_links)]
#[doc = include_str!("../doc/errors.md")]
pub mod errors {}

#[cfg(feature = "auxlib")]
mod aux_options;
#[cfg(feature = "auxlib")]
pub use aux_options::*;
mod coroutine;
pub use coroutine::*;
pub mod cdef;
mod dbg_what;
pub use dbg_what::*;
mod gc_mode;
pub use gc_mode::*;
mod managed;
pub use managed::*;
pub mod prelude;
#[cfg(feature = "auxlib")]
mod reg;
#[cfg(feature = "auxlib")]
pub use reg::*;
mod state;
pub use state::*;
mod thread;
pub use thread::*;

mod macros;
