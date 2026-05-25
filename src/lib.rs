//! `#![no_std]` bindings to Lua 5.4.

#![no_std]
#![allow(clippy::tabs_in_doc_comments)]

#[cfg(feature = "alloc")]
extern crate alloc;

#[cfg(any(doc, doctest))]
#[allow(rustdoc::redundant_explicit_links)]
#[doc = include_str!("../doc/errors.md")]
pub mod errors {}

pub mod cdef;

#[cfg(feature = "auxlib")]
mod auxlib;
pub use auxlib::*;

mod coroutine;
pub use coroutine::*;
mod dbg_what;
pub use dbg_what::*;
mod gc_mode;
pub use gc_mode::*;
mod indices;
pub use indices::*;
mod managed;
pub use managed::*;
pub mod prelude;
mod state;
pub use state::*;
mod thread;
pub use thread::*;

mod macros;
