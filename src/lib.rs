//! Low-level, `#![no_std]` definitions for Lua 5.4.

#![no_std]

pub mod ffi;

pub use ffi::{
	REGISTRY_INDEX,
	Number,
	Integer,
	ThreadStatus,
	Unsigned,
	upvalue_index
};
