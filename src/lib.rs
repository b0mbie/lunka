//! Low-level, `#![no_std]` definitions for Lua 5.4.

#![no_std]

pub mod cdef;

pub use cdef::{
	REGISTRY_INDEX,
	Event,
	HookMask,
	Number,
	Integer,
	Unsigned,
	upvalue_index
};
