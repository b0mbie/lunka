//! # lunka
//! `#![no_std]` bindings to Lua 5.4.

#![no_std]

mod thread_impl;
use core::ops::{
	Deref, DerefMut
};

use thread_impl::*;
pub use thread_impl::Gc;

pub mod cdef;
pub use cdef::{
	Number,
	Integer,
	upvalue_index
};

#[derive(Debug)]
#[repr(transparent)]
pub struct MainThread<const ID_SIZE: usize = { cdef::DEFAULT_ID_SIZE }> {
	thread: ThreadImpl<ID_SIZE>
}

impl<const ID_SIZE: usize> Deref for MainThread<ID_SIZE> {
	type Target = ThreadImpl<ID_SIZE>;
	fn deref(&self) -> &Self::Target {
		&self.thread
	}
}

impl<const ID_SIZE: usize> DerefMut for MainThread<ID_SIZE> {
	fn deref_mut(&mut self) -> &mut Self::Target {
		&mut self.thread
	}
}

impl<const ID_SIZE: usize> Drop for MainThread<ID_SIZE> {
	fn drop(&mut self) {
		unsafe { self.thread.close_as_main() }
	}
}

impl<const ID_SIZE: usize> MainThread<ID_SIZE> {
	pub unsafe fn from_ptr(l: *mut cdef::State) -> Self {
		let mut thread = ThreadImpl::from_ptr(l);
		thread.at_panic(Some(lua_panic));
		thread.stop_gc();
		Self {
			thread
		}
	}

	pub const fn as_ptr(&self) -> *mut cdef::State {
		self.thread.as_ptr()
	}

	pub fn version(&self) -> Number {
		self.thread.version()
	}
}
