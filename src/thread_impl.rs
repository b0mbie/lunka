//! See [`ThreadImpl`].

use super::cdef::*;
use core::ffi::{
	CStr,
	c_int,
	c_uint
};
use core::ptr::null_mut;

/// Lua garbage collection modes enum.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Gc {
	Incremental {
		pause: c_int,
		step_multiplier: c_int,
		step_size: c_int
	},
	Generational {
		minor_mul: c_int,
		major_mul: c_int
	}
}

/// Lua thread wrapper that's used by [`MainThread`](super::MainThread) and
/// friends.
#[derive(Debug)]
#[repr(transparent)]
pub struct ThreadImpl<const ID_SIZE: usize> {
	l: *mut State
}

/// Panic function that's similar to the panic function defined in `lauxlib.h`.
pub unsafe extern "C" fn lua_panic(l: *mut State) -> c_int {
	let msg = {
		let msg_str = lua_tostring(l, -1);
		if msg_str.is_null() {
			CStr::from_bytes_with_nul_unchecked(
				b"error object is not a string\0"
			)
		} else {
			CStr::from_ptr(msg_str)
		}
	};

	let msg = msg.to_str().unwrap_or("error object does not contain valid UTF-8");
	panic!("{}", msg)
}

impl<const ID_SIZE: usize> ThreadImpl<ID_SIZE> {
	pub const unsafe fn from_ptr(l: *mut State) -> Self {
		Self {
			l
		}
	}

	pub const fn as_ptr(&self) -> *mut State {
		self.l
	}

	pub fn at_panic(
		&mut self, func: Option<CFunction>
	) -> Option<CFunction> {
		unsafe { lua_atpanic(self.l, func) }
	}

	pub fn version(&self) -> Number {
		unsafe { lua_version(self.l) }
	}

	pub unsafe fn close_as_main(&mut self) {
		let l = self.l;
		self.l = null_mut();
		lua_close(l)
	}

	pub unsafe fn close_as_coroutine(&mut self) -> ThreadStatus {
		let l = self.l;
		self.l = null_mut();
		ThreadStatus::from_c_int_unchecked(lua_resetthread(l))
	}

	pub fn stop_gc(&mut self) {
		unsafe { lua_gc(self.l, GcTask::Stop as _) };
	}

	pub fn restart_gc(&mut self) {
		unsafe { lua_gc(self.l, GcTask::Restart as _) };
	}

	pub fn perform_gc_cycle(&mut self) {
		unsafe { lua_gc(self.l, GcTask::Collect as _) };
	}

	pub fn mem_kbytes(&mut self) -> c_uint {
		unsafe { lua_gc(self.l, GcTask::CountKbytes as _) }
			.clamp(0, c_int::MAX) as _
	}

	pub fn mem_byte_remainder(&mut self) -> c_uint {
		unsafe { lua_gc(self.l, GcTask::CountBytesRem as _) }
			.clamp(0, c_int::MAX) as _
	}

	pub fn step_gc(&mut self, step_size: c_uint) {
		unsafe { lua_gc(self.l, GcTask::Step as _, step_size) };
	}

	pub fn is_gc_running(&self) -> bool {
		(unsafe { lua_gc(self.l, GcTask::IsRunning as _) }) != 0
	}

	pub fn switch_gc_to(&mut self, gc: Gc) {
		match gc {
			Gc::Incremental { pause, step_multiplier, step_size } => unsafe {
				lua_gc(
					self.l, GcTask::ToIncremental as _,
					pause, step_multiplier, step_size
				)
			},
			Gc::Generational { minor_mul, major_mul } => unsafe {
				lua_gc(self.l, GcTask::ToGenerational as _, minor_mul, major_mul)
			}
		};
	}
}
