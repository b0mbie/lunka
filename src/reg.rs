//! See [`Library`].
 
use crate::auxlib::Reg;
use crate::cdef::CFunction;

use core::ffi::CStr;
use core::marker::PhantomData;
use core::mem::{
	transmute, MaybeUninit
};
use core::ptr::null;
use core::slice::from_raw_parts;

/// List of registered C functions to be used with
/// [`Thread::new_lib`](crate::Thread::new_lib).
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
#[repr(C)]
pub struct Library<'name, const N: usize> {
	pub regs: [Reg; N],
	terminator: Reg,
	_life: PhantomData<&'name CStr>
}

impl<'name, const N: usize> Library<'name, N> {
	/// Construct an instance of [`Library`] with a static list of functions.
	pub const fn new(
		items: [(&'name CStr, Option<CFunction>); N]
	) -> Self {
		// SAFETY: We make an uninit `[Reg; N]`, but then immediately fill it
		// with stuff without reading from it.
		let regs: [Reg; N] = unsafe {
			let mut dest: [Reg; N] = MaybeUninit::uninit().assume_init();
	
			let mut i = 0;
			while i < N {
				dest[i] = Reg {
					name: items[i].0.as_ptr(),
					func: items[i].1
				};
				i += 1;
			}

			dest
		};

		Self {
			regs,
			terminator: Reg {
				name: null(),
				func: None
			},
			_life: PhantomData
		}
	}

	/// Return the number of functions registered, plus `1`.
	pub const fn ffi_len() -> usize {
		N + 1
	}

	/// Return a pointer to this structure to be used with FFI.
	pub const fn as_ptr(&self) -> *const Reg {
		unsafe { transmute(self as *const _) }
	}

	/// Return a slice of [`Reg`]s that represent the registered functions.
	pub const fn as_reg_slice(&self) -> &[Reg] {
		unsafe { from_raw_parts(
			transmute(self as *const _ as *const Reg), N + 1
		) }
	}
}
