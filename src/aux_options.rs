//! See [`AuxOptions`].

use core::ffi::{
	CStr,
	c_char
};
use core::marker::PhantomData;
use core::mem::{
	transmute, MaybeUninit
};
use core::ptr::null;
use core::slice::from_raw_parts;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
#[repr(C)]
pub struct AuxOptions<'str, const N: usize> {
	pub options: [*const c_char; N],
	terminator: *const c_char,
	_life: PhantomData<&'str CStr>
}

impl<'str, const N: usize> AuxOptions<'str, N> {
	pub const fn new(items: [&'str CStr; N]) -> Self {
		// SAFETY: We make an uninit `[Reg; N]`, but then immediately fill it
		// with stuff without reading from it.
		let regs: [*const c_char; N] = unsafe {
			let mut dest: [*const c_char; N] = MaybeUninit::uninit().assume_init();
	
			let mut i = 0;
			while i < N {
				dest[i] = items[i].as_ptr();
				i += 1;
			}

			dest
		};

		Self {
			options: regs,
			terminator: null(),
			_life: PhantomData
		}
	}

	pub const fn count() -> usize {
		N
	}

	pub const fn as_ptr(&self) -> *const *const c_char {
		unsafe { transmute(self as *const _) }
	}

	pub const fn as_str_ptr_slice(&self) -> &[*const c_char] {
		unsafe { from_raw_parts(
			transmute(self as *const _ as *const c_char), N + 1
		) }
	}
}
