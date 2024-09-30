//! See [`AuxOptions`].

use core::{
	ffi::{
		CStr,
		c_char
	},
	marker::PhantomData,
	mem::{
		transmute, MaybeUninit
	},
	ptr::null,
	slice::from_raw_parts,
};

/// List of string options to be used with
/// [`Thread::check_option`](crate::Thread::check_option).
/// 
/// The generic `const N: usize` specifies the static number of entries;
/// `'str` indicates the lifetime for every entry, which are C strings.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
#[repr(C)]
pub struct AuxOptions<'str, const N: usize> {
	pub options: [*const c_char; N],
	terminator: *const c_char,
	_life: PhantomData<&'str CStr>
}

impl<'str, const N: usize> AuxOptions<'str, N> {
	/// Construct an instance of [`AuxOptions`] with a static list of options.
	pub const fn new(items: [&'str CStr; N]) -> Self {
		// SAFETY: We make an uninit `[*const c_char; N]`, but then immediately
		// fill it with stuff without reading from it.
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

	/// Return the number of options that this list has.
	pub const fn count() -> usize {
		N
	}

	/// Return a pointer to this structure to be used with C.
	pub const fn as_ptr(&self) -> *const *const c_char {
		unsafe { transmute(self as *const _) }
	}

	/// Return a slice of [`*const c_char`](c_char)s that represent the string
	/// options contained within the structure.
	pub const fn as_str_ptr_slice(&self) -> &[*const c_char] {
		unsafe { from_raw_parts(
			transmute(self as *const _ as *const c_char), N + 1
		) }
	}
}
