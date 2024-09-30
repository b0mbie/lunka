//! See [`Library`].
 
use crate::auxlib::Reg;
use crate::cdef::CFunction;

use core::{
	ffi::CStr,
	marker::PhantomData,
	mem::{
		transmute, MaybeUninit
	},
	ptr::null,
	slice::from_raw_parts,
};

/// List of registered C functions to be used with
/// [`Thread::new_lib`](crate::Thread::new_lib).
/// 
/// The generic `const N: usize` specifies the static number of entries;
/// `'name` indicates the lifetime for every key, which are C strings.
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

	/// Return the number of functions registered.
	#[inline(always)]
	pub const fn n_regs() -> usize {
		N
	}

	/// Return the number of functions registered, plus `1`.
	#[inline(always)]
	pub const fn n_regs_1() -> usize {
		N + 1
	}

	/// Return the number of functions registered for this set of functions.
	#[inline(always)]
	pub const fn len(&self) -> usize {
		Self::n_regs()
	}

	/// Return a pointer to this structure to be used with C.
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
