//! See [`Library`].
 
use crate::cdef::{
	auxlib::luaL_Reg,
	lua_CFunction,
};

use core::{
	ffi::CStr,
	marker::PhantomData,
	ptr::null,
	slice::from_raw_parts,
};

/// List of registered C functions to be used with
/// [`Managed::new_lib`](crate::Managed::new_lib).
/// 
/// The generic `const N: usize` specifies the static number of entries;
/// `'name` indicates the lifetime for every key, which are C strings.
#[derive(Debug, Clone, Copy)]
#[repr(C)]
pub struct Library<'name, const N: usize> {
	pub regs: [luaL_Reg; N],
	terminator: luaL_Reg,
	_life: PhantomData<&'name CStr>
}

impl<'name, const N: usize> Library<'name, N> {
	/// Construct an instance of [`Library`] with a static list of functions.
	pub const fn new(items: [(&'name CStr, Option<lua_CFunction>); N]) -> Self {
		let mut regs = [luaL_Reg::NULL; N];

		let mut i = 0;
		while i < N {
			regs[i] = luaL_Reg {
				name: items[i].0.as_ptr(),
				func: items[i].1
			};
			i += 1;
		}

		Self {
			regs,
			terminator: luaL_Reg {
				name: null(),
				func: None
			},
			_life: PhantomData,
		}
	}

	/// Return the number of registrations.
	pub const fn size() -> usize {
		N
	}

	/// Return the number of registrations in `self`.
	pub const fn len(&self) -> usize {
		N
	}

	/// Return `true` if there are no registrations.
	pub const fn is_empty(&self) -> bool {
		N == 0
	}

	/// Return a pointer to this structure to be used with C.
	pub const fn as_ptr(&self) -> *const luaL_Reg {
		self.regs.as_ptr()
	}

	/// Return a terminated slice of [`luaL_Reg`]s that represent the registered functions.
	pub const fn as_terminated_slice(&self) -> &[luaL_Reg] {
		unsafe { from_raw_parts(self.as_ptr(), N + 1) }
	}
}
