//! `#![no_std]` bindings to Lua 5.4.

#![no_std]

// Important notes:
// - Upvalues are presented as `int`s, however Lua uses them in `lu_byte`s.
// - Uservalue indices are presented as `int`s, however Lua uses them in
// `unsigned short`s.

use allocator_api2::alloc::{
	AllocError, Allocator, Global
};
use core::alloc::Layout;
use core::ffi::{
	c_int, c_void, CStr
};
use core::marker::PhantomData;
use core::mem::align_of;
use core::ops::{
	Deref, DerefMut
};
use core::ptr::{
	null_mut, NonNull
};

#[cfg(any(doc, doctest))]
#[cfg_attr(any(doc, doctest), doc = include_str!("../doc/errors.md"))]
pub mod errors {}

#[cfg(feature = "auxlib")]
pub mod aux_options;
pub mod cdef;
pub mod dbg_what;
pub mod managed;
pub use managed::*;
pub mod prelude;
#[cfg(feature = "auxlib")]
pub mod reg;
pub mod thread;
pub use thread::*;

use cdef::*;

#[cfg(feature = "auxlib")]
use auxlib::*;

/// Lua garbage collection mode setup information.
/// 
/// This structure is used for [`Thread::switch_gc_to`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum GcMode {
	Incremental {
		/// How long the collector should wait before starting a new cycle.
		/// Default is `200`, maximum is `1000`
		/// 
		/// The collector starts a new cycle when the use of memory hits `pause`%
		/// of the use after the previous collection.
		/// Larger values make the collector less aggressive.
		/// 
		/// Values equal to or less than `100` mean the collector will not wait
		/// to start a new cycle.
		/// A value of `200` means that the collector waits for the total memory
		/// in use to double before starting a new cycle.
		pause: u16,
		/// Speed of the collector relative to memory allocation; that is,
		/// how many elements it marks or sweeps for each kilobyte of memory
		/// allocated.
		/// Default is `100`, maximum is `1000`.
		/// 
		/// Larger values make the collector more aggressive but also increase
		/// the size of each incremental step.
		/// 
		/// You should not use values less than `100`, because they make the
		/// collector too slow and can result in the collector never finishing a
		/// cycle.
		step_multiplier: u16,
		/// Size of each incremental step, specifically how many bytes the
		/// interpreter allocates before performing a step.
		/// Default is `13` (steps of approximately `8` kilobytes).
		/// 
		/// This parameter is logarithmic: A value of `step_size` means the
		/// interpreter will allocate `2 ^ step_size` bytes between steps and
		/// perform equivalent work during the step.
		/// 
		/// A large value (e.g., `60`) makes the collector a stop-the-world
		/// (non-incremental) collector.
		step_size: c_int
	},
	Generational {
		/// Frequency of minor collections.
		/// Default is `20`, maximum is `200`.
		/// 
		/// For a minor multiplier `minor_mul`, a new minor collection will be
		/// done when memory grows `minor_mul`% larger than the memory in use
		/// after the previous major collection.
		/// 
		/// For instance, for a multiplier of `20`, the collector will do a
		/// minor collection when the use of memory gets `20%` larger than the
		/// use after the previous major collection.
		minor_mul: u8,
		/// Frequency of major collections.
		/// Default is `100`, maximum is `1000`.
		/// 
		/// For a major multiplier `major_mul`, a new major collection will be
		/// done when memory grows `major_mul`% larger than the memory in use
		/// after the previous major collection.
		/// 
		/// For instance, for a multiplier of `100`, the collector will do a
		/// major collection when the use of memory gets larger than twice the
		/// use after the previous collection.
		major_mul: u16
	}
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
	panic!("unprotected error in call to Lua API ({msg})")
}

/// Data structure that represents a main Lua thread.
/// 
/// Unlike [`Coroutine`], this data structure has a [`Drop`] implementation that
/// automatically closes (frees) the Lua state.
/// 
/// # Layout
/// [`Lua`] is guaranteed to have the same layout as [`Thread`].
#[derive(Debug)]
#[repr(transparent)]
pub struct Lua<const ID_SIZE: usize = DEFAULT_ID_SIZE> {
	thread: Thread<ID_SIZE>
}

impl<const ID_SIZE: usize> Drop for Lua<ID_SIZE> {
	fn drop(&mut self) {
		unsafe { self.thread.close_as_main() }
	}
}

impl<const ID_SIZE: usize> Deref for Lua<ID_SIZE> {
	type Target = Thread<ID_SIZE>;
	fn deref(&self) -> &Self::Target {
		&self.thread
	}
}

impl<const ID_SIZE: usize> DerefMut for Lua<ID_SIZE> {
	fn deref_mut(&mut self) -> &mut Self::Target {
		&mut self.thread
	}
}

#[cfg(feature = "auxlib")]
impl Lua<DEFAULT_ID_SIZE> {
	/// Potentially construct a new [`Lua`] with the default `ID_SIZE` of
	/// [`DEFAULT_ID_SIZE`], using the `lauxlib` function [`luaL_newstate`].
	/// 
	/// The function will return `None` if allocation failed.
	pub fn new_auxlib() -> Option<Self> {
		Self::new_auxlib_with()
	}

	/// Potentially Construct a new [`Lua`] with the default `ID_SIZE` of
	/// [`DEFAULT_ID_SIZE`], using the [`Global`] Rust allocator.
	/// 
	/// The function will return `None` if allocation failed.
	pub fn new() -> Option<Self> {
		Self::new_with()
	}
}

impl<const ID_SIZE: usize> Lua<ID_SIZE> {
	#[inline(always)]
	unsafe fn from_l(l: *mut State) -> Option<Self> {
		if !l.is_null() {
			let lua = Self {
				thread: unsafe { Thread::from_ptr(l) }
			};
			lua.stop_gc();
			Some(lua)
		} else {
			None
		}
	}

	/// Construct a new [`Lua`] using the `lauxlib` function [`luaL_newstate`].
	/// 
	/// The function will return `None` if allocation failed.
	#[cfg(feature = "auxlib")]
	#[inline(always)]
	pub fn new_auxlib_with() -> Option<Self> {
		unsafe { Self::from_l(luaL_newstate()) }
	}

	/// Construct a new [`Lua`] using an allocation function (see [`Alloc`]).
	/// 
	/// The function will return `None` if allocation failed.
	#[inline(always)]
	pub fn new_with_alloc_fn(
		alloc_fn: Alloc, alloc_fn_data: *mut c_void
	) -> Option<Self> {
		unsafe { Self::from_l(lua_newstate(alloc_fn, alloc_fn_data)) }
	}

	/// Construct a new [`Lua`] using the [`Global`] Rust allocator.
	/// 
	/// The function will return `None` if allocation failed.
	#[inline(always)]
	pub fn new_with() -> Option<Self> {
		// TODO: Is this right for emulating `malloc`?
		unsafe extern "C" fn l_alloc(
			_ud: *mut c_void,
			ptr: *mut c_void, osize: usize,
			nsize: usize
		) -> *mut c_void {
			if let Some(alloc_ptr) = NonNull::new(ptr as *mut u8) {
				if nsize <= 0 {
					Global.deallocate(
						alloc_ptr,
						Layout::from_size_align_unchecked(
							osize, align_of::<usize>()
						)
					);
					null_mut()
				} else {
					let old_layout = Layout::from_size_align_unchecked(
						osize, align_of::<usize>()
					);
					let new_layout = Layout::from_size_align_unchecked(
						nsize, align_of::<usize>()
					);
	
					if nsize > osize {
						Global.grow(alloc_ptr, old_layout, new_layout)
							.map(|mut ptr| {
								ptr.as_mut().as_mut_ptr() as *mut c_void
							})
							.unwrap_or(null_mut())
					} else if nsize < osize {
						Global.shrink(alloc_ptr, old_layout, new_layout)
							.map(|mut ptr| {
								ptr.as_mut().as_mut_ptr() as *mut c_void
							})
							.unwrap_or(null_mut())
					} else {
						ptr
					}
				}
			} else {
				debug_assert!(nsize > 0);
				Global.allocate(Layout::from_size_align_unchecked(
					nsize, align_of::<usize>()
				))
					.map(|ptr| (*ptr.as_ptr()).as_mut_ptr() as *mut c_void)
					.unwrap_or(null_mut())
			}
		}

		unsafe { Self::from_l(lua_newstate(l_alloc, null_mut())) }
	}

	/// Construct a new [`Lua`] using an already-allocated Lua state, and set
	/// its panic function to [`lua_panic`].
	/// 
	/// # Safety
	/// `l` must be a valid pointer to a Lua state.
	#[inline(always)]
	pub unsafe fn from_ptr(l: *mut State) -> Self {
		let thread = Thread::from_ptr(l);
		thread.at_panic(Some(lua_panic));
		Self {
			thread
		}
	}

	/// Return the raw pointer to the underlying Lua state.
	#[inline(always)]
	pub const fn as_ptr(&self) -> *mut State {
		self.thread.as_ptr()
	}
}

unsafe impl<const ID_SIZE: usize> Allocator for Lua<ID_SIZE> {
	fn allocate(&self, layout: Layout) -> Result<NonNull<[u8]>, AllocError> {
		let (alloc, ud) = self.get_alloc_fn();
		let len = layout.size();
		NonNull::new(unsafe { alloc(ud, null_mut(), 0, len) } as *mut u8)
			.map(|ptr| NonNull::slice_from_raw_parts(ptr, len))
			.ok_or(AllocError)
	}

	unsafe fn deallocate(&self, ptr: NonNull<u8>, layout: Layout) {
		let (alloc, ud) = self.get_alloc_fn();
		unsafe { alloc(ud, ptr.as_ptr() as *mut c_void, layout.size(), 0) };
	}
}

/// Data structure that represents a Lua coroutine.
/// 
/// See also [`Lua`] for the main thread.
/// 
/// This type does not have a [`Drop`] implementation.
/// Any threads that are not used anymore must either be closed manually with
/// [`Coroutine::close`] or left to be garbage-collected by Lua.
/// 
/// # Layout
/// [`Coroutine`] is guaranteed to have the same layout as [`Thread`].
#[derive(Debug)]
#[repr(transparent)]
pub struct Coroutine<'l, const ID_SIZE: usize = DEFAULT_ID_SIZE> {
	thread: Thread<ID_SIZE>,
	_life: PhantomData<&'l Lua<ID_SIZE>>
}

impl<'l, const ID_SIZE: usize> Coroutine<'l, ID_SIZE> {
	/// Alias to [`Thread::close_as_coroutine`].
	pub fn close(&mut self) -> Status {
		self.thread.close_as_coroutine()
	}

	/// Alias to [`Thread::close_as_coroutine_from`].
	pub fn close_from(&mut self, from: &Self) -> Status {
		self.thread.close_as_coroutine_from(&from.thread)
	}
}

/// Push a formatted string with [`lua_pushfstring`].
/// 
/// The "signature" for this function is
/// `lua_push_fmt_string!(lua: &Thread, fmt: <string>, ...)`, where `fmt` is a
/// literal format string, and `...` are the format arguments.
/// 
/// It is similar to the ISO C function `sprintf`, however you do not have to
/// allocate space for the result; the result is a Lua string and Lua takes care
/// of memory allocation (and deallocation, through garbage collection).
/// 
///	# Conversion specifiers
/// There are no flags, widths, or precisions.
/// The conversion specifiers can only be:
/// - `%%` - insert the character `%`.
/// - `%s` - insert a zero-terminated string using
/// [`*const c_char`](core::ffi::c_char), with no size restrictions.
/// - `%f` - insert a [`Number`].
/// - `%I` - insert an [`Integer`].
/// - `%p` - insert a *thin* pointer, like [`*mut c_void`](c_void).
/// - `%d` - insert a [`c_int`].
/// - `%c` - insert a [`c_int`] as a one-byte character.
/// - `%U` - insert a [`c_long`](core::ffi::c_long) as a UTF-8 byte sequence.
/// 
/// # Safety
/// The macro uses an unsafe function, and is itself unsafe to use; there have
/// to be sufficient format arguments, and they must be of the correct type.
#[macro_export]
macro_rules! lua_push_fmt_string {
	($lua:expr, $fmt:literal $(, $fmt_arg:expr)*) => {{
		let lua: &$crate::Thread = &$lua;
		$crate::cdef::lua_pushfstring(
			lua.as_ptr(),
			core::ffi::CStr::from_bytes_with_nul_unchecked(
				concat!($fmt, "\0").as_bytes()
			).as_ptr()
			$(, $fmt_arg)*
		)
	}};
}

/// Raise a formatted error with [`luaL_error`].
/// 
/// The "signature" for this function is
/// `lua_fmt_error!(lua: &Thread, fmt: <string>, ...)`, where `fmt` is a
/// literal format string, and `...` are the format arguments.
/// 
/// This function follows the same rules as [`lua_push_fmt_string!`].
/// 
/// # Safety
/// The macro uses an unsafe function, and is itself unsafe to use; there have
/// to be sufficient format arguments, and they must be of the correct type.
#[macro_export]
macro_rules! lua_fmt_error {
	($lua:expr, $fmt:literal $(, $fmt_arg:expr)*) => {{
		let lua: &$crate::Thread = &$lua;
		$crate::cdef::auxlib::luaL_error(
			lua.as_ptr(),
			core::ffi::CStr::from_bytes_with_nul_unchecked(
				concat!($fmt, "\0").as_bytes()
			).as_ptr()
			$(, $fmt_arg)*
		)
	}};
}

/// Create a [`Library`](crate::reg::Library) with a more understandable syntax.
/// 
/// The macro accepts a `struct` construction-like syntax, to construct an
/// instance from a static array of pairs of [`CStr`] and
/// [`Option<CFunction>`](CFunction), where a field with a value creates a pair
/// `("name", Some(func_name))`, and a field with no value specified creates a
/// pair `("name", None)`.
/// 
/// # Examples
/// ```
/// use lunka::prelude::*;
/// 
/// unsafe extern "C" fn l_get_pi(l: *mut LuaState) -> core::ffi::c_int {
/// 	let lua: LuaThread = LuaThread::from_ptr(l);
/// 	lua.push_number(3.14);
/// 	1
/// }
/// 
/// // This will create a `LuaLibrary` that, when used with `Thread::set_funcs`,
/// // will set a table's field `get_pi` to the `l_get_pi` function, and `set_pi`
/// // to `false`.
/// let library = lua_library! {
/// 	get_pi: l_get_pi,
/// 	set_pi
/// };
/// ```
#[cfg(feature = "auxlib")]
#[macro_export]
macro_rules! lua_library {
	{$(
		$field:ident $(: $fn_name:ident)?
	),*} => {
		$crate::reg::Library::new([
			$(lua_library!(@field $field $($fn_name)?)),*
		])
	};

	(@field $field:ident $fn_name:ident) => {
		(unsafe { core::ffi::CStr::from_bytes_with_nul_unchecked(
			concat!(stringify!($field), "\0").as_bytes()
		) }, Some($fn_name))
	};

	(@field $field:ident) => {
		(unsafe { core::ffi::CStr::from_bytes_with_nul_unchecked(
			concat!(stringify!($field), "\0").as_bytes()
		) }, None)
	};
}
