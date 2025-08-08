//! FFI definitions for `lauxlib.h`.

#![allow(non_snake_case)]

use super::*;

use core::{
	ffi::CStr,
	fmt,
	marker::PhantomData,
	mem::{
		MaybeUninit, size_of,
	},
	ptr::{
		null, null_mut,
	},
	slice::{
		from_raw_parts, from_raw_parts_mut,
	},
};

/// Global table name.
/// 
/// This cannot be changed for Lua that's already compiled.
pub const GLOBAL_TABLE: &CStr = c"_G";

/// Key, in the registry, for the table of loaded modules.
/// 
/// This cannot be changed for Lua that's already compiled.
pub const LOADED_TABLE: &CStr = c"_LOADED";

/// Key, in the registry, for the table of preloaded loaders.
/// 
/// This cannot be changed for Lua that's already compiled.
pub const PRELOAD_TABLE: &CStr = c"_PRELOAD";

/// Type for arrays of functions to be registered by [`luaL_setfuncs`].
/// Also known as `luaL_Reg`.
/// 
/// [`Reg::name`] is the function name and [`Reg::func`] is a pointer to the
/// function.
/// 
/// Any array of [`Reg`] must end with a sentinel entry in which both `name` and
/// `func` are null.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
#[repr(C)]
pub struct Reg {
	pub name: *const c_char,
	pub func: Option<CFunction>
}

/// Packed combination [`Integer`] and [`Number`] type sizes for
/// [`luaL_checkversion_`] to check against.
pub const NUM_SIZES: usize = size_of::<Integer>() * 16 + size_of::<Number>();

/// Constant that is guaranteed to indicate no reference.
pub const NO_REF: c_int = -2;

/// Constant that indicates a reference to `nil`.
pub const REF_NIL: c_int = -1;

#[cfg_attr(all(feature = "link-system", feature = "link-dynamic", target_os = "windows"), link(name = "lua54", kind = "raw-dylib"))]
#[cfg_attr(all(feature = "link-system", feature = "link-dynamic", not(target_os = "windows")), link(name = "lua5.4", kind = "dylib"))]
#[cfg_attr(all(feature = "link-system", not(feature = "link-dynamic"), target_os = "windows"), link(name = "lua54", kind = "static"))]
#[cfg_attr(all(feature = "link-system", not(feature = "link-dynamic"), not(target_os = "windows")), link(name = "lua5.4", kind = "static"))]
unsafe extern "C-unwind" {
	pub fn luaL_newstate() -> *mut State;

	pub fn luaL_prepbuffsize(buffer: *mut Buffer, size: usize) -> *mut c_char;
	pub fn luaL_addlstring(buffer: *mut Buffer, str: *const c_char, len: usize);
	pub fn luaL_addstring(buffer: *mut Buffer, str: *const c_char);
	pub fn luaL_addvalue(buffer: *mut Buffer);
	pub fn luaL_pushresult(buffer: *mut Buffer);
	pub fn luaL_pushresultsize(buffer: *mut Buffer, size: usize);

	lua_state_func! {
		pub fn luaL_checkversion_(self, ver: Number, sz: usize);
		pub fn luaL_getmetafield(
			self, obj: c_int, e: *const c_char
		) -> c_int;
		pub fn luaL_callmeta(self, obj: c_int, e: *const c_char) -> c_int;
		pub fn luaL_tolstring(
			self, idx: c_int, len: *mut usize
		) -> *const c_char;
		pub fn luaL_argerror(self, arg: c_int, extra_msg: *const c_char) -> !;
		pub fn luaL_typeerror(self, arg: c_int, type_name: *const c_char) -> !;
		pub fn luaL_checklstring(
			self, arg: c_int, len: *mut usize
		) -> *const c_char;
		pub fn luaL_optlstring(
			self, arg: c_int, default: *const c_char, len: *mut usize
		) -> *const c_char;
		pub fn luaL_checknumber(self, arg: c_int) -> Number;
		pub fn luaL_optnumber(self, arg: c_int, default: Number) -> Number;

		pub fn luaL_checkinteger(self, arg: c_int) -> Integer;
		pub fn luaL_optinteger(
			self, arg: c_int, default: Integer
		) -> Integer;

		pub fn luaL_checkstack(self, sz: c_int, msg: *const c_char);
		pub fn luaL_checktype(self, arg: c_int, type_tag: c_int);
		pub fn luaL_checkany(self, arg: c_int);

		pub fn luaL_newmetatable(self, type_name: *const c_char) -> c_int;
		pub fn luaL_setmetatable(self, type_name: *const c_char);
		pub fn luaL_testudata(
			self, ud: c_int, type_name: *const c_char
		) -> *mut c_void;
		pub fn luaL_checkudata(
			self, ud: c_int, type_name: *const c_char
		) -> *mut c_void;
		
		pub fn luaL_where(self, level: c_int);
		/// # Note
		/// The return type should be [`c_int`] judging from the C header,
		/// however the documentation states that this function *never* returns.
		/// 
		/// See the manual for more information:
		/// <https://www.lua.org/manual/5.4/manual.html#luaL_error>
		pub fn luaL_error(self, fmt: *const c_char, ...) -> !;

		pub fn luaL_checkoption(
			self, arg: c_int, default: *const c_char,
			list: *const *const c_char
		) -> c_int;

		pub fn luaL_fileresult(
			self, status: c_int, file_name: *const c_char
		) -> c_int;
		pub fn luaL_execresult(self, status: c_int) -> c_int;

		pub fn luaL_ref(self, table: c_int) -> c_int;
		pub fn luaL_unref(self, table: c_int, ref_idx: c_int);

		pub fn luaL_loadfilex(
			self, file_name: *const c_char, mode: *const c_char
		) -> c_int;

		pub fn luaL_loadbufferx(
			self,
			buffer: *const c_char, buffer_sz: usize,
			name: *const c_char,
			mode: *const c_char
		) -> c_int;
		pub fn luaL_loadstring(self, code: *const c_char) -> c_int;

		pub fn luaL_len(self, idx: c_int) -> Integer;

		pub fn luaL_gsub(
			self,
			haystack: *const c_char,
			needle: *const c_char, replacement: *const c_char
		) -> *const c_char;

		pub fn luaL_setfuncs(self, list: *const Reg, n_upvalues: c_int);
		pub fn luaL_getsubtable(
			self, idx: c_int, table_name: *const c_char
		) -> c_int;

		pub fn luaL_traceback(
			self, of: *mut State,
			message: *const c_char, level: c_int
		);

		pub fn luaL_requiref(
			self, module_name: *const c_char,
			open_fn: CFunction, into_global: c_int
		);

		pub fn luaL_buffinit(self, buffer: *mut Buffer);
		pub fn luaL_buffinitsize(self, buffer: *mut Buffer, size: usize);
	}
}

/// Equivalent to the `luaL_checkversion` C macro.
/// 
/// # Safety
/// `l` must be a valid pointer to a Lua state.
pub unsafe fn luaL_checkversion(l: *mut State) {
	unsafe { luaL_checkversion_(l, VERSION_NUM, NUM_SIZES) }
}

/// Equivalent to the `luaL_loadfile` C macro.
/// 
/// # Safety
/// `l` must be a valid pointer to a Lua state,
/// and `file_name` must be a valid C string.
pub unsafe fn luaL_loadfile(l: *mut State, file_name: *const c_char) -> c_int {
	unsafe { luaL_loadfilex(l, file_name, null()) }
}

/// Functionally equivalent to the `luaL_newlibtable` C macro.
/// 
/// # Safety
/// `l` must be a valid pointer to a Lua state,
/// and `lib` has to be terminated with a sentinel pair - see [`Reg`].
pub unsafe fn luaL_newlibtable(l: *mut State, lib: &[Reg]) {
	unsafe { lua_createtable(l, 0, (lib.len() - 1) as _) }
}

/// Functionally equivalent to the `luaL_newlib` C macro.
/// 
/// # Safety
/// `l` must be a valid pointer to a Lua state,
/// and `lib` has to be terminated with a sentinel pair - see [`Reg`].
pub unsafe fn luaL_newlib(l: *mut State, lib: &[Reg]) {
	unsafe {
		luaL_checkversion(l);
		luaL_newlibtable(l, lib);
		luaL_setfuncs(l, lib.as_ptr(), 0)
	}
}

// `luaL_argcheck` and `luaL_argexpected` omitted here because they're kind of
// useless. Maybe later.

/// Equivalent to the `luaL_checkstring` C macro.
/// 
/// # Safety
/// `l` must be a valid pointer to a Lua state.
pub unsafe fn luaL_checkstring(l: *mut State, arg: c_int) -> *const c_char {
	unsafe { luaL_checklstring(l, arg, null_mut()) }
}

/// Equivalent to the `luaL_optstring` C macro.
/// 
/// # Safety
/// `l` must be a valid pointer to a Lua state.
pub unsafe fn luaL_optstring(l: *mut State, arg: c_int, default: *const c_char) -> *const c_char {
	unsafe { luaL_optlstring(l, arg, default, null_mut()) }
}

/// Equivalent to the `luaL_typename` C macro.
/// 
/// # Safety
/// `l` must be a valid pointer to a Lua state.
pub unsafe fn luaL_typename(l: *mut State, idx: c_int) -> *const c_char {
	unsafe { lua_typename(l, lua_type(l, idx)) }
}

/// Equivalent to the `luaL_dofile` C macro.
/// 
/// # Safety
/// `l` must be a valid pointer to a Lua state,
/// and `file_name` must be a valid C string.
pub unsafe fn luaL_dofile(l: *mut State, file_name: *const c_char) -> bool {
	unsafe { luaL_loadfile(l, file_name) != 0 || lua_pcall(l, 0, MULT_RET, 0) != 0 }
}

/// Equivalent to the `luaL_dofile` C macro.
/// 
/// # Safety
/// `l` must be a valid pointer to a Lua state,
/// and `code` must be a valid C string.
pub unsafe fn luaL_dostring(l: *mut State, code: *const c_char) -> bool {
	unsafe { luaL_loadstring(l, code) != 0 || lua_pcall(l, 0, MULT_RET, 0) != 0 }
}

/// Equivalent to the `luaL_getmetatable` C macro.
/// 
/// # Safety
/// `l` must be a valid pointer to a Lua state,
/// and `name` must be a valid C string.
pub unsafe fn luaL_getmetatable(l: *mut State, name: *const c_char) -> c_int {
	unsafe { lua_getfield(l, REGISTRY_INDEX, name) }
}

// `luaL_opt` omitted here because it can be written out easily.

/// Equivalent to the `luaL_loadbuffer` C macro.
/// 
/// # Safety
/// `l` must be a valid pointer to a Lua state.
/// `buffer` must be the size of `buffer_sz`,
/// and `name` must be a valid C string.
pub unsafe fn luaL_loadbuffer(
	l: *mut State,
	buffer: *const c_char, buffer_sz: usize,
	name: *const c_char
) -> c_int {
	unsafe { luaL_loadbufferx(l, buffer, buffer_sz, name, null()) }
}

// `luaL_intop` omitted here because it can be written out easily.

/// Equivalent to the `luaL_pushfail` C macro.
/// 
/// # Safety
/// `l` must be a valid pointer to a Lua state.
pub unsafe fn luaL_pushfail(l: *mut State) {
	unsafe { lua_pushnil(l) }
}

/// Initial buffer size used by the buffer system, for [`Buffer`].
/// Also known as `LUAL_BUFFERSIZE`.
/// 
/// This cannot be changed for Lua that's already compiled.
// TODO: Does it make sense to ever change this?
pub const BUFFER_SIZE: usize =
	16 * size_of::<*mut c_void>() * size_of::<Number>();

/// String buffer that allows code to build Lua strings piecemeal.
/// 
/// This structure has a lifetime `'l` because it internally stores a pointer to
/// the Lua [`State`] that was used to initialize this buffer.
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord)]
#[repr(C)]
pub struct Buffer<'l> {
	buffer_ptr: *mut c_char,
	capacity: usize,
	len: usize,
	l: *mut State,
	// `buffer` replaces `init` because that structure is not needed here.
	// Also, I am not entirely sure how this is used.
	pub buffer: [c_char; BUFFER_SIZE],
	_life: PhantomData<&'l *mut State>
}

impl Buffer<'_> {
	/// Construct an instance of [`Buffer`] that's zeroed, and put it inside of
	/// [`MaybeUninit`] for future usage.
	/// 
	/// This actually puts the buffer into an invalid state - it must be used
	/// with [`luaL_buffinit`] to properly initialize it.
	/// Only then can it be assumed to be initialized.
	pub const fn zeroed() -> MaybeUninit<Self> {
		MaybeUninit::new(Self {
			buffer_ptr: null_mut(),
			capacity: 0,
			len: 0,
			l: null_mut(),
			buffer: [0; BUFFER_SIZE],
			_life: PhantomData
		})
	}

	/// Construct a properly initialized instance of [`Buffer`] with the
	/// capacity [`BUFFER_SIZE`] in the raw Lua state pointed to by `l`.
	/// 
	/// # Safety
	/// `l` must point to a valid Lua [`State`].
	pub unsafe fn new_in_raw(l: *mut State) -> Self {
		let mut buffer = Self::zeroed();
		unsafe {
			luaL_buffinit(l, buffer.as_mut_ptr());
			buffer.assume_init()
		}
	}

	/// Allocate enough space in the buffer for a given number of C characters,
	/// and use a Rust function to fill the space with characters.
	/// 
	/// # Safety
	/// The underlying Lua state may raise a memory [error](crate::errors).
	pub unsafe fn prep_with(
		&mut self,
		size: usize, func: impl FnOnce(&mut [c_char])
	) {
		let prep_space = unsafe { luaL_prepbuffsize(self as *mut _, size) };
		func(unsafe { from_raw_parts_mut(prep_space, size) });
		self.len += size
	}

	/// Allocate enough space in the buffer [`BUFFER_SIZE`] C characters, and
	/// use a Rust function to fill the space with characters.
	/// 
	/// See also [`Buffer::prep_with`].
	/// 
	/// # Safety
	/// The underlying Lua state may raise a memory [error](crate::errors).
	pub unsafe fn prep_default_with(&mut self, func: impl FnOnce(&mut [c_char])) {
		unsafe { self.prep_with(BUFFER_SIZE, func) }
	}

	/// Get the current length of the buffer.
	/// 
	/// Equivalent to the C macro `luaL_bufflen`.
	pub const fn len(&self) -> usize {
		self.len
	}

	/// Return `true` if the buffer is empty.
	pub const fn is_empty(&self) -> bool {
		self.len == 0
	}

	/// Get the current capacity of the buffer.
	pub const fn capacity(&self) -> usize {
		self.capacity
	}

	/// Return the current contents of the buffer as a Rust mutable slice.
	/// 
	/// Functionally equivalent to the C macro `luaL_buffaddr`.
	pub fn contents(&mut self) -> &mut [c_char] {
		unsafe { from_raw_parts_mut(self.buffer_ptr, self.capacity) }
	}

	/// Add 1 C character to the buffer.
	/// 
	/// Equivalent to the C macro `luaL_addchar`.
	/// 
	/// # Safety
	/// The underlying Lua state may raise a memory [error](crate::errors).
	pub unsafe fn add_char(&mut self, ch: c_char) {
		if self.len >= self.capacity {
			unsafe { luaL_prepbuffsize(self as *mut _, 1) };
		}
		self.buffer[self.len] = ch;
		self.len += 1;
	}

	/// Remove a given number of C characters from the buffer.
	/// Equivalent to the C macro `luaL_buffsub`.
	pub fn remove(&mut self, delta: usize) {
		self.len -= delta
	}

	/// Add an array of C characters to the buffer.
	/// 
	/// Functionally equivalent to the function [`luaL_addlstring`].
	/// 
	/// # Safety
	/// The underlying Lua state may raise a memory [error](crate::errors).
	pub unsafe fn add_chars(&mut self, data: &[c_char]) {
		unsafe { luaL_addlstring(self as *mut _, data.as_ptr(), data.len()) }
	}

	/// Add a C string to the buffer.
	/// Equivalent to the function [`luaL_addstring`].
	/// 
	/// # Safety
	/// The underlying Lua state may raise a memory [error](crate::errors).
	pub unsafe fn add_string(&mut self, data: &CStr) {
		unsafe { luaL_addstring(self as *mut _, data.as_ptr()) }
	}

	/// Convert a value on top of the associated Lua stack to a string, and pop
	/// the result into the buffer.
	/// 
	/// Equivalent to the function [`luaL_addvalue`].
	pub fn add_value(&mut self) {
		unsafe { luaL_addvalue(self as *mut _) }
	}

	/// Equivalent to the function [`luaL_pushresult`].
	pub fn finish(mut self) {
		debug_assert!(
			self.len <= self.capacity,
			"buffer length is bigger than its capacity"
		);
		unsafe { luaL_pushresult(&mut self as *mut _) }
	}
}

const fn bytes_to_c_chars(b: &[u8]) -> &[c_char] {
	unsafe { from_raw_parts(
		b.as_ptr() as *const c_char,
		b.len() * size_of::<u8>() / size_of::<c_char>(),
	) }
}

impl fmt::Write for Buffer<'_> {
	fn write_str(&mut self, s: &str) -> fmt::Result {
		unsafe { self.add_chars(bytes_to_c_chars(s.as_bytes())) };
		Ok(())
	}

	fn write_char(&mut self, c: char) -> fmt::Result {
		let mut char_data = [0u8; 4];
		c.encode_utf8(&mut char_data);
		unsafe { self.add_chars(bytes_to_c_chars(&char_data as &[u8])) };
		Ok(())
	}
}
