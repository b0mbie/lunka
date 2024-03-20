//! FFI definitions for `lauxlib.h`.

#![allow(non_snake_case)]

use super::*;
use core::ffi::CStr;
use core::mem::size_of;
use core::ptr::null;

/// Global table name.
/// 
/// This cannot be changed for Lua that's already compiled.
pub const GLOBAL_TABLE: &'static CStr = unsafe {
	CStr::from_bytes_with_nul_unchecked(b"_G\0")
};

/// Key, in the registry, for the table of loaded modules.
/// 
/// This cannot be changed for Lua that's already compiled.
pub const LOADED_TABLE: &'static CStr = unsafe {
	CStr::from_bytes_with_nul_unchecked(b"_LOADED\0")
};

/// Key, in the registry, for the table of preloaded loaders.
/// 
/// This cannot be changed for Lua that's already compiled.
pub const PRELOAD_TABLE: &'static CStr = unsafe {
	CStr::from_bytes_with_nul_unchecked(b"_PRELOAD\0")
};

/// Type for arrays of functions to be registered by [`luaL_setfuncs`].
/// [`Reg::name`] is the function name and [`Reg::func`] is a pointer to the
/// function.
/// 
/// Also known as `luaL_Reg`.
/// 
/// Any array of [`Reg`] must end with a sentinel entry in which both `name` and
/// `func` are null.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
#[repr(C)]
pub struct Reg {
	pub name: *const c_char,
	pub func: CFunction
}

/// Packed combination [`Integer`] and [`Number`] type sizes for
/// [`luaL_checkversion_`] to check against.
pub const NUM_SIZES: usize = size_of::<Integer>() * 16 + size_of::<Number>();

/// Constant that is guaranteed to indicate no reference.
pub const NO_REF: c_int = -2;

/// Constant that indicates a reference to `nil`.
pub const REF_NIL: c_int = -1;

extern "C" {
	pub fn luaL_newstate() -> *mut State;

	lua_state_func! {
		pub fn luaL_checkversion_(&mut self, ver: Number, sz: usize);
		pub fn luaL_getmetafield(
			&mut self, obj: c_int, e: *const c_char
		) -> c_int;
		pub fn luaL_callmeta(&mut self, obj: c_int, e: *const c_char) -> c_int;
		pub fn luaL_tolstring(
			&mut self, idx: c_int, len: *mut usize
		) -> *const c_char;
		pub fn luaL_argerror(&mut self, arg: c_int, extra_msg: *const c_char) -> !;
		pub fn luaL_typeerror(&mut self, arg: c_int, type_name: *const c_char) -> !;
		pub fn luaL_checklstring(
			&mut self, arg: c_int, len: *mut usize
		) -> *const c_char;
		pub fn luaL_optlstring(
			&mut self, arg: c_int, default: *const c_char, len: *mut usize
		) -> *const c_char;
		pub fn luaL_checknumber(&mut self, arg: c_int) -> Number;
		pub fn luaL_optnumber(&mut self, arg: c_int, default: Number) -> Number;

		pub fn luaL_checkinteger(&mut self, arg: c_int) -> Integer;
		pub fn luaL_optinteger(
			&mut self, arg: c_int, default: Integer
		) -> Integer;

		pub fn luaL_checkstack(&mut self, sz: c_int, msg: *const c_char);
		pub fn luaL_checktype(&mut self, arg: c_int, type_tag: c_int);
		pub fn luaL_checkany(&mut self, arg: c_int);

		pub fn luaL_newmetatable(&mut self, type_name: *const c_char) -> c_int;
		pub fn luaL_setmetatable(&mut self, type_name: *const c_char);
		pub fn luaL_testudata(
			&mut self, ud: c_int, type_name: *const c_char
		) -> *mut c_void;
		pub fn luaL_checkudata(
			&mut self, ud: c_int, type_name: *const c_char
		) -> *mut c_void;
		
		pub fn luaL_where(&mut self, level: c_int);
		/// # Note
		/// The return type should be [`c_int`] judging from the C header,
		/// however the documentation states that this function *never* returns.
		/// 
		/// See the manual for more information:
		/// <https://www.lua.org/manual/5.4/manual.html#luaL_error>
		pub fn luaL_error(&mut self, fmt: *const c_char, ...) -> !;

		pub fn luaL_checkoption(
			&mut self, arg: c_int, default: *const c_char,
			list: *const *const c_char
		) -> c_int;

		pub fn luaL_fileresult(
			&mut self, status: c_int, file_name: *const c_char
		) -> c_int;
		pub fn luaL_execresult(&mut self, status: c_int) -> c_int;

		pub fn luaL_ref(&mut self, table: c_int) -> c_int;
		pub fn luaL_unref(&mut self, table: c_int, ref_idx: c_int);

		pub fn luaL_loadfilex(
			&mut self, file_name: *const c_char, mode: *const c_char
		) -> c_int;

		pub fn luaL_loadbufferx(
			&mut self,
			buffer: *const c_char, buffer_sz: usize,
			name: *const c_char,
			mode: *const c_char
		) -> c_int;
		pub fn luaL_loadstring(&mut self, code: *const c_char) -> c_int;

		pub fn luaL_len(&self, idx: c_int) -> Integer;

		pub fn luaL_gsub(
			&mut self,
			haystack: *const c_char,
			needle: *const c_char, replacement: *const c_char
		) -> *const c_char;

		pub fn luaL_setfuncs(&mut self, list: *const Reg, n_upvalues: c_int);
		pub fn luaL_getsubtable(
			&mut self, idx: c_int, table_name: *const c_char
		) -> c_int;

		pub fn luaL_traceback(
			&mut self, of: *mut State,
			message: *const c_char, level: c_int
		);

		pub fn luaL_requiref(
			&mut self, module_name: *const c_char,
			open_fn: CFunction, into_global: c_int
		);
	}
}

/// Equivalent to the `luaL_checkversion` C macro.
#[inline]
pub unsafe fn luaL_checkversion(l: *mut State) {
	luaL_checkversion_(l, VERSION_NUM, NUM_SIZES)
}

/// Equivalent to the `luaL_loadfile` C macro.
#[inline]
pub unsafe fn luaL_loadfile(l: *mut State, file_name: *const c_char) -> c_int {
	luaL_loadfilex(l, file_name, null())
}

/// Functionally equivalent to the `luaL_newlibtable` C macro.
/// 
/// `lib` still has to be terminated with a sentinel pair - see [`Reg`].
#[inline]
pub unsafe fn luaL_newlibtable(l: *mut State, lib: &[Reg]) {
	lua_createtable(l, 0, (lib.len() - 1) as _)
}

/// Functionally equivalent to the `luaL_newlib` C macro.
/// 
/// `lib` still has to be terminated with a sentinel pair - see [`Reg`].
#[inline]
pub unsafe fn luaL_newlib(l: *mut State, lib: &[Reg]) {
	luaL_checkversion(l);
	luaL_newlibtable(l, lib);
	luaL_setfuncs(l, lib.as_ptr(), 0);
}

// `luaL_argcheck` and `luaL_argexpected` omitted here because they're kind of
// useless. Maybe later.

/// Equivalent to the `luaL_checkstring` C macro.
#[inline]
pub unsafe fn luaL_checkstring(l: *mut State, arg: c_int) -> *const c_char {
	luaL_checklstring(l, arg, null_mut())
}

/// Equivalent to the `luaL_optstring` C macro.
#[inline]
pub unsafe fn luaL_optstring(
	l: *mut State, arg: c_int, default: *const c_char
) -> *const c_char {
	luaL_optlstring(l, arg, default, null_mut())
}

/// Equivalent to the `luaL_typename` C macro.
#[inline]
pub unsafe fn luaL_typename(l: *mut State, idx: c_int) -> *const c_char {
	lua_typename(l, lua_type(l, idx))
}

/// Equivalent to the `luaL_dofile` C macro.
#[inline]
pub unsafe fn luaL_dofile(l: *mut State, file_name: *const c_char) -> bool {
	luaL_loadfile(l, file_name) != 0 || lua_pcall(l, 0, MULT_RET, 0) != 0
}

/// Equivalent to the `luaL_dofile` C macro.
#[inline]
pub unsafe fn luaL_dostring(l: *mut State, code: *const c_char) -> bool {
	luaL_loadstring(l, code) != 0 || lua_pcall(l, 0, MULT_RET, 0) != 0
}

/// Equivalent to the `luaL_getmetatable` C macro.
#[inline]
pub unsafe fn luaL_getmetatable(l: *mut State, name: *const c_char) -> c_int {
	lua_getfield(l, REGISTRY_INDEX, name)
}

// `luaL_opt` omitted here because it can be written out easily.

/// Equivalent to the `luaL_loadbuffer` C macro.
#[inline]
pub unsafe fn luaL_loadbuffer(
	l: *mut State,
	buffer: *const c_char, buffer_sz: usize,
	name: *const c_char
) -> c_int {
	luaL_loadbufferx(l, buffer, buffer_sz, name, null())
}

// `luaL_intop` omitted here because it can be written out easily.

/// Equivalent to the `luaL_pushfail` C macro.
#[inline]
pub unsafe fn luaL_pushfail(l: *mut State) {
	lua_pushnil(l)
}

// TODO: `luaL_Buffer`?
