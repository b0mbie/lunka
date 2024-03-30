//! FFI definitions for `lualib.h`.

use super::*;
use core::ffi::CStr;

pub const COROUTINE_LIB_NAME: &'static CStr = unsafe {
	CStr::from_bytes_with_nul_unchecked(b"coroutine\0")
};

pub const TABLE_LIB_NAME: &'static CStr = unsafe {
	CStr::from_bytes_with_nul_unchecked(b"table\0")
};

pub const IO_LIB_NAME: &'static CStr = unsafe {
	CStr::from_bytes_with_nul_unchecked(b"io\0")
};

pub const OS_LIB_NAME: &'static CStr = unsafe {
	CStr::from_bytes_with_nul_unchecked(b"os\0")
};

pub const STRING_LIB_NAME: &'static CStr = unsafe {
	CStr::from_bytes_with_nul_unchecked(b"string\0")
};

pub const UTF8_LIB_NAME: &'static CStr = unsafe {
	CStr::from_bytes_with_nul_unchecked(b"utf8\0")
};

pub const MATH_LIB_NAME: &'static CStr = unsafe {
	CStr::from_bytes_with_nul_unchecked(b"math\0")
};

pub const DEBUG_LIB_NAME: &'static CStr = unsafe {
	CStr::from_bytes_with_nul_unchecked(b"debug\0")
};

pub const PACKAGE_LIB_NAME: &'static CStr = unsafe {
	CStr::from_bytes_with_nul_unchecked(b"package\0")
};

#[link(name = "lua54", kind = "raw-dylib")]
extern "C" {
	lua_state_func! {
		pub fn luaopen_base(self) -> c_int;

		pub fn luaopen_coroutine(self) -> c_int;
		pub fn luaopen_table(self) -> c_int;
		pub fn luaopen_io(self) -> c_int;
		pub fn luaopen_os(self) -> c_int;
		pub fn luaopen_string(self) -> c_int;
		pub fn luaopen_utf8(self) -> c_int;
		pub fn luaopen_math(self) -> c_int;
		pub fn luaopen_debug(self) -> c_int;
		pub fn luaopen_package(self) -> c_int;

		pub fn luaL_openlibs(self);
	}
}
