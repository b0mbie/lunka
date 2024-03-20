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

extern "C" {
	lua_state_func! {
		pub fn luaopen_base(&mut self) -> c_int;

		pub fn luaopen_coroutine(&mut self) -> c_int;
		pub fn luaopen_table(&mut self) -> c_int;
		pub fn luaopen_io(&mut self) -> c_int;
		pub fn luaopen_os(&mut self) -> c_int;
		pub fn luaopen_string(&mut self) -> c_int;
		pub fn luaopen_utf8(&mut self) -> c_int;
		pub fn luaopen_math(&mut self) -> c_int;
		pub fn luaopen_debug(&mut self) -> c_int;
		pub fn luaopen_package(&mut self) -> c_int;

		pub fn luaL_openlibs(&mut self);
	}
}
