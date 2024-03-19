//! FFI definitions for `lualib.h`.

use super::*;
use core::ffi::CStr;

pub const COROUTINE_LIB_NAME: &'static CStr = unsafe {
	CStr::from_bytes_with_nul_unchecked("coroutine\0".as_bytes())
};

pub const TABLE_LIB_NAME: &'static CStr = unsafe {
	CStr::from_bytes_with_nul_unchecked("table\0".as_bytes())
};

pub const IO_LIB_NAME: &'static CStr = unsafe {
	CStr::from_bytes_with_nul_unchecked("io\0".as_bytes())
};

pub const OS_LIB_NAME: &'static CStr = unsafe {
	CStr::from_bytes_with_nul_unchecked("os\0".as_bytes())
};

pub const STRING_LIB_NAME: &'static CStr = unsafe {
	CStr::from_bytes_with_nul_unchecked("string\0".as_bytes())
};

pub const UTF8_LIB_NAME: &'static CStr = unsafe {
	CStr::from_bytes_with_nul_unchecked("utf8\0".as_bytes())
};

pub const MATH_LIB_NAME: &'static CStr = unsafe {
	CStr::from_bytes_with_nul_unchecked("math\0".as_bytes())
};

pub const DEBUG_LIB_NAME: &'static CStr = unsafe {
	CStr::from_bytes_with_nul_unchecked("debug\0".as_bytes())
};

pub const PACKAGE_LIB_NAME: &'static CStr = unsafe {
	CStr::from_bytes_with_nul_unchecked("package\0".as_bytes())
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
