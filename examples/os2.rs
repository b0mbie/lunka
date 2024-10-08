//! Example library that demonstrates the exposing of some Rust functionality to
//! Lua in an importable library.

use lunka::prelude::*;
use std::{
	ffi::{
		c_int, CStr
	},
	fmt::Write,
	fs::metadata, time::SystemTime,
};

macro_rules! c_str {
	($ident:ident) => {
		unsafe { CStr::from_bytes_with_nul_unchecked(
			concat!(stringify!($ident), "\0").as_bytes()
		) }
	};
}

unsafe extern "C" fn l_metadata(l: *mut LuaState) -> c_int {	
	let lua = LuaThread::from_ptr_mut(l);
	let path = lua.check_string(1);
	
	let meta = match metadata(String::from_utf8_lossy(path).into_owned()) {
		Ok(meta) => meta,
		Err(error) => {
			lua.push_fail();
			let mut buf = lua.new_buffer();
			let _ = write!(buf, "{error}");
			return 2
		}
	};

	lua.run_managed(|mut mg| {
		mg.create_table(0, 1);

		let file_type = meta.file_type();
		mg.push_string(if file_type.is_file() {
			"file"
		} else if file_type.is_dir() {
			"directory"
		} else if file_type.is_symlink() {
			"symlink"
		} else {
			"other"
		}.as_bytes());
		mg.set_field(-2, c_str!(type));

		mg.push_integer(meta.len() as _);
		mg.set_field(-2, c_str!(len));

		if let Ok(time) = meta.modified() {
			if let Ok(time) = time.duration_since(SystemTime::UNIX_EPOCH) {
				mg.push_number(time.as_secs_f64());
				mg.set_field(-2, c_str!(modified));
			}
		}
	});

	1
}

const LIBRARY: LuaLibrary<1> = lua_library! {
	metadata: l_metadata
};

#[export_name = "luaopen_os2"]
unsafe extern "C" fn luaopen_os2(l: *mut LuaState) -> c_int {
	let lua = LuaThread::from_ptr(l);
	lua.new_lib(&LIBRARY);
	1
}
