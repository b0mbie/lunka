//! Example library that demonstrates
//! the exposing of some Rust functionality to Lua
//! in an importable library.

use lunka::prelude::*;
use std::{
	fs::metadata,
	time::SystemTime,
};

lua_export_fn!(luaopen_os2);
fn luaopen_os2(lua: &mut LuaThread) -> LuaRets {
	lua.new_lib(&LIBRARY);
	1.into()
}

const LIBRARY: LuaLibrary = lua_library! {
	metadata: l_metadata,
};

extern "C-unwind" fn l_metadata(mut lua: LuaCtx<'_>) -> LuaRets {
	let path = lua.check_string(1);
	
	let meta = match metadata(String::from_utf8_lossy(path).as_ref()) {
		Ok(meta) => meta,
		Err(error) => {
			lua.push_fail();
			lua.push_display(&error);
			return 2.into()
		}
	};

	lua.create_table(0, 1);

	let file_type = meta.file_type();
	lua.push_string(if file_type.is_file() {
		"file"
	} else if file_type.is_dir() {
		"directory"
	} else if file_type.is_symlink() {
		"symlink"
	} else {
		"other"
	}.as_bytes());
	lua.set_field(-2, c"type");

	lua.push_integer(meta.len() as _);
	lua.set_field(-2, c"len");

	if let Ok(time) = meta.modified()
	&& let Ok(time) = time.duration_since(SystemTime::UNIX_EPOCH) {
		lua.push_number(time.as_secs_f64());
		lua.set_field(-2, c"modified");
	}

	1.into()
}
