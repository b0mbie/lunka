//! Lua runtime stuff.

use lunka::*;

use core::ffi::CStr;
use core::mem::transmute;
use std::error::Error;
use std::io::{
	stdout, Write
};

const TEST_FILE: &CStr = unsafe { CStr::from_bytes_with_nul_unchecked(
	b"test.lua\0"
) };

fn get_lua_error(lua: &Lua) -> Option<Box<dyn Error>> {
	unsafe { lua.to_string(-1) }
		.map(|message| {
			lua.pop(1);
			String::from_utf8_lossy(message.to_bytes()).into_owned().into()
		})
}

unsafe extern "C" fn l_rs_print(l: *mut cdef::State) -> core::ffi::c_int {
	let lua: Thread = Thread::from_ptr(l);
	if let Some(data) = lua.to_chars(1) {
		let mut out = stdout();
		let _ = out.write_all(transmute(data));
		let _ = out.write_all(b"\n");
	}
	0
}

fn main() -> Result<(), Box<dyn Error>> {
	let mut lua = Lua::new_auxlib_default().ok_or("couldn't allocate Lua state")?;
	println!("running Lua {}", lua.version());

	lua.run_managed(|mut mg| unsafe { mg.open_libs() });

	unsafe { lua.register(
		CStr::from_bytes_with_nul_unchecked(b"rs_print\0"),
		l_rs_print
	) };

	lua.load_file(TEST_FILE).or_else(|_| {
		get_lua_error(&lua)
			.unwrap_or_else(|| "a load error occurred".into())
	})?;
		
	println!("... load OK");
	lua.run_managed(|mut mg| mg.run_gc());

	lua.run_managed(|mut mg| {
		mg.restart_gc();
		mg.pcall(0, 0, 0)
	}).or_else(|_| {
		get_lua_error(&lua)
			.unwrap_or_else(|| "a runtime error occurred".into())
	})?;
		
	println!("... run OK");
	lua.run_managed(|mut mg| mg.run_gc());

	Ok(())
}
