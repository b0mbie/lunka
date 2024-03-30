//! (Very) simple Lua interpreter.

use lunka::prelude::*;
use std::env::args;
use std::ffi::{
	c_int,
	c_uint,
	CStr
};
use std::io::{
	stderr,
	Write
};
use std::mem::transmute;
use std::process::ExitCode;

macro_rules! cstr {
	($data:literal) => {
		CStr::from_bytes_with_nul_unchecked(concat!($data, "\0").as_bytes())
	};
}

fn c_eprintln(data: &CStr) {
	let mut out = stderr();
	let _ = out.write_all(unsafe { transmute(data.to_bytes()) });
	let _ = out.write_all(b"\n");
}

fn report(lua: &mut LuaThread, status: LuaStatus) -> bool {
	if !status.is_ok() {
		if let Some(message) = unsafe { lua.to_string(-1) } {
			c_eprintln(message);
		}
		lua.run_managed(|mut mg| unsafe { mg.pop(1) });
		false
	} else {
		true
	}
}

unsafe extern "C" fn l_err_handler(l: *mut LuaState) -> c_int {
	let mut lua: LuaThread = LuaThread::from_ptr(l);

	if let Some(msg) = lua.to_string(1) {
		lua.traceback(&lua, Some(msg), 1);
		return 1
	}

	let ok = lua.run_managed(|mut mg| {
		mg.call_metamethod(1, cstr!("__tostring"))
	});

	if ok && lua.type_of(-1) == LuaType::String {
		return 1
	}

	lua_push_fmt_string!(lua, "(error object is a %s value)", lua.type_name_of(1));

	1
}

unsafe extern "C" fn l_main(lua: *mut LuaState) -> c_int {
	let mut lua: LuaThread = LuaThread::from_ptr(lua);

	unsafe { lua.check_version() };
	lua.run_managed(|mut mg| unsafe { mg.open_libs() });

	lua.push_c_function(l_err_handler);
	let base = lua.top();

	let mut arguments = args().skip(1);
	let load_status = if let Some(mut file_name) = arguments.nth(0) {
		lua.load_file(unsafe {
			file_name.push('\0');
			CStr::from_bytes_until_nul(file_name.as_bytes()).unwrap_unchecked()
		})
	} else {
		lua.load_stdin()
	};

	if !report(&mut lua, load_status) {
		return 0
	}

	let mut arg_count: c_uint = 0;
	for arg in arguments {
		unsafe { lua.push_byte_str(arg.as_bytes()) };
		arg_count += 1;
	}

	let run_status = lua.run_managed(|mut mg| mg.pcall(arg_count, 0, base));
	if !report(&mut lua, run_status) {
		return 0
	}

	lua.push_boolean(true);
	1
}

fn main() -> ExitCode {
	let Some(mut lua) = Lua::new_default() else {
		eprintln!("cannot create state: not enough memory");
		return ExitCode::FAILURE
	};

	lua.push_c_function(l_main);
	let status = lua.run_managed(|mut mg| mg.pcall(0, 1, 0));
	let is_ok = lua.to_boolean(-1);
	report(&mut lua, status);

	if status.is_ok() && is_ok {
		ExitCode::SUCCESS
	} else {
		ExitCode::FAILURE
	}
}
