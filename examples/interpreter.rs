//! (Very) simple Lua interpreter.

use lunka::prelude::*;
use std::{
	env::args,
	ffi::{
		CStr, c_int, c_uint,
	},
	io::{
		stderr,
		Write
	},
	process::ExitCode
};

fn c_eprintln(data: &CStr) {
	let mut out = stderr();
	let _ = out.write_all(data.to_bytes());
	let _ = out.write_all(b"\n");
}

fn report(lua: &mut LuaThread, status: LuaStatus) -> bool {
	if !status.is_ok() {
		if let Some(message) = lua.to_c_str(-1) {
			c_eprintln(message);
		}
		lua.run_managed(|mut mg| unsafe { mg.pop(1) });
		false
	} else {
		true
	}
}

unsafe extern "C-unwind" fn l_err_handler(l: *mut LuaState) -> c_int {
	let lua = unsafe { LuaThread::from_ptr_mut(l) };

	if let Some(msg) = lua.to_c_str(1) {
		lua.traceback(lua, Some(msg), 1);
		return 1
	}

	let ok = lua.run_managed(|mut mg| unsafe {
		mg.call_metamethod(1, c"__tostring")
	});

	if ok && lua.type_of(-1) == LuaType::String {
		return 1
	}

	unsafe { lua_push_fmt_string!(lua, c"(error object is a %s value)", lua.type_name_of(1)) };

	1
}

unsafe extern "C-unwind" fn l_main(l: *mut LuaState) -> c_int {
	let lua = unsafe { LuaThread::from_ptr_mut(l) };

	lua.check_version();
	lua.run_managed(|mut mg| mg.open_libs());

	lua.push_c_function(l_err_handler);
	let base = lua.top();

	let mut arguments = args().skip(1);
	let load_status = if let Some(mut file_name) = arguments.next() {
		lua.load_file(unsafe {
			file_name.push('\0');
			CStr::from_bytes_until_nul(file_name.as_bytes()).unwrap_unchecked()
		})
	} else {
		lua.load_stdin()
	};

	if !report(lua, load_status) {
		return 0
	}

	let mut arg_count: c_uint = 0;
	for arg in arguments {
		lua.push_string(arg.as_bytes());
		arg_count += 1;
	}

	let run_status = lua.run_managed(|mut mg| {
		mg.restart_gc();
		let run_status = unsafe { mg.pcall(arg_count, 0, base) };
		mg.stop_gc();
		run_status
	});
	if !report(lua, run_status) {
		return 0
	}

	lua.push_boolean(true);
	1
}

fn main() -> ExitCode {
	let mut lua = Lua::new();

	lua.push_c_function(l_main);
	let status = lua.run_managed(|mut mg| unsafe { mg.pcall(0, 1, 0) });
	let is_ok = lua.to_boolean(-1);
	report(&mut lua, status);

	if status.is_ok() && is_ok {
		ExitCode::SUCCESS
	} else {
		ExitCode::FAILURE
	}
}
