//! "Hello, world!" example running in Lua.

use core::ffi::c_int;
use lunka::prelude::*;

unsafe extern "C" fn l_main(l: *mut LuaState) -> c_int {
	let lua = unsafe { LuaThread::from_ptr_mut(l) };
	lua.run_managed(move |mut mg| unsafe { mg.open_libs() });

	let is_ok = lua.load_string(
		r#"print("Hello, world!")"#,
		c"=<embedded>"
	).is_ok();
	if !is_ok {
		let error = {
			unsafe { lua.to_string(-1) }
				.and_then(move |bytes| core::str::from_utf8(bytes).ok())
				.unwrap_or("<message is not UTF-8>")
		};
		eprintln!("couldn't load example Lua code:\n\t{error}");
		lua.push_boolean(false);
		return 1
	}

	let is_ok = lua.run_managed(move |mut mg| mg.pcall(0, 0, 0).is_ok());
	if !is_ok {
		let error = {
			unsafe { lua.to_string(-1) }
				.and_then(move |bytes| core::str::from_utf8(bytes).ok())
				.unwrap_or("<message is not UTF-8>")
		};
		eprintln!("couldn't run example Lua code:\n\t{error}");
		lua.push_boolean(false);
		return 1
	}

	lua.push_boolean(true);
	1
}

fn main() {
	let mut lua = Lua::new();

	let did_run_ok = lua.run_managed(move |mut mg| {
		mg.push_c_function(l_main);
		if mg.pcall(0, 1, 0).is_ok() {
			mg.to_boolean(-1)
		} else {
			false
		}
	});
	if !did_run_ok {
		panic!("couldn't run \"Hello, world!\" example for some reason");
	}
}
