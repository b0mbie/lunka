use core::ffi::c_int;
use lunka::prelude::*;

unsafe extern "C-unwind" fn l_hello(l: *mut LuaState) -> c_int {
	// SAFETY: Caller ensures `l` is valid.
	let lua = unsafe { LuaThread::from_ptr_mut(l) };

	let n = lua.check_number(1);

	lua.managed().push_string("Hello, world!");
	lua.push_number(n * core::f64::consts::PI as LuaNumber);

	2
}

const LIBRARY: LuaLibrary<1> = library! {
	hello: l_hello
};

#[unsafe(no_mangle)]
unsafe extern "C-unwind" fn luaopen_hello(l: *mut LuaState) -> c_int {
	// SAFETY: Caller ensures `l` is valid.
	let lua = unsafe { LuaThread::from_ptr_mut(l) };
	lua.managed().new_lib(&LIBRARY);
	1
}
