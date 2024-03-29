//! Lua runtime stuff.

use lunka::*;

use core::ffi::CStr;
use core::fmt::Write;
use core::mem::transmute;
use std::io::{
	stdout,
	stderr,
	Write as IoWrite
};

const TEST_FILE: &CStr = unsafe { CStr::from_bytes_with_nul_unchecked(
	b"test.lua\0"
) };

fn c_println(data: &CStr) {
	let mut out = stdout();
	let _ = out.write_all(unsafe { transmute(data.to_bytes()) });
	let _ = out.write_all(b"\n");
}

fn c_eprintln(data: &CStr) {
	let mut out = stderr();
	let _ = out.write_all(unsafe { transmute(data.to_bytes()) });
	let _ = out.write_all(b"\n");
}

unsafe extern "C" fn l_rs_print(l: *mut cdef::State) -> core::ffi::c_int {
	let lua: Thread = Thread::from_ptr(l);
	
	for index in 1..=lua.top() {
		if let Some(data) = lua.to_string(index) {
			c_println(data);
		}
	}
	0
}

#[must_use]
fn report(lua: &mut Lua, status: ThreadStatus) -> bool {
	if !status.is_ok() {
		if let Some(message) = unsafe { lua.to_string(-1) } {
			lua.pop(1);
			c_eprintln(message);
		} else {
			let mut buf = lua.new_buffer();
			let _ = buf.write_str("(error object is a ");
			unsafe { buf.add_string(lua.type_name_of(-1)) };
			let _ = buf.write_str(" value)");
			buf.finish();
			c_eprintln(unsafe { lua.to_string(-1).unwrap_unchecked() })
		};
		false
	} else {
		true
	}
}

fn main() {
	let Some(mut lua) = Lua::new_auxlib_default() else {
		eprintln!("couldn't allocate Lua state");
		return
	};

	lua.run_managed(|mut mg| unsafe { mg.open_libs() });

	unsafe { lua.register(
		CStr::from_bytes_with_nul_unchecked(b"rs_print\0"),
		l_rs_print
	) };

	let status = lua.load_file(TEST_FILE);
	if !report(&mut lua, status) { return }

	unsafe { lua.push_byte_str(b"Mega Serval") };
	let status = lua.run_managed(|mut mg| {
		mg.restart_gc();
		mg.pcall(1, 0, 0)
	});
	if !report(&mut lua, status) { return }
		
	lua.run_managed(|mut mg| mg.run_gc());
}
