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

macro_rules! cstr {
	($text:literal) => {
		CStr::from_bytes_with_nul_unchecked(
			concat!($text, "\0").as_bytes()
		)
	};
}

const TEST_FILE: &CStr = unsafe { cstr!("test.lua") };

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
fn report(lua: &mut Thread, status: Status) -> bool {
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

pub const RS_LIB: Library<'static, 1> = Library::new(unsafe {[
	(cstr!("print"), l_rs_print)
]});

unsafe extern "C" fn l_msgh(l: *mut cdef::State) -> core::ffi::c_int {
	let mut lua: Thread = Thread::from_ptr(l);
	
	if let Some(msg) = lua.to_string(1) {
		lua.traceback(&lua, msg, 1);
		return 1
	}

	let ok = lua.run_managed(|mut mg| {
		mg.call_metamethod(1, cstr!("__tostring"))
	});

	if ok && lua.type_of(-1) == Type::String {
		return 1
	}

	push_fmt_string!(lua, "(error object is a %s value)", lua.type_name_of(1));

	1
}

unsafe extern "C" fn l_main(l: *mut cdef::State) -> core::ffi::c_int {
	let mut lua: Thread = Thread::from_ptr(l);
	
	lua.new_lib(&RS_LIB);
	lua.set_global(cstr!("rs"));

	lua.run_managed(|mut mg| mg.open_libs());

	lua.push_c_function(l_msgh);
	let base = lua.top();

	let status = lua.load_file(TEST_FILE);
	if !status.is_ok() {
		lua.error()
	}

	lua.push_byte_str(b"Mega Serval");
	let status = lua.run_managed(|mut mg| {
		mg.restart_gc();
		mg.pcall(1, 0, base)
	});
	if !report(&mut lua, status) { return 0 }
		
	lua.run_managed(|mut mg| mg.run_gc());

	0
}

fn main() {
	let Some(mut lua) = Lua::new_auxlib_default() else {
		eprintln!("couldn't allocate Lua state");
		return
	};

	lua.push_c_function(l_main);
	let status = lua.run_managed(|mut mg| {
		mg.restart_gc();
		mg.pcall(0, 0, 0)
	});
	if !report(&mut lua, status) { return }
}
