//! Example of extending `Thread` to add an overloaded `push` method.

use core::ffi::CStr;
use lunka::prelude::*;

const PRINT_CODE: &'static str = r#"print("Received arguments: ", ...)"#;

const PRINT_CODE_LUA_NAME: &'static CStr = unsafe {
	CStr::from_bytes_with_nul_unchecked(b"=<embedded>\0")
};

trait Push<const N: usize> {
	fn push_into(&self, thread: &LuaThread);
}

impl Push<1> for ()  {
	fn push_into(&self, thread: &LuaThread) {
		thread.push_nil();
	}
}

impl Push<1> for LuaInteger {
	fn push_into(&self, thread: &LuaThread) {
		thread.push_integer(*self);
	}
}

impl Push<1> for LuaNumber {
	fn push_into(&self, thread: &LuaThread) {
		thread.push_number(*self);
	}
}

impl Push<1> for &str {
	fn push_into(&self, thread: &LuaThread) {
		unsafe { thread.push_byte_str(self.as_bytes()) };
	}
}

impl<T: Push<1>, E: Push<1>> Push<2> for Result<T, E> {
	fn push_into(&self, thread: &LuaThread) {
		match self {
			Self::Ok(t) => {
				t.push_into(thread);
				thread.push_nil()
			}
			Self::Err(e) => {
				thread.push_fail();
				e.push_into(thread)
			}
		}
	}
}

trait LuaThreadExt {
	fn push<const N: usize>(&self, what: impl Push<N>);
}

impl LuaThreadExt for LuaThread {
	fn push<const N: usize>(&self, what: impl Push<N>) {
		what.push_into(self)
	}
}

fn main() {
	let mut lua = Lua::new();
	lua.run_managed(|mut mg| unsafe { mg.open_libs() });

	if !lua.load_byte_str(PRINT_CODE.as_bytes(), PRINT_CODE_LUA_NAME).is_ok() {
		panic!("couldn't load Lua chunk");
	}

	lua.push(4 as LuaInteger);
	lua.push(3.14 as LuaNumber);
	lua.push("how");

	if !lua.run_managed(|mut mg| {
		mg.restart_gc();
		mg.pcall(3, 0, 0)
	}).is_ok() {
		let error_bytes = unsafe { lua.to_byte_str(-1) };
		panic!(
			"error while running Lua chunk: {}",
			error_bytes.map(String::from_utf8_lossy)
				.unwrap_or(std::borrow::Cow::Borrowed("<no message>"))
		);
	}
}
