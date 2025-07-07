//! Representing enum values with strings in Lua.

use core::ffi::{
	CStr,
	c_int
};
use lunka::prelude::*;

pub unsafe trait LuaEnum<const N: usize> {
	const OPTIONS: &'static lunka::AuxOptions<'static, N>;
	unsafe fn from_index_unchecked(index: usize) -> Self;
}

#[derive(Debug)]
enum SocketKind {
	Udp,
	Tcp,
	UnixUdp,
	UnixTcp,
}

macro_rules! c_str {
	($data:literal) => {
		CStr::from_bytes_with_nul_unchecked(concat!($data, "\0").as_bytes())
	};
	($id:ident) => { unsafe {
		CStr::from_bytes_with_nul_unchecked(
			concat!(stringify!($id), "\0").as_bytes()
		)
	} };
}

unsafe impl LuaEnum<4> for SocketKind {
	const OPTIONS: &'static LuaAuxOptions<'static, 4> = &LuaAuxOptions::new([
		c_str!(udp),
		c_str!(tcp),
		unsafe { c_str!("unix udp") },
		unsafe { c_str!("unix tcp") },
	]);
	unsafe fn from_index_unchecked(index: usize) -> Self {
		match index {
			0 => Self::Udp,
			1 => Self::Tcp,
			2 => Self::UnixUdp,
			3 => Self::UnixTcp,
			_ => core::hint::unreachable_unchecked(),
		}
	}
}

trait ThreadExt {
	unsafe fn check_enum<E: LuaEnum<N>, const N: usize>(&self, arg: c_int) -> E;
}

impl ThreadExt for LuaThread {
	unsafe fn check_enum<E: LuaEnum<N>, const N: usize>(&self, arg: c_int) -> E {
		let index = self.check_option(arg, None, E::OPTIONS);
		unsafe { E::from_index_unchecked(index) }
	}
}

unsafe extern "C" fn l_test(l: *mut LuaState) -> c_int {
	let lua = unsafe { LuaThread::from_ptr(l) };
	let socket_kind: SocketKind = lua.check_enum(1);
	println!("socket kind: {socket_kind:?}");
	0
}

unsafe extern "C" fn l_main(l: *mut LuaState) -> c_int {
	let lua = unsafe { LuaThread::from_ptr_mut(l) };
	let mut test = move |variant: &[u8]| {
		lua.run_managed(move |mut mg| {
			mg.push_c_function(l_test);
			mg.push_string(variant);
			mg.call(1, 0)
		})
	};
	test(b"udp");
	test(b"tcp");
	test(b"unix udp");
	test(b"unix tcp");
	test(b"invalid");
	0
}

fn main() {
	let mut lua = Lua::new();
	let did_run_ok = lua.run_managed(move |mut mg| {
		mg.push_c_function(l_main);
		mg.pcall(0, 1, 0).is_ok()
	});
	assert!(!did_run_ok, "test code should fail");
}
