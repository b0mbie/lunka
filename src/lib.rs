//! # lunka
//! `#![no_std]` bindings to Lua 5.4.

#![no_std]

use core::ffi::{
	c_char, c_int, c_uint, c_ushort, c_void, CStr
};
use core::marker::PhantomData;
use core::ops::{
	Deref, DerefMut
};
use core::slice::{
	from_raw_parts, from_raw_parts_mut
};

pub mod cdef;
pub use cdef::{
	Number,
	Integer,
	upvalue_index
};

use crate::cdef::*;

/// Lua garbage collection modes enum.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Gc {
	Incremental {
		pause: c_int,
		step_multiplier: c_int,
		step_size: c_int
	},
	Generational {
		minor_mul: c_int,
		major_mul: c_int
	}
}

/// Lua thread wrapper that's used by [`MainThread`](super::MainThread) and
/// friends.
#[derive(Debug)]
#[repr(transparent)]
pub struct Thread<const ID_SIZE: usize = DEFAULT_ID_SIZE> {
	l: *mut State
}

/// Panic function that's similar to the panic function defined in `lauxlib.h`.
pub unsafe extern "C" fn lua_panic(l: *mut State) -> c_int {
	let msg = {
		let msg_str = lua_tostring(l, -1);
		if msg_str.is_null() {
			CStr::from_bytes_with_nul_unchecked(
				b"error object is not a string\0"
			)
		} else {
			CStr::from_ptr(msg_str)
		}
	};

	let msg = msg.to_str().unwrap_or("error object does not contain valid UTF-8");
	panic!("{}", msg)
}

#[derive(Debug)]
#[repr(transparent)]
pub struct Managed<'l, const ID_SIZE: usize = DEFAULT_ID_SIZE> {
    l: *mut State,
    _life: PhantomData<&'l mut Thread<ID_SIZE>>
}

impl<'l, const ID_SIZE: usize> Deref for Managed<'l, ID_SIZE> {
	type Target = Thread;
	fn deref(&self) -> &Self::Target {
		unsafe { &*(self as *const _ as *const Self::Target) }
	}
}

impl<'l, const ID_SIZE: usize> DerefMut for Managed<'l, ID_SIZE> {
	fn deref_mut(&mut self) -> &mut Self::Target {
		unsafe { &mut *(self as *mut _ as *mut Self::Target) }
	}
}

impl<'l> Managed<'l> {
	pub fn restart_gc(&mut self) {
		unsafe { lua_gc(self.l, GcTask::Restart as _) };
	}

	pub fn run_gc(&mut self) {
		unsafe { lua_gc(self.l, GcTask::Collect as _) };
	}

	pub fn step_gc(&mut self, step_size: c_uint) {
		unsafe { lua_gc(self.l, GcTask::Step as _, step_size) };
	}

	pub fn pcall(
		&mut self,
		n_args: c_ushort, n_results: c_ushort,
		err_func: c_int
	) -> ThreadStatus {
		unsafe { ThreadStatus::from_c_int_unchecked(
			lua_pcall(self.l, n_args as _, n_results as _, err_func)
		) }
	}

	pub fn arith(&mut self, operation: Arith) {
		unsafe { lua_arith(self.l, operation as _) }
	}

	pub fn compare(
		&mut self,
		operation: Compare,
		idx_a: c_int, idx_b: c_int
	) -> bool {
		(unsafe { lua_compare(self.l, idx_a, idx_b, operation as _) }) != 0
	}

	pub fn concat(&mut self, n: c_ushort) {
		unsafe { lua_concat(self.l, n as _) }
	}

	pub fn get_i(&mut self, obj_index: c_int, i: Integer) -> Type {
		unsafe { Type::from_c_int_unchecked(lua_geti(self.l, obj_index, i)) }
	}

	pub fn get_table(&mut self, obj_index: c_int) -> Type {
		unsafe { Type::from_c_int_unchecked(lua_gettable(self.l, obj_index)) }
	}

	pub fn length_of(&mut self, index: c_int) {
		unsafe { lua_len(self.l, index) }
	}
}

impl<const ID_SIZE: usize> Thread<ID_SIZE> {
	pub const unsafe fn from_ptr(l: *mut State) -> Self {
		Self {
			l
		}
	}

	pub const fn as_ptr(&self) -> *mut State {
		self.l
	}

	pub fn run_managed<R>(&mut self, func: impl FnOnce(Managed<'_>) -> R) -> R {
		let result = func(Managed {
			l: self.l,
			_life: PhantomData
		});
		self.stop_gc();
		result
	}

	pub unsafe fn close_as_main(&mut self) {
		lua_close(self.l)
	}

	pub fn close_as_coroutine(&mut self) -> ThreadStatus {
		unsafe { ThreadStatus::from_c_int_unchecked(lua_resetthread(self.l)) }
	}

	pub fn status(&self) -> ThreadStatus {
		unsafe { ThreadStatus::from_c_int_unchecked(lua_status(self.l)) }
	}

	pub fn at_panic(
		&self, func: Option<CFunction>
	) -> Option<CFunction> {
		unsafe { lua_atpanic(self.l, func) }
	}

	pub fn version(&self) -> Number {
		unsafe { lua_version(self.l) }
	}

	pub fn stop_gc(&mut self) {
		unsafe { lua_gc(self.l, GcTask::Stop as _) };
	}

	pub fn mem_kbytes(&self) -> c_uint {
		unsafe { lua_gc(self.l, GcTask::CountKbytes as _) }
			.clamp(0, c_int::MAX) as _
	}

	pub fn mem_byte_remainder(&self) -> c_uint {
		unsafe { lua_gc(self.l, GcTask::CountBytesRem as _) }
			.clamp(0, c_int::MAX) as _
	}

	pub fn is_gc_running(&self) -> bool {
		(unsafe { lua_gc(self.l, GcTask::IsRunning as _) }) != 0
	}

	pub fn switch_gc_to(&mut self, gc: Gc) {
		match gc {
			Gc::Incremental { pause, step_multiplier, step_size } => unsafe {
				lua_gc(
					self.l, GcTask::ToIncremental as _,
					pause, step_multiplier, step_size
				)
			},
			Gc::Generational { minor_mul, major_mul } => unsafe {
				lua_gc(self.l, GcTask::ToGenerational as _, minor_mul, major_mul)
			}
		};
	}

	pub fn abs_index(&self, idx: c_int) -> c_int {
		unsafe { lua_absindex(self.l, idx) }
	}

	pub fn top(&self) -> c_int {
		unsafe { lua_gettop(self.l) }
	}

	pub fn type_of(&self, idx: c_int) -> Type {
		unsafe { Type::from_c_int_unchecked(lua_type(self.l, idx)) }
	}

	pub fn type_name<'a>(&'a self, type_tag: Type) -> &'a CStr {
		unsafe { CStr::from_ptr(lua_typename(self.l, type_tag as _)) }
	}

	pub fn to_number(&self, idx: c_int) -> Number {
		unsafe { lua_tonumber(self.l, idx) }
	}

	pub fn to_number_opt(&self, idx: c_int) -> Option<Number> {
		let mut is_num = 0;
		let result = unsafe { lua_tonumberx(self.l, idx, &mut is_num as *mut _) };
		(is_num != 0).then_some(result)
	}

	pub fn to_integer(&self, idx: c_int) -> Integer {
		unsafe { lua_tointeger(self.l, idx) }
	}

	pub fn to_integer_opt(&self, idx: c_int) -> Option<Integer> {
		let mut is_num = 0;
		let result = unsafe { lua_tointegerx(self.l, idx, &mut is_num as *mut _) };
		(is_num != 0).then_some(result)
	}

	pub fn to_boolean(&self, idx: c_int) -> bool {
		(unsafe { lua_toboolean(self.l, idx) }) != 0
	}

	pub fn raw_length(&self, idx: c_int) -> Unsigned {
		unsafe { lua_rawlen(self.l, idx) }
	}

	pub fn to_c_function(&self, idx: c_int) -> Option<CFunction> {
		unsafe { lua_tocfunction(self.l, idx) }
	}

	pub fn to_userdata(&self, idx: c_int) -> *mut c_void {
		unsafe { lua_touserdata(self.l, idx) }
	}

	pub fn to_pointer(&self, idx: c_int) -> *const c_void {
		unsafe { lua_topointer(self.l, idx) }
	}

	pub fn raw_equal(&self, idx_a: c_int, idx_b: c_int) -> bool {
		(unsafe { lua_rawequal(self.l, idx_a, idx_b) }) != 0
	}

	pub fn check_stack(&self, n: c_ushort) -> bool {
		(unsafe { lua_checkstack(self.l, n as _) }) != 0
	}

	pub fn copy(&self, from_idx: c_int, to_idx: c_int) {
		unsafe { lua_copy(self.l, from_idx, to_idx) }
	}

	// FIXME: This function can raise a memory error!!!
	pub unsafe fn create_table(&self, n_arr: c_uint, n_rec: c_uint) {
		unsafe { lua_createtable(self.l, n_arr as _, n_rec as _) }
	}

	// AFAIK this will never call any metamethods.
	pub fn get_global(&self, name: &CStr) -> Type {
		unsafe { Type::from_c_int_unchecked(lua_getglobal(self.l, name.as_ptr())) }
	}

	pub fn get_metatable(&self, obj_index: c_int) -> bool {
		(unsafe { lua_getmetatable(self.l, obj_index) }) != 0
	}

	pub fn get_i_uservalue(&self, ud_index: c_int, n: c_int) -> Type {
		unsafe { Type::from_c_int_unchecked(
			lua_getiuservalue(self.l, ud_index, n)
		) }
	}

	pub fn insert(&self, index: c_int) {
		unsafe { lua_insert(self.l, index) }
	}

	// TODO: lua_is* functions.

	pub fn can_yield(&self) -> bool {
		(unsafe { lua_isyieldable(self.l) }) != 0
	}

	// TODO: Safe `Reader`?
	pub fn load(
		&self,
		reader: Reader, data: *mut c_void,
		chunk_name: &CStr, mode: &CStr
	) -> ThreadStatus {
		unsafe { ThreadStatus::from_c_int_unchecked(
			lua_load(self.l, reader, data, chunk_name.as_ptr(), mode.as_ptr())
		) }
	}

	// FIXME: This function can raise a memory error!!!
	pub unsafe fn new_table(&self) {
		unsafe { lua_newtable(self.l) }
	}

	// TODO: `lua_newthread` function.

	// FIXME: This function can raise a memory error!!!
	pub(crate) unsafe fn new_thread_(&self) -> Thread<ID_SIZE> {
		unsafe { Thread::from_ptr(lua_newthread(self.l)) }
	}

	// FIXME: This function can raise a memory error!!!
	pub unsafe fn new_userdata_uv<'l>(
		&'l self,
		size: usize,
		n_uservalues: c_int
	) -> &'l mut [u8] {
		let udata = unsafe { lua_newuserdatauv(self.l, size, n_uservalues) };
		from_raw_parts_mut(udata as *mut u8, size)
	}

	pub fn push_native_fn(&self, func: CFunction) {
		unsafe { lua_pushcfunction(self.l, func) }
	}
	
	// TODO: `lua_next`.

	pub fn pop(&self, n: c_int) {
		unsafe { lua_pop(self.l, n) }
	}
	
	// TODO: `lua_push*` functions.

	// FIXME: This function can raise a memory error!!!
	pub unsafe fn to_l_string<'l>(&'l self, index: c_int) -> Option<&'l [c_char]> {
		let mut len = 0;
		let str_ptr = unsafe { lua_tolstring(self.l, index, &mut len as *mut _) };
		if !str_ptr.is_null() {
			Some(unsafe { from_raw_parts(str_ptr, len) })
		} else {
			None
		}
	}

	// FIXME: This function can raise a memory error!!!
	pub unsafe fn to_string<'l>(&'l self, index: c_int) -> Option<&'l CStr> {
		let str_ptr = unsafe { lua_tostring(self.l, index) };
		if !str_ptr.is_null() {
			Some(unsafe { CStr::from_ptr(str_ptr) })
		} else {
			None
		}
	}
}

#[cfg(feature = "auxlib")]
impl<const ID_SIZE: usize> Thread<ID_SIZE> {
	pub fn load_string(&self, code: &CStr) -> ThreadStatus {
		unsafe { ThreadStatus::from_c_int_unchecked(
			auxlib::luaL_loadstring(self.l, code.as_ptr())
		) }
	}

	// FIXME: This function can raise an arbitrary error!!!
	pub unsafe fn require(
		&self,
		module_name: &CStr,
		open_fn: CFunction,
		into_global: bool
	) {
		unsafe { auxlib::luaL_requiref(
			self.l,
			module_name.as_ptr(),
			open_fn,
			if into_global { 1 } else { 0 }
		) }
	}
}

#[derive(Debug)]
#[repr(transparent)]
pub struct Lua<const ID_SIZE: usize = DEFAULT_ID_SIZE> {
	thread: Thread<ID_SIZE>
}

impl<const ID_SIZE: usize> Drop for Lua<ID_SIZE> {
	fn drop(&mut self) {
		unsafe { self.thread.close_as_main() }
	}
}

impl<const ID_SIZE: usize> Deref for Lua<ID_SIZE> {
	type Target = Thread<ID_SIZE>;
	fn deref(&self) -> &Self::Target {
		&self.thread
	}
}

impl<const ID_SIZE: usize> DerefMut for Lua<ID_SIZE> {
	fn deref_mut(&mut self) -> &mut Self::Target {
		&mut self.thread
	}
}

impl Lua<DEFAULT_ID_SIZE> {
	#[cfg(feature = "auxlib")]
	pub fn new_auxlib_default() -> Option<Self> {
		Self::new_auxlib()
	}
}

impl<const ID_SIZE: usize> Lua<ID_SIZE> {
	#[cfg(feature = "auxlib")]
	pub fn new_auxlib() -> Option<Self> {
		let l = unsafe { auxlib::luaL_newstate() };
		if !l.is_null() {
			Some(Self {
				thread: unsafe { Thread::from_ptr(l) }
			})
		} else {
			None
		}
	}

	pub unsafe fn from_ptr(l: *mut cdef::State) -> Self {
		let thread = Thread::from_ptr(l);
		thread.at_panic(Some(lua_panic));
		Self {
			thread
		}
	}

	pub const fn as_ptr(&self) -> *mut cdef::State {
		self.thread.as_ptr()
	}

	// FIXME: This function can raise a memory error!!!
	pub unsafe fn new_thread<'l>(&'l self) -> Coroutine<'l, ID_SIZE> {
		Coroutine {
			thread: unsafe { self.thread.new_thread_() },
			_life: PhantomData
		}
	}
}

#[derive(Debug)]
#[repr(transparent)]
pub struct Coroutine<'l, const ID_SIZE: usize = DEFAULT_ID_SIZE> {
	thread: Thread<ID_SIZE>,
	_life: PhantomData<&'l Lua<ID_SIZE>>
}

impl<'l, const ID_SIZE: usize> Coroutine<'l, ID_SIZE> {
	pub fn close(&mut self) -> ThreadStatus {
		self.thread.close_as_coroutine()
	}
}
