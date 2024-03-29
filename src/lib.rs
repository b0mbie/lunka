//! # lunka
//! `#![no_std]` bindings to Lua 5.4.

#![no_std]

use allocator_api2::alloc::{
	AllocError, Allocator, Global
};
use core::alloc::Layout;
use core::ffi::{
	c_char, c_int, c_uint, c_ushort, c_void, CStr
};
use core::marker::PhantomData;
use core::mem::{
	align_of,
	size_of
};
use core::ops::{
	Deref, DerefMut
};
use core::ptr::{
	null, null_mut, write, NonNull
};
use core::slice::{
	from_raw_parts, from_raw_parts_mut
};

#[cfg(doc)]
pub mod errors;

pub mod cdef;
pub use cdef::{
	Number,
	Integer,
	ThreadStatus,
	Type,
	upvalue_index
};

use crate::cdef::*;

/// Lua garbage collection modes enum.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum GcMode {
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

/// Lua thread wrapper that's used by [`Lua`] and associated structures.
/// 
/// [`Lua`], [`Managed`] and [`Coroutine`] implement [`Deref`] to this type.
/// 
/// # Borrowing
/// Most methods borrow instances of this type immutably, even though, at least
/// *in theory*, they should've borrowed mutably.
/// For instance, [`Thread::push_nil`], even though it modifies the Lua stack by
/// pushing a `nil`, still borrows a [`Thread`] immutably.
/// 
/// In the case for this structure, borrowing immutably means **not in any way
/// being able to trigger the GC to collect garbage**.
/// Any references returned by methods for this structure are simply the same
/// pointers that the C API returns, though they are converted to references for
/// the Rust borrow checker to ensure safety.
/// The Lua garbage collector will not invalidate any pointers if it is stopped.
/// [`Lua`] will usually force the garbage collector to stay off with an API
/// call if the code has declared that some pointers must not be invalidated.
/// 
/// To call API functions that can potentially enable the GC, it is required
/// that any references that have been acquired previously from a [`Thread`] are
/// immediately invalidated, so they cannot be used *if* the garbage collector
/// decides to collect them.
/// This is done by borrowing [`Thread`] mutably once, through
/// [`Thread::run_managed`], which allows for more operations.
/// 
/// The main reason for this model existing is because it may be difficult to
/// formally prove that a reference would not be collected without using stack
/// indices. This model simply utilizes checks done at compile time to ensure
/// safety.
/// 
/// # Layout
/// [`Thread`] is guaranteed to have the same layout as a [`*mut State`](State).
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
	panic!("PANIC: unprotected error in call to Lua API ({msg})")
}

/// Context for invalidating pointers that may be freed during garbage
/// collection.
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
	#[inline(always)]
	pub fn restart_gc(&mut self) {
		unsafe { lua_gc(self.l, GcTask::Restart as _) };
	}

	#[inline(always)]
	pub fn run_gc(&mut self) {
		unsafe { lua_gc(self.l, GcTask::Collect as _) };
	}

	#[inline(always)]
	pub fn step_gc(&mut self, step_size: c_uint) {
		unsafe { lua_gc(self.l, GcTask::Step as _, step_size) };
	}

	#[inline(always)]
	pub fn pcall(
		&mut self,
		n_args: c_uint, n_results: c_uint,
		err_func: c_int
	) -> ThreadStatus {
		unsafe { ThreadStatus::from_c_int_unchecked(
			lua_pcall(self.l, n_args as _, n_results as _, err_func)
		) }
	}

	/// # Safety
	/// The underlying Lua state may raise an arbitrary [error](crate::errors).
	#[inline(always)]
	pub unsafe fn arith(&mut self, operation: Arith) {
		unsafe { lua_arith(self.l, operation as _) }
	}

	/// # Safety
	/// The underlying Lua state may raise an arbitrary [error](crate::errors).
	#[inline(always)]
	pub unsafe fn compare(
		&mut self,
		operation: Compare,
		idx_a: c_int, idx_b: c_int
	) -> bool {
		(unsafe { lua_compare(self.l, idx_a, idx_b, operation as _) }) != 0
	}

	/// # Safety
	/// The underlying Lua state may raise an arbitrary [error](crate::errors).
	#[inline(always)]
	pub unsafe fn concat(&mut self, n: c_uint) {
		unsafe { lua_concat(self.l, n as _) }
	}

	/// # Safety
	/// The underlying Lua state may raise an arbitrary [error](crate::errors).
	#[inline(always)]
	pub unsafe fn get_i(&mut self, obj_index: c_int, i: Integer) -> Type {
		unsafe { Type::from_c_int_unchecked(lua_geti(self.l, obj_index, i)) }
	}

	/// # Safety
	/// The underlying Lua state may raise an arbitrary [error](crate::errors).
	#[inline(always)]
	pub unsafe fn get_table(&mut self, obj_index: c_int) -> Type {
		unsafe { Type::from_c_int_unchecked(lua_gettable(self.l, obj_index)) }
	}

	/// # Safety
	/// The underlying Lua state may raise an arbitrary [error](crate::errors).
	#[inline(always)]
	pub unsafe fn length_of(&mut self, index: c_int) {
		unsafe { lua_len(self.l, index) }
	}

	/// # Safety
	/// The underlying Lua state may raise an arbitrary [error](crate::errors).
	#[cfg(feature = "stdlibs")]
	#[inline(always)]
	pub unsafe fn open_libs(&mut self) {
		unsafe { stdlibs::luaL_openlibs(self.l) }
	}

	/// # Safety
	/// The underlying Lua state may raise an arbitrary [error](crate::errors).
	#[inline(always)]
	pub unsafe fn set_field(&self, obj_index: c_int, key: &CStr) {
		unsafe { lua_setfield(self.l, obj_index, key.as_ptr()) }
	}

	/// # Safety
	/// The underlying Lua state may raise an arbitrary [error](crate::errors).
	#[inline(always)]
	pub unsafe fn set_i(&self, obj_index: c_int, i: Integer) {
		unsafe { lua_seti(self.l, obj_index, i) }
	}
}

macro_rules! lua_is {
	(
		@bool
		$(#[$attr:meta])*
		$vis:vis fn $name:ident(&self, index: c_int) -> bool
		for $ffi_fn:ident
	) => {
		$(#[$attr])*
		$vis fn $name(&self, index: c_int) -> bool {
			unsafe { $ffi_fn(self.l, index) }
		}
	};

	(
		@c_int
		$(#[$attr:meta])*
		$vis:vis fn $name:ident(&self, index: c_int) -> bool
		for $ffi_fn:ident
	) => {
		$(#[$attr])*
		$vis fn $name(&self, index: c_int) -> bool {
			(unsafe { $ffi_fn(self.l, index) }) != 0
		}
	};

	(
		$(
			$(#[$attr:meta])*
			$vis:vis fn $name:ident(&self, index: c_int) -> bool
			for $ffi_fn:ident -> $ffi_fn_ret:tt;
		)*
	) => {
		$(
			lua_is!{
				@ $ffi_fn_ret
				$(#[$attr])*
				$vis fn $name(&self, index: c_int) -> bool
				for $ffi_fn
			}
		)*
	};
}

impl<const ID_SIZE: usize> Thread<ID_SIZE> {
	#[inline(always)]
	pub const unsafe fn from_ptr(l: *mut State) -> Self {
		Self {
			l
		}
	}

	#[inline(always)]
	pub const fn as_ptr(&self) -> *mut State {
		self.l
	}

	#[inline(always)]
	pub fn run_managed<R>(&mut self, func: impl FnOnce(Managed<'_>) -> R) -> R {
		let result = func(Managed {
			l: self.l,
			_life: PhantomData
		});
		self.stop_gc();
		result
	}

	/// This is the same as [`Thread::run_managed`], however it doesn't borrow
	/// mutably by assuming that the garbage collector will not collect (and
	/// thus invalidate) any outside references.
	/// 
	/// # Safety
	/// The body of `func` must not include any operations that may cause the
	/// garbage collector to run a cycle.
	/// 
	/// For example, if performing arithmetic on numbers does not trigger any
	/// metamethods, or it triggers metamethods that can't ever cause the
	/// collector to collect, then this invariant is not broken.
	#[inline(always)]
	pub fn run_managed_no_gc<R>(&self, func: impl FnOnce(Managed<'_>) -> R) -> R {
		func(Managed {
			l: self.l,
			_life: PhantomData
		})
	}

	#[inline(always)]
	pub unsafe fn close_as_main(&mut self) {
		lua_close(self.l)
	}

	#[inline(always)]
	pub fn close_as_coroutine(&mut self) -> ThreadStatus {
		unsafe { ThreadStatus::from_c_int_unchecked(lua_resetthread(self.l)) }
	}

	#[inline(always)]
	pub fn at_panic(
		&self, func: Option<CFunction>
	) -> Option<CFunction> {
		unsafe { lua_atpanic(self.l, func) }
	}

	#[inline(always)]
	pub fn error(&self) -> ! {
		unsafe { lua_error(self.l) }
	}

	#[inline(always)]
	pub fn stop_gc(&mut self) {
		unsafe { lua_gc(self.l, GcTask::Stop as _) };
	}

	#[inline(always)]
	pub fn mem_kbytes(&self) -> c_uint {
		unsafe { lua_gc(self.l, GcTask::CountKbytes as _) }
			.clamp(0, c_int::MAX) as _
	}

	#[inline(always)]
	pub fn mem_byte_remainder(&self) -> c_uint {
		unsafe { lua_gc(self.l, GcTask::CountBytesRem as _) }
			.clamp(0, c_int::MAX) as _
	}

	#[inline(always)]
	pub fn is_gc_running(&self) -> bool {
		(unsafe { lua_gc(self.l, GcTask::IsRunning as _) }) != 0
	}

	#[inline(always)]
	pub fn switch_gc_to(&mut self, gc: GcMode) {
		match gc {
			GcMode::Incremental { pause, step_multiplier, step_size } => unsafe {
				lua_gc(
					self.l, GcTask::ToIncremental as _,
					pause, step_multiplier, step_size
				)
			},
			GcMode::Generational { minor_mul, major_mul } => unsafe {
				lua_gc(self.l, GcTask::ToGenerational as _, minor_mul, major_mul)
			}
		};
	}

	#[inline(always)]
	pub fn abs_index(&self, idx: c_int) -> c_int {
		unsafe { lua_absindex(self.l, idx) }
	}

	#[inline(always)]
	pub fn check_stack(&self, n: c_uint) -> bool {
		(unsafe { lua_checkstack(self.l, n as _) }) != 0
	}

	#[inline(always)]
	pub fn copy(&self, from_idx: c_int, to_idx: c_int) {
		unsafe { lua_copy(self.l, from_idx, to_idx) }
	}

	/// # Safety
	/// The underlying Lua state may raise a memory [error](crate::errors).
	#[inline(always)]
	pub unsafe fn create_table(&self, n_arr: c_uint, n_rec: c_uint) {
		unsafe { lua_createtable(self.l, n_arr as _, n_rec as _) }
	}

	#[inline(always)]
	pub fn get_alloc_fn(&self) -> (Alloc, *mut c_void) {
		let mut ud = null_mut();
		let alloc_fn = unsafe { lua_getallocf(
			self.l, &mut ud as *mut *mut c_void
		) };
		(alloc_fn, ud)
	}

	/// # Safety
	/// The underlying Lua state may raise an arbitrary [error](crate::errors).
	#[inline(always)]
	pub unsafe fn get_global(&self, name: &CStr) -> Type {
		unsafe { Type::from_c_int_unchecked(lua_getglobal(self.l, name.as_ptr())) }
	}

	// NOTE: In C `n` is `int`, however Lua uses it as an `unsigned short`.
	#[inline(always)]
	pub fn get_i_uservalue(&self, ud_index: c_int, n: c_ushort) -> Type {
		unsafe { Type::from_c_int_unchecked(
			lua_getiuservalue(self.l, ud_index, n as _)
		) }
	}

	#[inline(always)]
	pub fn get_metatable(&self, obj_index: c_int) -> bool {
		(unsafe { lua_getmetatable(self.l, obj_index) }) != 0
	}

	#[inline(always)]
	pub fn top(&self) -> c_int {
		unsafe { lua_gettop(self.l) }
	}

	#[inline(always)]
	pub fn insert(&self, index: c_int) {
		unsafe { lua_insert(self.l, index) }
	}

	lua_is! {
		#[inline(always)]
		pub fn is_boolean(&self, index: c_int) -> bool for lua_isboolean -> bool;
		#[inline(always)]
		pub fn is_c_function(&self, index: c_int) -> bool
			for lua_iscfunction -> c_int;
		#[inline(always)]
		pub fn is_function(&self, index: c_int) -> bool
			for lua_isfunction -> bool;
		#[inline(always)]
		pub fn is_integer(&self, index: c_int) -> bool
			for lua_isinteger -> c_int;
		#[inline(always)]
		pub fn is_light_userdata(&self, index: c_int) -> bool
			for lua_islightuserdata -> bool;
		#[inline(always)]
		pub fn is_nil(&self, index: c_int) -> bool for lua_isnil -> bool;
		#[inline(always)]
		pub fn is_none(&self, index: c_int) -> bool for lua_isnone -> bool;
		#[inline(always)]
		pub fn is_none_or_nil(&self, index: c_int) -> bool
			for lua_isnoneornil -> bool;
		#[inline(always)]
		pub fn is_number(&self, index: c_int) -> bool for lua_isnumber -> c_int;
		#[inline(always)]
		pub fn is_string(&self, index: c_int) -> bool for lua_isstring -> c_int;
		#[inline(always)]
		pub fn is_table(&self, index: c_int) -> bool for lua_istable -> bool;
		#[inline(always)]
		pub fn is_thread(&self, index: c_int) -> bool for lua_isthread -> bool;
		#[inline(always)]
		pub fn is_userdata(&self, index: c_int) -> bool
			for lua_isuserdata -> c_int;
	}

	#[inline(always)]
	pub fn can_yield(&self) -> bool {
		(unsafe { lua_isyieldable(self.l) }) != 0
	}

	// TODO: Safe `Reader`?
	#[inline(always)]
	pub fn load(
		&self,
		reader: Reader, data: *mut c_void,
		chunk_name: &CStr, mode: &CStr
	) -> ThreadStatus {
		unsafe { ThreadStatus::from_c_int_unchecked(
			lua_load(self.l, reader, data, chunk_name.as_ptr(), mode.as_ptr())
		) }
	}

	/// # Safety
	/// The underlying Lua state may raise a memory [error](crate::errors).
	#[inline(always)]
	pub unsafe fn new_table(&self) {
		unsafe { lua_newtable(self.l) }
	}

	/// # Safety
	/// The underlying Lua state may raise a memory [error](crate::errors).
	#[inline(always)]
	pub unsafe fn new_thread<'l>(&'l self) -> Coroutine<'l, ID_SIZE> {
		Coroutine {
			thread: unsafe { Thread::from_ptr(lua_newthread(self.l)) },
			_life: PhantomData
		}
	}

	/// # Safety
	/// The underlying Lua state may raise a memory [error](crate::errors).
	// NOTE: In C `n_uservalues` is `int`, however Lua uses it as an
	// `unsigned short`.
	#[inline(always)]
	pub unsafe fn new_userdata_uv<'l>(
		&'l self,
		size: usize,
		n_uservalues: c_ushort
	) -> &'l mut [u8] {
		let udata = unsafe { lua_newuserdatauv(self.l, size, n_uservalues as _) };
		from_raw_parts_mut(udata as *mut u8, size)
	}

	/// Similar to [`Thread::new_userdata_uv`], but takes an already existing
	/// value and writes it to the allocated userdata.
	/// 
	/// This function does not give a finalizer for the userdata, so `T` must be
	/// [`Copy`].
	/// 
	/// # Safety
	/// The underlying Lua state may raise a memory [error](crate::errors).
	// NOTE: In C `n_uservalues` is `int`, however Lua uses it as an
	// `unsigned short`.
	#[inline(always)]
	pub unsafe fn new_copy_t<'l, T: Copy>(
		&'l self, value: T, n_uservalues: c_ushort
	) -> &'l mut T {
		let udata = unsafe { lua_newuserdatauv(
			self.l, size_of::<T>(), n_uservalues as _
		) } as *mut T;
		unsafe { write(udata, value) };
		unsafe { &mut *udata }
	}
	
	/// # Safety
	/// The underlying Lua state may raise an [error](crate::errors) if a given
	/// key is neither `nil` nor present in the table.
	#[inline(always)]
	pub unsafe fn next(&self, index: c_int) -> bool {
		(unsafe { lua_next(self.l, index) }) != 0
	}

	#[inline(always)]
	pub fn pop(&self, n: c_int) {
		unsafe { lua_pop(self.l, n) }
	}

	#[inline(always)]
	pub fn push_boolean(&self, value: bool) {
		unsafe { lua_pushboolean(self.l, if value { 1 } else { 0 }) }
	}

	/// # Safety
	/// The underlying Lua state may raise a memory [error](crate::errors).
	// NOTE: `n_upvalues` is a C `int`, however Lua uses it as a byte.
	#[inline(always)]
	pub unsafe fn push_c_closure(&self, func: CFunction, n_upvalues: u8) {
		unsafe { lua_pushcclosure(self.l, func, n_upvalues as _) }
	}

	#[inline(always)]
	pub fn push_c_function(&self, func: CFunction) {
		unsafe { lua_pushcfunction(self.l, func) }
	}

	#[inline(always)]
	pub fn push_global_table(&self) {
		unsafe { lua_pushglobaltable(self.l) }
	}

	#[inline(always)]
	pub fn push_integer(&self, value: Integer) {
		unsafe { lua_pushinteger(self.l, value) }
	}

	#[inline(always)]
	pub fn push_light_userdata(&self, ptr: *mut c_void) {
		unsafe { lua_pushlightuserdata(self.l, ptr) }
	}

	/// # Safety
	/// The underlying Lua state may raise a memory [error](crate::errors).
	#[inline(always)]
	pub unsafe fn push_chars<'l>(&'l self, data: &[c_char]) -> &'l [c_char] {
		let length = data.len();
		unsafe { from_raw_parts(
			lua_pushlstring(self.l, data.as_ptr(), length),
			length
		) }
	}

	/// Works the same as [`Thread::push_chars`], however it accepts [`u8`]s
	/// instead of [`c_char`]s.
	/// 
	/// # Safety
	/// The underlying Lua state may raise a memory [error](crate::errors).
	#[inline(always)]
	pub unsafe fn push_byte_str<'l>(&'l self, data: &[u8]) -> &'l [u8] {
		let length = data.len();
		unsafe { from_raw_parts(
			lua_pushlstring(
				self.l,
				data.as_ptr() as *const _, length
			) as *const _,
			length
		) }
	}

	#[inline(always)]
	pub fn push_nil(&self) {
		unsafe { lua_pushnil(self.l) }
	}

	/// # Safety
	/// The underlying Lua state may raise a memory [error](crate::errors).
	#[inline(always)]
	pub unsafe fn push_string<'l>(&'l self, data: &CStr) -> &'l CStr {
		unsafe { CStr::from_ptr(
			lua_pushstring(self.l, data.as_ptr())
		) }
	}

	#[inline(always)]
	pub fn push_thread(&self) -> bool {
		(unsafe { lua_pushthread(self.l) }) != 0
	}

	#[inline(always)]
	pub fn push_value(&self, index: c_int) {
		unsafe { lua_pushvalue(self.l, index) }
	}

	#[inline(always)]
	pub fn raw_equal(&self, idx_a: c_int, idx_b: c_int) -> bool {
		(unsafe { lua_rawequal(self.l, idx_a, idx_b) }) != 0
	}

	#[inline(always)]
	pub fn raw_get(&self, tbl_index: c_int) -> Type {
		unsafe { Type::from_c_int_unchecked(
			lua_rawget(self.l, tbl_index)
		) }
	}

	#[inline(always)]
	pub fn raw_get_i(&self, tbl_index: c_int, i: Integer) -> Type {
		unsafe { Type::from_c_int_unchecked(
			lua_rawgeti(self.l, tbl_index, i)
		) }
	}

	#[inline(always)]
	pub fn raw_get_p(&self, tbl_index: c_int, ptr: *const c_void) -> Type {
		unsafe { Type::from_c_int_unchecked(
			lua_rawgetp(self.l, tbl_index, ptr)
		) }
	}

	#[inline(always)]
	pub fn raw_length(&self, index: c_int) -> Unsigned {
		unsafe { lua_rawlen(self.l, index) }
	}

	/// # Safety
	/// The underlying Lua state may raise a memory [error](crate::errors).
	#[inline(always)]
	pub unsafe fn raw_set(&self, tbl_index: c_int) {
		unsafe { lua_rawset(self.l, tbl_index) }
	}

	/// # Safety
	/// The underlying Lua state may raise a memory [error](crate::errors).
	#[inline(always)]
	pub unsafe fn raw_set_i(&self, tbl_index: c_int, i: Integer) {
		unsafe { lua_rawseti(self.l, tbl_index, i) }
	}

	/// # Safety
	/// The underlying Lua state may raise a memory [error](crate::errors).
	#[inline(always)]
	pub unsafe fn raw_set_p(&self, tbl_index: c_int, ptr: *const c_void) {
		unsafe { lua_rawsetp(self.l, tbl_index, ptr) }
	}

	/// # Safety
	/// The underlying Lua state may raise an arbitrary [error](crate::errors).
	#[inline(always)]
	pub unsafe fn register(&self, name: &CStr, func: CFunction) {
		unsafe { lua_register(self.l, name.as_ptr(), func) }
	}

	#[inline(always)]
	pub fn replace(&self, index: c_int) {
		unsafe { lua_replace(self.l, index) }
	}

	#[inline(always)]
	pub fn resume(
		&self, from: &Thread,
		n_args: c_int
	) -> (ThreadStatus, c_int) {
		let mut n_res = 0;
		let status = unsafe { lua_resume(
			self.l, from.as_ptr(),
			n_args,
			&mut n_res as *mut _
		) };
		(unsafe { ThreadStatus::from_c_int_unchecked(status) }, n_res)
	}

	#[inline(always)]
	pub fn rotate(&self, index: c_int, n_values: c_int) {
		unsafe { lua_rotate(self.l, index, n_values) }
	}

	/// # Safety
	/// The underlying Lua state may raise an arbitrary [error](crate::errors).
	#[inline(always)]
	pub unsafe fn set_global(&self, key: &CStr) {
		unsafe { lua_setglobal(self.l, key.as_ptr()) }
	}

	// NOTE: In C `n` is `int`, however Lua uses it as an `unsigned short`.
	#[inline(always)]
	pub fn set_i_uservalue(&self, ud_index: c_int, n: c_ushort) -> bool {
		(unsafe { lua_setiuservalue(self.l, ud_index, n as _) }) != 0
	}

	// NOTE: `lua_setmetatable` always returns a `1`, which isn't useful.
	#[inline(always)]
	pub fn set_metatable(&self, obj_index: c_int) {
		unsafe { lua_setmetatable(self.l, obj_index) };
	}

	#[inline(always)]
	pub fn set_warn_fn(&self, func: Option<WarnFunction>, ud: *mut c_void) {
		unsafe { lua_setwarnf(self.l, func, ud) }
	}

	#[inline(always)]
	pub fn status(&self) -> ThreadStatus {
		unsafe { ThreadStatus::from_c_int_unchecked(lua_status(self.l)) }
	}

	#[inline(always)]
	pub fn to_boolean(&self, idx: c_int) -> bool {
		(unsafe { lua_toboolean(self.l, idx) }) != 0
	}

	#[inline(always)]
	pub fn to_c_function(&self, index: c_int) -> Option<CFunction> {
		unsafe { lua_tocfunction(self.l, index) }
	}

	#[inline(always)]
	pub fn to_integer(&self, idx: c_int) -> Integer {
		unsafe { lua_tointeger(self.l, idx) }
	}

	#[inline(always)]
	pub fn to_integer_opt(&self, idx: c_int) -> Option<Integer> {
		let mut is_num = 0;
		let result = unsafe { lua_tointegerx(self.l, idx, &mut is_num as *mut _) };
		(is_num != 0).then_some(result)
	}

	/// # Safety
	/// The underlying Lua state may raise a memory [error](crate::errors).
	#[inline(always)]
	pub unsafe fn to_chars<'l>(
		&'l self, index: c_int
	) -> Option<&'l [c_char]> {
		let mut len = 0;
		let str_ptr = unsafe { lua_tolstring(self.l, index, &mut len as *mut _) };
		if !str_ptr.is_null() {
			Some(unsafe { from_raw_parts(str_ptr, len) })
		} else {
			None
		}
	}

	#[inline(always)]
	pub fn to_number(&self, idx: c_int) -> Number {
		unsafe { lua_tonumber(self.l, idx) }
	}

	#[inline(always)]
	pub fn to_number_opt(&self, idx: c_int) -> Option<Number> {
		let mut is_num = 0;
		let result = unsafe { lua_tonumberx(self.l, idx, &mut is_num as *mut _) };
		(is_num != 0).then_some(result)
	}

	#[inline(always)]
	pub fn to_pointer(&self, idx: c_int) -> *const c_void {
		unsafe { lua_topointer(self.l, idx) }
	}

	/// # Safety
	/// The underlying Lua state may raise a memory [error](crate::errors).
	#[inline(always)]
	pub unsafe fn to_string<'l>(&'l self, index: c_int) -> Option<&'l CStr> {
		let str_ptr = unsafe { lua_tostring(self.l, index) };
		if !str_ptr.is_null() {
			Some(unsafe { CStr::from_ptr(str_ptr) })
		} else {
			None
		}
	}

	#[inline(always)]
	pub fn to_thread<'l>(&'l self, index: c_int) -> Option<Coroutine<'l, ID_SIZE>> {
		let l_ptr = unsafe { lua_tothread(self.l, index) };
		if !l_ptr.is_null() {
			Some(Coroutine {
				thread: unsafe { Thread::from_ptr(l_ptr) },
				_life: PhantomData
			})
		} else {
			None
		}
	}

	#[inline(always)]
	pub fn to_userdata(&self, idx: c_int) -> *mut c_void {
		unsafe { lua_touserdata(self.l, idx) }
	}

	#[inline(always)]
	pub fn type_of(&self, idx: c_int) -> Type {
		unsafe { Type::from_c_int_unchecked(lua_type(self.l, idx)) }
	}

	#[inline(always)]
	pub fn type_name<'a>(&'a self, type_tag: Type) -> &'a CStr {
		unsafe { CStr::from_ptr(lua_typename(self.l, type_tag as _)) }
	}

	#[inline(always)]
	pub fn version(&self) -> Number {
		unsafe { lua_version(self.l) }
	}

	#[inline(always)]
	pub fn warning(&self, message: &CStr, to_be_continued: bool) {
		unsafe { lua_warning(
			self.l, message.as_ptr(), if to_be_continued { 1 } else { 0 }
		) }
	}

	#[inline(always)]
	pub fn xmove(&self, to: &Thread, n_values: c_uint) {
		unsafe { lua_xmove(self.l, to.as_ptr(), n_values as _) }
	}

	// TODO: Safety.
	#[inline(always)]
	pub unsafe fn yield_with(&self, n_results: c_int) -> ! {
		unsafe { lua_yield(self.l, n_results) }
	}

	// TODO: Safety.
	#[inline(always)]
	pub unsafe fn yield_in_hook_with(&self, n_results: c_int) {
		unsafe { lua_yield_in_hook(self.l, n_results) };
	}

	// TODO: Safety.
	#[inline(always)]
	pub unsafe fn yield_continue_with(
		&self, n_results: c_int,
		continuation: KFunction, context: KContext
	) -> ! {
		unsafe { lua_yieldk(self.l, n_results, context, Some(continuation)) }
	}

	// TODO: Safety.
	#[inline(always)]
	pub unsafe fn yield_in_hook_continue_with(
		&self, n_results: c_int,
		continuation: KFunction, context: KContext
	) {
		unsafe { lua_yieldk_in_hook(
			self.l, n_results,
			context, Some(continuation)
		) };
	}

	#[inline(always)]
	pub fn hook(&self) -> Hook<ID_SIZE> {
		unsafe { lua_gethook(self.l) }
	}

	#[inline(always)]
	pub fn hook_count(&self) -> c_int {
		unsafe { lua_gethookcount(self.l) }
	}

	#[inline(always)]
	pub fn hook_mask(&self) -> HookMask {
		unsafe { HookMask::from_c_int_unchecked(lua_gethookmask(self.l)) }
	}

	#[inline(always)]
	pub fn get_info(&self, what: &CStr, ar: &mut Debug<ID_SIZE>) -> bool {
		(unsafe { lua_getinfo(self.l, what.as_ptr(), ar) }) != 0
	}

	#[inline(always)]
	pub fn get_local<'dbg>(
		&self,
		ar: &'dbg Debug<ID_SIZE>, n: c_int
	) -> &'dbg CStr {
		unsafe { CStr::from_ptr(lua_getlocal(self.l, ar, n)) }
	}

	#[inline(always)]
	pub fn get_upvalue<'l>(&'l self, func_index: c_int, n: c_int) -> &'l CStr {
		unsafe { CStr::from_ptr(lua_getupvalue(self.l, func_index, n)) }
	}

	#[inline(always)]
	pub fn set_hook(&self, hook: Hook<ID_SIZE>, mask: HookMask, count: c_int) {
		unsafe { lua_sethook(self.l, hook, mask.into_c_int(), count) }
	}

	#[inline(always)]
	pub fn set_local<'dbg>(
		&self,
		ar: &'dbg Debug<ID_SIZE>, n: c_int
	) -> &'dbg CStr {
		unsafe { CStr::from_ptr(lua_setlocal(self.l, ar, n)) }
	}

	#[inline(always)]
	pub fn set_upvalue<'l>(&'l self, func_index: c_int, n: c_int) -> &'l CStr {
		unsafe { CStr::from_ptr(lua_setupvalue(self.l, func_index, n)) }
	}

	#[inline(always)]
	pub fn upvalue_id(&self, func_index: c_int, n: c_int) -> *mut c_void {
		unsafe { lua_upvalueid(self.l, func_index, n) }
	}

	#[inline(always)]
	pub fn upvalue_join(
		&self,
		func_into_index: i32, n_into: i32,
		func_from_index: i32, n_from: i32
	) {
		unsafe { lua_upvaluejoin(
			self.l,
			func_into_index, n_into,
			func_from_index, n_from
		) }
	}
}

unsafe impl Allocator for Lua {
	fn allocate(&self, layout: Layout) -> Result<NonNull<[u8]>, AllocError> {
		let (alloc, ud) = self.get_alloc_fn();
		let len = layout.size();
		NonNull::new(unsafe { alloc(ud, null_mut(), 0, len) } as *mut u8)
			.map(|ptr| NonNull::slice_from_raw_parts(ptr, len))
			.ok_or(AllocError)
	}

	unsafe fn deallocate(&self, ptr: NonNull<u8>, layout: Layout) {
		let (alloc, ud) = self.get_alloc_fn();
		unsafe { alloc(ud, ptr.as_ptr() as *mut c_void, layout.size(), 0) };
	}
}

#[cfg(feature = "auxlib")]
impl<const ID_SIZE: usize> Thread<ID_SIZE> {
	#[inline(always)]
	pub fn new_buffer<'l>(&'l self) -> auxlib::Buffer<'l> {
		unsafe { auxlib::Buffer::new_in_raw(self.l) }
	}

	#[inline(always)]
	pub fn error_str(&self, message: &CStr) -> ! {
		unsafe { auxlib::luaL_error(
			self.l,
			CStr::from_bytes_with_nul_unchecked(b"%s\0").as_ptr(),
			message.as_ptr()
		) }
	}

	#[inline(always)]
	pub fn load_file(&self, code: &CStr) -> ThreadStatus {
		unsafe { ThreadStatus::from_c_int_unchecked(
			auxlib::luaL_loadfile(self.l, code.as_ptr())
		) }
	}

	#[inline(always)]
	pub fn load_stdin(&self) -> ThreadStatus {
		unsafe { ThreadStatus::from_c_int_unchecked(
			auxlib::luaL_loadfile(self.l, null())
		) }
	}

	#[inline(always)]
	pub fn load_string(&self, code: &CStr) -> ThreadStatus {
		unsafe { ThreadStatus::from_c_int_unchecked(
			auxlib::luaL_loadstring(self.l, code.as_ptr())
		) }
	}

	/// # Safety
	/// The underlying Lua state may raise a memory [error](crate::errors).
	#[inline(always)]
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

	#[inline(always)]
	pub fn type_name_of<'l>(&'l self, index: c_int) -> &'l CStr {
		unsafe { CStr::from_ptr(auxlib::luaL_typename(self.l, index)) }
	}
}

/// Data structure that represents a main Lua thread.
/// 
/// Unlike [`Coroutine`], this data structure has a [`Drop`] implementation that
/// automatically closes (frees) the Lua state.
/// 
/// # Layout
/// [`Lua`] is guaranteed to have the same layout as [`Thread`].
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

#[cfg(feature = "auxlib")]
impl Lua<DEFAULT_ID_SIZE> {
	pub fn new_auxlib_default() -> Option<Self> {
		Self::new_auxlib()
	}
}

impl<const ID_SIZE: usize> Lua<ID_SIZE> {
	#[inline(always)]
	unsafe fn from_l(l: *mut State) -> Option<Self> {
		if !l.is_null() {
			Some(Self {
				thread: unsafe { Thread::from_ptr(l) }
			})
		} else {
			None
		}
	}

	#[cfg(feature = "auxlib")]
	#[inline(always)]
	pub fn new_auxlib() -> Option<Self> {
		unsafe { Self::from_l(auxlib::luaL_newstate()) }
	}

	#[inline(always)]
	pub fn new() -> Option<Self> {
		// TODO: Is this right for emulating `malloc`?
		unsafe extern "C" fn l_alloc(
			_ud: *mut c_void,
			ptr: *mut c_void, osize: usize,
			nsize: usize
		) -> *mut c_void {
			if let Some(alloc_ptr) = NonNull::new(ptr as *mut u8) {
				if nsize <= 0 {
					Global.deallocate(
						alloc_ptr,
						Layout::from_size_align_unchecked(
							osize, align_of::<usize>()
						)
					);
					null_mut()
				} else {
					let old_layout = Layout::from_size_align_unchecked(
						osize, align_of::<usize>()
					);
					let new_layout = Layout::from_size_align_unchecked(
						nsize, align_of::<usize>()
					);
	
					if nsize > osize {
						Global.grow(alloc_ptr, old_layout, new_layout)
							.map(|mut ptr| {
								ptr.as_mut().as_mut_ptr() as *mut c_void
							})
							.unwrap_or(null_mut())
					} else if nsize < osize {
						Global.shrink(alloc_ptr, old_layout, new_layout)
							.map(|mut ptr| {
								ptr.as_mut().as_mut_ptr() as *mut c_void
							})
							.unwrap_or(null_mut())
					} else {
						ptr
					}
				}
			} else {
				debug_assert!(nsize > 0);
				Global.allocate(Layout::from_size_align_unchecked(
					nsize, align_of::<usize>()
				))
					.map(|ptr| (*ptr.as_ptr()).as_mut_ptr() as *mut c_void)
					.unwrap_or(null_mut())
			}
		}

		unsafe { Self::from_l(lua_newstate(l_alloc, null_mut())) }
	}

	#[inline(always)]
	pub unsafe fn from_ptr(l: *mut cdef::State) -> Self {
		let thread = Thread::from_ptr(l);
		thread.at_panic(Some(lua_panic));
		Self {
			thread
		}
	}

	#[inline(always)]
	pub const fn as_ptr(&self) -> *mut cdef::State {
		self.thread.as_ptr()
	}
}

/// Data structure that represents a Lua coroutine.
/// 
/// See also [`Lua`] for the main thread.
/// 
/// This type does not have a [`Drop`] implementation.
/// Any threads that are not used anymore must either be closed manually with
/// [`Coroutine::close`] or left to be garbage-collected by Lua.
/// 
/// # Layout
/// [`Coroutine`] is guaranteed to have the same layout as [`Thread`].
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
