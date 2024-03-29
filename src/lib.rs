//! # lunka
//! `#![no_std]` bindings to Lua 5.4.

#![no_std]

// Important notes:
// - Upvalues are presented as `int`s, however Lua uses them in `lu_byte`s.
// - Uservalue indices are presented as `int`s, however Lua uses them in
// `unsigned short`s.

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

#[cfg(feature = "auxlib")]
pub mod aux_options;
pub mod cdef;
pub use cdef::{
	Number,
	Integer,
	Status,
	Type,
	upvalue_index
};
#[cfg(feature = "auxlib")]
pub mod reg;

use crate::cdef::*;

#[cfg(feature = "auxlib")]
use auxlib::*;

#[cfg(feature = "auxlib")]
pub use {
	auxlib::Reg,
	aux_options::*,
	reg::*
};

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
	panic!("unprotected error in call to Lua API ({msg})")
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

impl<'l, const ID_SIZE: usize> Managed<'l, ID_SIZE> {
	/// Perform an arithmetic or bitwise operation over two (or one) values at
	/// the top of the stack, popping them, and push the result of the operation.
	/// 
	/// The value on the top is the second operand, and the value just below it
	/// is the first operand.
	/// 
	/// This function follows the semantics of the corresponding Lua operator
	/// (that is, it may call metamethods).
	/// 
	/// # Safety
	/// The underlying Lua state may raise an arbitrary [error](crate::errors)
	/// from a metamethod.
	#[inline(always)]
	pub unsafe fn arith(&mut self, operation: Arith) {
		unsafe { lua_arith(self.l, operation as _) }
	}

	/// Compare two Lua values.
	/// 
	/// Returns `true` if the value at `idx_a` satisfies `operation` when
	/// compared with the value at index `idx_b`, following the semantics of the
	/// corresponding Lua operator (that is, it may call metamethods).
	/// Otherwise returns `false`.
	/// Also returns `false` if any of the indices are not valid.
	/// 
	/// # Safety
	/// The underlying Lua state may raise an arbitrary [error](crate::errors)
	/// from a metamethod.
	#[inline(always)]
	pub unsafe fn compare(
		&mut self,
		operation: Compare,
		idx_a: c_int, idx_b: c_int
	) -> bool {
		(unsafe { lua_compare(self.l, idx_a, idx_b, operation as _) }) != 0
	}

	/// Concatenate `n` values at the top of the stack, popping them, and leave
	/// the result on the top.
	/// 
	/// If `n` is `1`, the result is the single value on the stack (that is, the
	/// function does nothing).
	/// 
	/// If `n` is `0`, the result is an empty string.
	/// 
	/// Concatenation is performed following the usual semantics of Lua.
	/// 
	/// # Safety
	/// The underlying Lua state may raise an arbitrary [error](crate::errors)
	/// from a metamethod.
	#[inline(always)]
	pub unsafe fn concat(&mut self, n: c_uint) {
		unsafe { lua_concat(self.l, n as _) }
	}

	/// Restart the garbage collector.
	#[inline(always)]
	pub fn restart_gc(&mut self) {
		unsafe { lua_gc(self.l, GcTask::Restart as _) };
	}

	/// Perform a full garbage collection cycle.
	#[inline(always)]
	pub fn run_gc(&mut self) {
		unsafe { lua_gc(self.l, GcTask::Collect as _) };
	}

	/// Perform an incremental step of garbage collection, corresponding to the
	/// allocation of `stepsize` kilobytes. 
	#[inline(always)]
	pub fn step_gc(&mut self, step_size: c_uint) {
		unsafe { lua_gc(self.l, GcTask::Step as _, step_size) };
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

	#[inline(always)]
	pub fn pcall(
		&mut self,
		n_args: c_uint, n_results: c_uint,
		err_func: c_int
	) -> Status {
		unsafe { Status::from_c_int_unchecked(
			lua_pcall(self.l, n_args as _, n_results as _, err_func)
		) }
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

#[cfg(feature = "stdlibs")]
impl<'l, const ID_SIZE: usize> Managed<'l, ID_SIZE> {
	/// # Safety
	/// The underlying Lua state may raise an arbitrary [error](crate::errors).
	#[inline(always)]
	pub unsafe fn open_libs(&mut self) {
		unsafe { stdlibs::luaL_openlibs(self.l) }
	}
}

#[cfg(feature = "auxlib")]
impl<'l, const ID_SIZE: usize> Managed<'l, ID_SIZE> {
	/// # Safety
	/// The underlying Lua state may raise an arbitrary [error](crate::errors).
	#[inline(always)]
	pub unsafe fn call_metamethod(
		&mut self,
		obj_index: c_int, event: &CStr
	) -> bool {
		(unsafe { luaL_callmeta(
			self.l,
			obj_index, event.as_ptr()
		) }) != 0
	}

	/// # Safety
	/// The underlying Lua state may raise a memory [error](crate::errors).
	#[inline(always)]
	pub unsafe fn do_file(&mut self, file_name: &CStr) -> bool {
		unsafe { luaL_dofile(self.l, file_name.as_ptr()) }
	}

	#[inline(always)]
	pub fn do_string(&mut self, code: &CStr) -> bool {
		unsafe { luaL_dostring(self.l, code.as_ptr()) }
	}

	/// # Safety
	/// The underlying Lua state may raise an arbitrary [error](crate::errors).
	#[inline(always)]
	pub unsafe fn get_sub_table(
		&mut self,
		parent_index: c_int, table_name: &CStr
	) -> bool {
		(unsafe { luaL_getsubtable(
			self.l,
			parent_index, table_name.as_ptr()
		) }) != 0
	}

	/// # Safety
	/// The underlying Lua state may raise an arbitrary [error](crate::errors).
	#[inline(always)]
	pub unsafe fn to_chars_aux(&'l mut self, index: c_int) -> Option<&'l [c_char]> {
		let mut len = 0;
		let str_ptr = unsafe { luaL_tolstring(self.l, index, &mut len as *mut _) };
		if !str_ptr.is_null() {
			Some(unsafe { from_raw_parts(str_ptr, len) })
		} else {
			None
		}
	}

	/// Works the same as [`Managed::to_chars_aux`], however it returns an array
	/// of [`u8`]s instead of [`c_char`]s.
	/// 
	/// # Safety
	/// The underlying Lua state may raise an arbitrary [error](crate::errors).
	#[inline(always)]
	pub unsafe fn to_byte_str_aux(&'l mut self, index: c_int) -> Option<&'l [u8]> {
		let mut len = 0;
		let str_ptr = unsafe { luaL_tolstring(self.l, index, &mut len as *mut _) };
		if !str_ptr.is_null() {
			Some(unsafe { from_raw_parts(str_ptr as *const _, len) })
		} else {
			None
		}
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

	/// Close all active to-be-closed variables in the main thread, release all
	/// objects (calling the corresponding garbage-collection metamethods, if
	/// any), and free all dynamic memory used by this [`Thread`].
	#[inline(always)]
	pub unsafe fn close_as_main(&mut self) {
		lua_close(self.l)
	}

	#[inline(always)]
	pub fn close_as_coroutine(&mut self) -> Status {
		unsafe { Status::from_c_int_unchecked(lua_resetthread(self.l)) }
	}

	/// Set a new panic function and return the old one.
	#[inline(always)]
	pub fn at_panic(
		&self, func: Option<CFunction>
	) -> Option<CFunction> {
		unsafe { lua_atpanic(self.l, func) }
	}

	/// Raise a Lua error, using the value on the top of the stack as the error
	/// object.
	/// 
	/// This function does a long jump, and therefore never returns.
	#[inline(always)]
	pub fn error(&self) -> ! {
		unsafe { lua_error(self.l) }
	}

	/// Stop the garbage collector.
	#[inline(always)]
	pub fn stop_gc(&self) {
		unsafe { lua_gc(self.l, GcTask::Stop as _) };
	}

	/// Return the current amount of memory (in kilobytes) in use by this
	/// [`Thread`].
	#[inline(always)]
	pub fn mem_kbytes(&self) -> c_uint {
		unsafe { lua_gc(self.l, GcTask::CountKbytes as _) }
			.clamp(0, c_int::MAX) as _
	}

	/// Return the remainder of dividing the current amount of bytes of memory
	/// in use by this [`Thread`] by `1024`.
	#[inline(always)]
	pub fn mem_byte_remainder(&self) -> c_uint {
		unsafe { lua_gc(self.l, GcTask::CountBytesRem as _) }
			.clamp(0, c_int::MAX) as _
	}

	/// Return true if the collector is running (i.e. not stopped).
	#[inline(always)]
	pub fn is_gc_running(&self) -> bool {
		(unsafe { lua_gc(self.l, GcTask::IsRunning as _) }) != 0
	}

	/// Change the collector to either incremental or generational mode (see
	/// also [`GcMode`]) with the given parameters.
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

	/// Convert the acceptable index `idx` into an equivalent absolute index
	/// (that is, one that does not depend on the stack size).
	#[inline(always)]
	pub fn abs_index(&self, idx: c_int) -> c_int {
		unsafe { lua_absindex(self.l, idx) }
	}

	/// Ensure that the stack has space for at least `n` extra elements.
	/// That is, that you can safely push up to `n` values into it.
	/// 
	/// Returns `false` if it cannot fulfill the request, either because it
	/// would cause the stack to be greater than a fixed maximum size (typically
	/// at least several thousand elements) or because it cannot allocate memory
	/// for the extra space.
	/// 
	/// This function never shrinks the stack; if the stack already has space
	/// for the extra elements, it is left unchanged.
	#[inline(always)]
	pub fn test_stack(&self, n: c_uint) -> bool {
		(unsafe { lua_checkstack(self.l, n as _) }) != 0
	}

	/// Copy the element at `from_idx` into the valid index `to_idx`, replacing
	/// the value at that position.
	/// 
	/// Values at other positions are not affected.
	#[inline(always)]
	pub fn copy(&self, from_idx: c_int, to_idx: c_int) {
		unsafe { lua_copy(self.l, from_idx, to_idx) }
	}

	/// Create a new empty table and push it onto the stack.
	/// 
	/// `narr` is a hint for how many elements the table will have as a sequence,
	/// and `nrec` is a hint for how many other elements the table will have.
	/// Lua may use these hints to preallocate memory for the new table.
	/// This preallocation may help performance when its known in advance how
	/// many elements the table will have.
	/// 
	/// See also [`Thread::new_table`].
	/// 
	/// # Safety
	/// The underlying Lua state may raise a memory [error](crate::errors).
	#[inline(always)]
	pub unsafe fn create_table(&self, n_arr: c_uint, n_rec: c_uint) {
		unsafe { lua_createtable(self.l, n_arr as _, n_rec as _) }
	}

	/// Dump a function as a binary chunk.
	/// 
	/// This function receives a Lua function on the top of the stack and
	/// produces a binary chunk that, if loaded again, results in a function
	/// equivalent to the one dumped.
	/// 
	/// As it produces parts of the chunk, the function calls `writer` (see also
	/// [`Writer`]) with the given data to write them.
	/// If `strip_debug_info` is `true`, the binary representation may not
	/// include all debug information about the function, to save space.
	/// 
	/// The value returned is the error code returned by the last call to the
	/// writer.
	/// 
	/// This function does not pop the Lua function from the stack. 
	#[inline(always)]
	pub fn dump(
		&self,
		writer: Writer, writer_data: *mut c_void,
		strip_debug_info: bool
	) -> Status {
		unsafe { Status::from_c_int_unchecked(lua_dump(
			self.l,
			writer, writer_data,
			if strip_debug_info { 1 } else { 0 }
		)) }
	}

	/// Return the memory-allocation function of this [`Thread`] along with the
	/// opaque pointer given when the memory-allocator function was set.
	#[inline(always)]
	pub fn get_alloc_fn(&self) -> (Alloc, *mut c_void) {
		let mut ud = null_mut();
		let alloc_fn = unsafe { lua_getallocf(
			self.l, &mut ud as *mut *mut c_void
		) };
		(alloc_fn, ud)
	}

	/// Push onto the stack the value of the global `name`, and return the type
	/// of that value.
	/// 
	/// # Safety
	/// The underlying Lua state may raise an arbitrary [error](crate::errors).
	#[inline(always)]
	pub unsafe fn get_global(&self, name: &CStr) -> Type {
		unsafe { Type::from_c_int_unchecked(lua_getglobal(self.l, name.as_ptr())) }
	}

	/// Push onto the stack the `n`-th user value associated with the full
	/// userdata at the given index and returns the type of the pushed value.
	/// 
	/// If the userdata does not have that value, push `nil` and return
	/// [`Type::None`]. 
	#[inline(always)]
	pub fn get_i_uservalue(&self, ud_index: c_int, n: c_ushort) -> Type {
		unsafe { Type::from_c_int_unchecked(
			lua_getiuservalue(self.l, ud_index, n as _)
		) }
	}

	/// If the value at the given index has a metatable, push that metatable
	/// onto the stack and return `true`. Otherwise, push nothing and return
	/// `false`. 
	#[inline(always)]
	pub fn get_metatable(&self, obj_index: c_int) -> bool {
		(unsafe { lua_getmetatable(self.l, obj_index) }) != 0
	}

	/// Return the index of the top element in the stack.
	/// 
	/// Because indices start at `1`, this result is equal to the number of
	/// elements in the stack; in particular, `0` means an empty stack.
	#[inline(always)]
	pub fn top(&self) -> c_int {
		unsafe { lua_gettop(self.l) }
	}

	/// Move the top element into the given valid index, shifting up the
	/// elements above that index to open space.
	/// 
	/// This function cannot be called with a pseudo-index, because a
	/// pseudo-index is not an actual stack position.
	#[inline(always)]
	pub fn insert(&self, index: c_int) {
		unsafe { lua_insert(self.l, index) }
	}

	lua_is! {
		/// Return `true` if the value at the given index is a boolean.
		#[inline(always)]
		pub fn is_boolean(&self, index: c_int) -> bool for lua_isboolean -> bool;
		/// Return `true` if the value at the given index is a C function.
		#[inline(always)]
		pub fn is_c_function(&self, index: c_int) -> bool
			for lua_iscfunction -> c_int;
		/// Return `true` if the value at the given index is a function (either
		/// C or Lua).
		#[inline(always)]
		pub fn is_function(&self, index: c_int) -> bool
			for lua_isfunction -> bool;
		/// Return `true` if the value at the given index is an integer.
		#[inline(always)]
		pub fn is_integer(&self, index: c_int) -> bool
			for lua_isinteger -> c_int;
		/// Return `true` if the value at the given index is a light userdata.
		#[inline(always)]
		pub fn is_light_userdata(&self, index: c_int) -> bool
			for lua_islightuserdata -> bool;
		/// Return `true` if the value at the given index is `nil`.
		#[inline(always)]
		pub fn is_nil(&self, index: c_int) -> bool for lua_isnil -> bool;
		/// Return `true` if the value at the given index is not valid.
		#[inline(always)]
		pub fn is_none(&self, index: c_int) -> bool for lua_isnone -> bool;
		/// Return `true` if the value at the given index is not valid or is
		/// `nil`.
		#[inline(always)]
		pub fn is_none_or_nil(&self, index: c_int) -> bool
			for lua_isnoneornil -> bool;
		/// Return `true` if the value at the given index is a number.
		#[inline(always)]
		pub fn is_number(&self, index: c_int) -> bool for lua_isnumber -> c_int;
		/// Return `true` if the value at the given index is a string *or* a
		/// number, which is always convertible to a string.
		#[inline(always)]
		pub fn is_string(&self, index: c_int) -> bool for lua_isstring -> c_int;
		/// Return `true` if the value at the given index is a table.
		#[inline(always)]
		pub fn is_table(&self, index: c_int) -> bool for lua_istable -> bool;
		/// Return `true` if the value at the given index is a thread.
		#[inline(always)]
		pub fn is_thread(&self, index: c_int) -> bool for lua_isthread -> bool;
		/// Return `true` if the value at the given index is a userdata (either
		/// full or light).
		#[inline(always)]
		pub fn is_userdata(&self, index: c_int) -> bool
			for lua_isuserdata -> c_int;
	}

	/// Return `true` if the coroutine can yield.
	#[inline(always)]
	pub fn can_yield(&self) -> bool {
		(unsafe { lua_isyieldable(self.l) }) != 0
	}

	/// Load a Lua chunk without running it.
	/// If there are no errors, push the compiled chunk as a Lua function.
	/// Otherwise, push an error message.
	/// 
	/// This function uses a user-supplied `reader` to read the chunk (see also [`Reader`]).
	/// `data` is an opaque value passed to the reader function.
	/// 
	/// `chunk_name` gives a name to the chunk, which is used for error messages
	/// and in debug information.
	/// 
	/// The function automatically detects whether the chunk is text or binary
	/// and loads it accordingly.
	/// The string `mode` works similarly as in the Lua base library function
	/// `load`:
	/// - `Some("b")` loads only binary chunks.
	/// - `Some("t")` loads only text chunks.
	/// - `Some("bt")` loads both binary and text chunks.
	/// - `None` is equivalent to the string `"bt"`.
	/// 
	/// This function uses the stack internally, so `reader` must always leave
	/// the stack *unmodified* when returning.
	/// 
	/// If the resulting function has upvalues, its first upvalue is set to the
	/// value of the global environment stored at index [`REGISTRY_GLOBALS`] in
	/// the registry.
	/// When loading main chunks, this upvalue will be the `_ENV` variable.
	/// Other upvalues are initialized with `nil`. 
	// TODO: Safe `Reader`?
	#[inline(always)]
	pub fn load(
		&self,
		reader: Reader, data: *mut c_void,
		chunk_name: &CStr, mode: Option<&CStr>
	) -> Status {
		unsafe { Status::from_c_int_unchecked(
			lua_load(
				self.l,
				reader, data,
				chunk_name.as_ptr(),
				mode.map(|cstr| cstr.as_ptr()).unwrap_or(null())
			)
		) }
	}

	/// Create a new empty table and push it onto the stack.
	/// 
	/// See also [`Thread::create_table`].
	/// 
	/// # Safety
	/// The underlying Lua state may raise a memory [error](crate::errors).
	#[inline(always)]
	pub unsafe fn new_table(&self) {
		unsafe { lua_newtable(self.l) }
	}

	/// Create a new thread, push it on the stack, and return a [`Coroutine`]
	/// that represents this new thread.
	/// 
	/// The new thread returned by this function shares with the original thread
	/// its global environment, but has an independent execution stack.
	/// Threads are subject to garbage collection, like any Lua object.
	/// 
	/// # Safety
	/// The underlying Lua state may raise a memory [error](crate::errors).
	#[inline(always)]
	pub unsafe fn new_thread<'l>(&'l self) -> Coroutine<'l, ID_SIZE> {
		Coroutine {
			thread: unsafe { Thread::from_ptr(lua_newthread(self.l)) },
			_life: PhantomData
		}
	}

	/// Create and push on the stack a new full userdata, with `n_uservalues`
	/// associated Lua values, called user values, and an associated block of
	/// raw memory of `size` bytes.
	/// 
	/// The user values can be set and read with the functions
	/// [`Thread::set_i_uservalue`] and [`Thread::get_i_uservalue`].
	/// 
	/// The function returns a mutable slice of the block of memory that was
	/// allocated by Lua.
	/// Lua ensures that the slice is valid as long as the corresponding
	/// userdata is alive. Moreover, if the userdata is marked for finalization,
	/// it is valid at least until the call to its finalizer.
	/// 
	/// # Safety
	/// The underlying Lua state may raise a memory [error](crate::errors).
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
	
	/// Pop a key from the stack, and push a key–value pair from the table at
	/// the given index, the "next" pair after the given key.
	/// 
	/// This function returns `true` while there are still elements to go
	/// through. If there are no more elements in the table, then this it
	/// returns `false` and pushes nothing.
	/// 
	/// # Note on string conversion functions
	/// While traversing a table, avoid calling [`Thread::to_chars`] directly on
	/// a key, unless it is known that the key is actually a **string**.
	/// [`Thread::to_chars`] and other similar functions may change the value at
	/// the given index; this confuses the next call to [`Thread::next`].
	/// 
	/// # Safety
	/// The underlying Lua state may raise an [error](crate::errors) if a given
	/// key is neither `nil` nor present in the table.
	#[inline(always)]
	pub unsafe fn next(&self, index: c_int) -> bool {
		(unsafe { lua_next(self.l, index) }) != 0
	}

	/// Pop `n` elements from the stack.
	#[inline(always)]
	pub fn pop(&self, n: c_int) {
		unsafe { lua_pop(self.l, n) }
	}

	/// Push a [`bool`] onto the stack.
	#[inline(always)]
	pub fn push_boolean(&self, value: bool) {
		unsafe { lua_pushboolean(self.l, if value { 1 } else { 0 }) }
	}

	/// Push a new C closure onto the stack.
	/// 
	/// This function receives a C function `func` and pushes onto the stack a
	/// Lua value of type `function` that, when called, invokes the
	/// corresponding C function.
	/// `n_upvalues` tells how many upvalues this function will have.
	/// 
	/// Any function to be callable by Lua must follow the correct protocol to
	/// receive its parameters and return its results (see [`CFunction`]).
	/// 
	/// # C closures
	/// When a C function is created, it is possible to associate some values
	/// with it, which are called *upvalues*.
	/// These upvalues are then accessible to the function whenever it is called,
	/// where the function is called a *C closure*. To create a C closure:
	/// 1. Push the initial values for its upvalues onto the stack.
	/// (When there are multiple upvalues, the first value is pushed first.)
	/// 2. Call this function with the argument `n_upvalues` telling how many
	/// upvalues will be associated with the function.
	/// The function will also pop these values from the stack.
	/// 
	/// When `n_upvalues == 0`, this function creates a "light" C function,
	/// which is just a pointer to the C function. In that case, it never raises
	/// a memory error.
	/// 
	/// See also [`Thread::push_c_function`].
	/// 
	/// # Safety
	/// The underlying Lua state may raise a memory [error](crate::errors) if
	/// `n_upvalues > 0`.
	#[inline(always)]
	pub unsafe fn push_c_closure(&self, func: CFunction, n_upvalues: u8) {
		unsafe { lua_pushcclosure(self.l, func, n_upvalues as _) }
	}

	/// Push a light C function onto the stack (that is, a C function with no
	/// upvalues).
	/// 
	/// See also [`Thread::push_c_closure`].
	#[inline(always)]
	pub fn push_c_function(&self, func: CFunction) {
		unsafe { lua_pushcfunction(self.l, func) }
	}

	/// Push the global environment onto the stack.
	#[inline(always)]
	pub fn push_global_table(&self) {
		unsafe { lua_pushglobaltable(self.l) }
	}

	/// Push an [`Integer`] onto the stack.
	#[inline(always)]
	pub fn push_integer(&self, value: Integer) {
		unsafe { lua_pushinteger(self.l, value) }
	}

	/// Push a light userdata onto the stack.
	/// 
	/// A light userdata represents a plain pointer.
	/// It is a value, like a number: it is not created, it has no individual
	/// metatable, and it is not collected (as it was never created).
	/// 
	/// A light userdata is equal to any light userdata with the same C address.
	#[inline(always)]
	pub fn push_light_userdata(&self, ptr: *mut c_void) {
		unsafe { lua_pushlightuserdata(self.l, ptr) }
	}

	// TODO: Document this.
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

	/// Push `nil` onto the stack.
	#[inline(always)]
	pub fn push_nil(&self) {
		unsafe { lua_pushnil(self.l) }
	}

	// TODO: Document this.
	/// # Safety
	/// The underlying Lua state may raise a memory [error](crate::errors).
	#[inline(always)]
	pub unsafe fn push_string<'l>(&'l self, data: &CStr) -> &'l CStr {
		unsafe { CStr::from_ptr(
			lua_pushstring(self.l, data.as_ptr())
		) }
	}

	/// Push the Lua thread represented by this [`Thread`] onto its own stack,
	/// and return `true` if this thread is the main thread (see also [`Lua`]).
	#[inline(always)]
	pub fn push_thread(&self) -> bool {
		(unsafe { lua_pushthread(self.l) }) != 0
	}

	/// Push a copy of the element at the given index onto the stack.
	#[inline(always)]
	pub fn push_value(&self, index: c_int) {
		unsafe { lua_pushvalue(self.l, index) }
	}

	/// Return `true` if the two values in indices `idx_a` and `idx_b` are
	/// primitively equal (that is, equal without calling the `__eq` metamethod).
	/// 
	/// This also returns `false` if any of the indices are not valid.
	#[inline(always)]
	pub fn raw_equal(&self, idx_a: c_int, idx_b: c_int) -> bool {
		(unsafe { lua_rawequal(self.l, idx_a, idx_b) }) != 0
	}

	// TODO: Document this.
	#[inline(always)]
	pub fn raw_get(&self, tbl_index: c_int) -> Type {
		unsafe { Type::from_c_int_unchecked(
			lua_rawget(self.l, tbl_index)
		) }
	}

	// TODO: Document this.
	#[inline(always)]
	pub fn raw_get_i(&self, tbl_index: c_int, i: Integer) -> Type {
		unsafe { Type::from_c_int_unchecked(
			lua_rawgeti(self.l, tbl_index, i)
		) }
	}

	// TODO: Document this.
	#[inline(always)]
	pub fn raw_get_p(&self, tbl_index: c_int, ptr: *const c_void) -> Type {
		unsafe { Type::from_c_int_unchecked(
			lua_rawgetp(self.l, tbl_index, ptr)
		) }
	}

	/// Return the raw "length" of the value at the given index.
	/// 
	/// For strings, this is the string length;
	/// for tables, this is the result of the length operator (`#`) with no
	/// metamethods;
	/// for userdata, this is the size of the block of memory allocated for the
	/// userdata.
	/// For other values, this call returns `0`. 
	#[inline(always)]
	pub fn raw_length(&self, index: c_int) -> Unsigned {
		unsafe { lua_rawlen(self.l, index) }
	}

	// TODO: Document this.
	/// # Safety
	/// The underlying Lua state may raise a memory [error](crate::errors).
	#[inline(always)]
	pub unsafe fn raw_set(&self, tbl_index: c_int) {
		unsafe { lua_rawset(self.l, tbl_index) }
	}

	// TODO: Document this.
	/// # Safety
	/// The underlying Lua state may raise a memory [error](crate::errors).
	#[inline(always)]
	pub unsafe fn raw_set_i(&self, tbl_index: c_int, i: Integer) {
		unsafe { lua_rawseti(self.l, tbl_index, i) }
	}

	// TODO: Document this.
	/// # Safety
	/// The underlying Lua state may raise a memory [error](crate::errors).
	#[inline(always)]
	pub unsafe fn raw_set_p(&self, tbl_index: c_int, ptr: *const c_void) {
		unsafe { lua_rawsetp(self.l, tbl_index, ptr) }
	}

	/// Set the C function `func` as the new value of global `name`.
	/// 
	/// # Safety
	/// The underlying Lua state may raise an arbitrary [error](crate::errors).
	#[inline(always)]
	pub unsafe fn register(&self, name: &CStr, func: CFunction) {
		unsafe { lua_register(self.l, name.as_ptr(), func) }
	}

	/// Remove the element at the given valid index, shifting down the elements
	/// above this index to fill the gap.
	/// 
	/// This function cannot be called with a pseudo-index, because a
	/// pseudo-index is not an actual stack position.
	#[inline(always)]
	pub fn remove(&self, index: c_int) {
		unsafe { lua_remove(self.l, index) }
	}

	/// Move the top element into the given valid index without shifting any
	/// element (therefore replacing the value at that given index),
	/// and then pop that top element.
	#[inline(always)]
	pub fn replace(&self, index: c_int) {
		unsafe { lua_replace(self.l, index) }
	}

	// TODO: Document this.
	#[inline(always)]
	pub fn resume(
		&self, from: &Thread,
		n_args: c_int
	) -> (Status, c_int) {
		let mut n_res = 0;
		let status = unsafe { lua_resume(
			self.l, from.as_ptr(),
			n_args,
			&mut n_res as *mut _
		) };
		(unsafe { Status::from_c_int_unchecked(status) }, n_res)
	}

	/// Rotate the stack elements between the valid index `index` and the top of
	/// the stack.
	/// 
	/// The elements are rotated `n` positions in the direction of the top for a 
	/// ositive `n`, or `-n` positions in the direction of the bottom for a
	/// negative `n`.
	/// The absolute value of `n` must not be greater than the size of the slice
	/// being rotated.
	/// 
	/// This function cannot be called with a pseudo-index, because a
	/// pseudo-index is not an actual stack position.
	#[inline(always)]
	pub fn rotate(&self, index: c_int, n_values: c_int) {
		unsafe { lua_rotate(self.l, index, n_values) }
	}

	/// Pop a value from the stack and set it as the new value of global `name`.
	/// # Safety
	/// The underlying Lua state may raise an arbitrary [error](crate::errors).
	#[inline(always)]
	pub unsafe fn set_global(&self, key: &CStr) {
		unsafe { lua_setglobal(self.l, key.as_ptr()) }
	}

	/// Pop a value from the stack and set it as the new `n`-th user value
	/// associated to the full userdata at the given index.
	/// 
	/// Returns `false` if the userdata does not have that value.
	#[inline(always)]
	pub fn set_i_uservalue(&self, ud_index: c_int, n: c_ushort) -> bool {
		(unsafe { lua_setiuservalue(self.l, ud_index, n as _) }) != 0
	}

	/// Pop a table or `nil` from the stack and sets that value as the new
	/// metatable for the value at the given index. (`nil` means no metatable.)
	// NOTE: `lua_setmetatable` always returns a `1`, which isn't useful.
	#[inline(always)]
	pub fn set_metatable(&self, obj_index: c_int) {
		unsafe { lua_setmetatable(self.l, obj_index) };
	}

	/// Accept any index, or `0`, and set the stack top to this index.
	/// 
	/// If the new top is greater than the old one, then the new elements are
	/// filled with `nil`. If index is 0, then all stack elements are removed.
	/// 
	/// This function can run arbitrary code when removing an index marked as
	/// to-be-closed from the stack. 
	// FIXME: ^ speaking of this, the function signature should say that.
	pub fn set_top(&self, top: c_int) {
		unsafe { lua_settop(self.l, top) }
	}

	// TODO: Document this.
	#[inline(always)]
	pub fn set_warn_fn(&self, func: Option<WarnFunction>, ud: *mut c_void) {
		unsafe { lua_setwarnf(self.l, func, ud) }
	}

	/// Return the status of the Lua thread represented by this [`Thread`].
	/// 
	/// The status can be [`Status::Ok`] for a normal thread, an error variant
	/// if the thread finished the execution of a [`Thread::resume`] with an
	/// error, or [`Status::Yielded`] if the thread is suspended.
	/// 
	/// Functions can only be called in threads with status [`Status::Ok`].
	/// Threads with status [`Status::Ok`] or [`Status::Yielded`] can be resumed
	/// (to start a new coroutine or resume an existing one). 
	#[inline(always)]
	pub fn status(&self) -> Status {
		unsafe { Status::from_c_int_unchecked(lua_status(self.l)) }
	}

	/// Convert the Lua value at the given index to a [`bool`].
	/// 
	/// Like all tests in Lua, this returns `true` for any Lua value different
	/// from `false` and `nil`; otherwise it returns `false`.
	/// 
	/// If you want to accept only actual boolean values, use
	/// [`Thread::is_boolean`] to test the value's type first.
	#[inline(always)]
	pub fn to_boolean(&self, idx: c_int) -> bool {
		(unsafe { lua_toboolean(self.l, idx) }) != 0
	}

	/// Convert a value at the given index to a C function.
	/// If it is not one, return `None`.
	#[inline(always)]
	pub fn to_c_function(&self, index: c_int) -> Option<CFunction> {
		unsafe { lua_tocfunction(self.l, index) }
	}

	// TODO: Document this.
	#[inline(always)]
	pub fn to_integer(&self, idx: c_int) -> Integer {
		unsafe { lua_tointeger(self.l, idx) }
	}

	// TODO: Document this.
	#[inline(always)]
	pub fn to_integer_opt(&self, idx: c_int) -> Option<Integer> {
		let mut is_num = 0;
		let result = unsafe { lua_tointegerx(self.l, idx, &mut is_num as *mut _) };
		(is_num != 0).then_some(result)
	}

	// TODO: Document this.
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

	/// Works the same as [`Thread::to_chars`], however it returns an array of
	/// [`u8`]s instead of [`c_char`]s.
	/// 
	/// # Safety
	/// The underlying Lua state may raise a memory [error](crate::errors).
	#[inline(always)]
	pub unsafe fn to_byte_str<'l>(
		&'l self, index: c_int
	) -> Option<&'l [u8]> {
		let mut len = 0;
		let str_ptr = unsafe { lua_tolstring(self.l, index, &mut len as *mut _) };
		if !str_ptr.is_null() {
			Some(unsafe { from_raw_parts(str_ptr as *const _, len) })
		} else {
			None
		}
	}

	// TODO: Document this.
	#[inline(always)]
	pub fn to_number(&self, idx: c_int) -> Number {
		unsafe { lua_tonumber(self.l, idx) }
	}

	// TODO: Document this.
	#[inline(always)]
	pub fn to_number_opt(&self, idx: c_int) -> Option<Number> {
		let mut is_num = 0;
		let result = unsafe { lua_tonumberx(self.l, idx, &mut is_num as *mut _) };
		(is_num != 0).then_some(result)
	}

	/// Convert the value at the given index to a generic C pointer
	/// ([`*const c_void`](c_void)).
	/// 
	/// The value can be a userdata, a table, a thread, a string, or a function;
	/// otherwise, this function returns null.
	/// 
	/// Different objects will give different pointers.
	/// There is no way to convert the pointer back to its original value.
	/// 
	/// Typically this function is used only for hashing and debug information. 
	#[inline(always)]
	pub fn to_pointer(&self, idx: c_int) -> *const c_void {
		unsafe { lua_topointer(self.l, idx) }
	}

	// TODO: Document this.
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

	/// Return the type of the value in the given valid index, or [`Type::None`]
	/// for a non-valid but acceptable index.
	#[inline(always)]
	pub fn type_of(&self, idx: c_int) -> Type {
		unsafe { Type::from_c_int_unchecked(lua_type(self.l, idx)) }
	}

	/// Return the name of the type encoded by `type_tag`.
	#[inline(always)]
	pub fn type_name<'a>(&'a self, type_tag: Type) -> &'a CStr {
		unsafe { CStr::from_ptr(lua_typename(self.l, type_tag as _)) }
	}

	/// Return the version number of the Lua core.
	#[inline(always)]
	pub fn version(&self) -> Number {
		unsafe { lua_version(self.l) }
	}

	/// Emit a warning with the given message.
	/// 
	/// A message in a call with `to_be_continued == true` should be continued
	/// in another call to this function.
	#[inline(always)]
	pub fn warning(&self, message: &CStr, to_be_continued: bool) {
		unsafe { lua_warning(
			self.l, message.as_ptr(), if to_be_continued { 1 } else { 0 }
		) }
	}

	/// Exchange values between different threads of the same state.
	/// 
	/// This function pops `n_values` values from the stack of this thread, and
	/// pushes them onto the stack of the thread `to`.
	#[inline(always)]
	pub fn xmove(&self, to: &Thread, n_values: c_uint) {
		unsafe { lua_xmove(self.l, to.as_ptr(), n_values as _) }
	}

	// TODO: Safety and documentation.
	#[inline(always)]
	pub unsafe fn yield_with(&self, n_results: c_int) -> ! {
		unsafe { lua_yield(self.l, n_results) }
	}

	// TODO: Safety and documentation.
	#[inline(always)]
	pub unsafe fn yield_in_hook_with(&self, n_results: c_int) {
		unsafe { lua_yield_in_hook(self.l, n_results) };
	}

	// TODO: Safety and documentation.
	#[inline(always)]
	pub unsafe fn yield_continue_with(
		&self, n_results: c_int,
		continuation: KFunction, context: KContext
	) -> ! {
		unsafe { lua_yieldk(self.l, n_results, context, Some(continuation)) }
	}

	// TODO: Safety and documentation.
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

	/// Return the current hook function.
	/// 
	/// See also [`Hook`].
	#[inline(always)]
	pub fn hook(&self) -> Hook<ID_SIZE> {
		unsafe { lua_gethook(self.l) }
	}

	/// Return the current hook count.
	#[inline(always)]
	pub fn hook_count(&self) -> c_int {
		unsafe { lua_gethookcount(self.l) }
	}

	/// Return the current hook mask.
	/// 
	/// See also [`HookMask`].
	#[inline(always)]
	pub fn hook_mask(&self) -> HookMask {
		unsafe { HookMask::from_c_int_unchecked(lua_gethookmask(self.l)) }
	}

	/// Gets information about a specific function or function invocation.
	/// 
	/// # Safety
	/// `ar` must be a valid activation record that was filled by a previous
	/// call to [`Thread:get_stack`] or given as argument to a hook (see [`Hook`]). 
	#[inline(always)]
	pub unsafe fn get_info(&self, what: &CStr, ar: &mut Debug<ID_SIZE>) -> bool {
		(unsafe { lua_getinfo(self.l, what.as_ptr(), ar) }) != 0
	}

	// TODO: Document this.
	#[inline(always)]
	pub fn get_local<'dbg>(
		&self,
		ar: &'dbg Debug<ID_SIZE>, n: c_int
	) -> &'dbg CStr {
		unsafe { CStr::from_ptr(lua_getlocal(self.l, ar, n)) }
	}

	/// Get information about the `n`-th upvalue of the closure at index
	/// `func_index`.
	/// 
	/// This function pushes the upvalue's value onto the stack and returns its
	/// name. Returns `None` (and pushes nothing) when the index `n` is greater
	/// than the number of upvalues.
	#[inline(always)]
	pub fn get_upvalue<'l>(
		&'l self, func_index: c_int, n: u8
	) -> Option<&'l CStr> {
		let str_ptr = unsafe { lua_getupvalue(self.l, func_index, n as _) };
		if !str_ptr.is_null() {
			Some(unsafe { CStr::from_ptr(str_ptr) })
		} else {
			None
		}
	}

	// TODO: Document this.
	#[inline(always)]
	pub fn set_hook(&self, hook: Hook<ID_SIZE>, mask: HookMask, count: c_int) {
		unsafe { lua_sethook(self.l, hook, mask.into_c_int(), count) }
	}

	// TODO: Document this.
	#[inline(always)]
	pub unsafe fn set_local<'dbg>(
		&self,
		ar: &'dbg Debug<ID_SIZE>, n: c_int
	) -> &'dbg CStr {
		unsafe { CStr::from_ptr(lua_setlocal(self.l, ar, n)) }
	}

	// TODO: Document this.
	#[inline(always)]
	pub unsafe fn set_upvalue<'l>(&'l self, func_index: c_int, n: u8) -> &'l CStr {
		unsafe { CStr::from_ptr(lua_setupvalue(self.l, func_index, n as _)) }
	}

	// TODO: Document this.
	#[inline(always)]
	pub fn upvalue_id(&self, func_index: c_int, n: u8) -> *mut c_void {
		unsafe { lua_upvalueid(self.l, func_index, n as _) }
	}

	/// Make the
	/// `n_into`-th upvalue of the Lua closure at index `func_into_index`
	/// refer to the
	/// `n_from`-th upvalue of the Lua closure at index `func_from_index`.
	#[inline(always)]
	pub fn upvalue_join(
		&self,
		func_into_index: i32, n_into: u8,
		func_from_index: i32, n_from: u8
	) {
		unsafe { lua_upvaluejoin(
			self.l,
			func_into_index, n_into as _,
			func_from_index, n_from as _
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
	pub fn new_buffer<'l>(&'l self) -> Buffer<'l> {
		unsafe { Buffer::new_in_raw(self.l) }
	}

	#[inline(always)]
	pub fn arg_error(&self, arg: c_int, extra_message: &CStr) -> ! {
		unsafe { luaL_argerror(self.l, arg, extra_message.as_ptr()) }
	}

	/// # Safety
	/// The underlying Lua state may raise an [error](crate::errors) if the
	/// argument `arg`'s type is incorrect.
	#[inline(always)]
	pub unsafe fn check_any(&self, arg: c_int) {
		unsafe { luaL_checkany(self.l, arg) }
	}

	/// # Safety
	/// The underlying Lua state may raise an [error](crate::errors) if the
	/// argument `arg`'s type is incorrect.
	#[inline(always)]
	pub unsafe fn check_integer(&self, arg: c_int) -> Integer {
		unsafe { luaL_checkinteger(self.l, arg) }
	}

	/// # Safety
	/// The underlying Lua state may raise an [error](crate::errors) if the
	/// argument `arg` isn't a string.
	#[inline(always)]
	pub unsafe fn check_chars<'l>(&'l self, arg: c_int) -> &'l [c_char] {
		let mut len = 0;
		let str_ptr = unsafe { luaL_checklstring(self.l, arg, &mut len as *mut _) };
		unsafe { from_raw_parts(str_ptr, len) }
	}

	/// Works the same as [`Thread::check_chars`], however it returns an array
	/// of [`u8`]s instead of [`c_char`]s.
	/// 
	/// # Safety
	/// The underlying Lua state may raise an [error](crate::errors) if the
	/// argument `arg` isn't a string.
	#[inline(always)]
	pub unsafe fn check_byte_str<'l>(&'l self, arg: c_int) -> &'l [u8] {
		let mut len = 0;
		let str_ptr = unsafe { luaL_checklstring(self.l, arg, &mut len as *mut _) };
		unsafe { from_raw_parts(str_ptr as *const _, len) }
	}

	/// # Safety
	/// The underlying Lua state may raise an [error](crate::errors) if the
	/// argument `arg`'s type is incorrect.
	#[inline(always)]
	pub unsafe fn check_number(&self, arg: c_int) -> Number {
		unsafe { luaL_checknumber(self.l, arg) }
	}

	/// # Safety
	/// The underlying Lua state may raise an [error](crate::errors) if the
	/// argument `arg` is not a string or if the string cannot be found in `list`. 
	#[inline(always)]
	pub unsafe fn check_option<const N: usize>(
		&self, arg: c_int,
		default: Option<&CStr>,
		list: AuxOptions<'_, N>
	) -> usize {
		(unsafe { luaL_checkoption(
			self.l, arg,
			default.map(|cstr| cstr.as_ptr()).unwrap_or(null()),
			list.as_ptr()
		) }) as _
	}

	/// # Safety
	/// The underlying Lua state may raise an [error](crate::errors) if the
	/// Lua stack cannot grow to the given size.
	#[inline(always)]
	pub unsafe fn check_stack(&self, size: c_int, message: &CStr) {
		unsafe { luaL_checkstack(self.l, size, message.as_ptr()) }
	}

	/// # Safety
	/// The underlying Lua state may raise an [error](crate::errors) if the
	/// argument `arg` isn't a string.
	#[inline(always)]
	pub unsafe fn check_string<'l>(&'l self, arg: c_int) -> &'l CStr {
		let str_ptr = unsafe { luaL_checkstring(self.l, arg) };
		unsafe { CStr::from_ptr(str_ptr) }
	}

	/// # Safety
	/// The underlying Lua state may raise an [error](crate::errors) if the
	/// argument `arg`'s type is incorrect.
	#[inline(always)]
	pub unsafe fn check_type(&self, arg: c_int, type_tag: Type) {
		unsafe { luaL_checktype(self.l, arg, type_tag as _) }
	}

	#[inline(always)]
	pub unsafe fn check_udata(
		&self, arg: c_int, table_name: &CStr
	) -> *mut c_void {
		unsafe { luaL_checkudata(self.l, arg, table_name.as_ptr()) }
	}

	/// # Safety
	/// The underlying Lua state may raise an [error](crate::errors) if the code
	/// making the call and the Lua library being called are using different
	/// version of Lua, or if the numeric types differ.
	#[inline(always)]
	pub unsafe fn check_version(&self) {
		unsafe { luaL_checkversion(self.l) }
	}

	#[inline(always)]
	pub fn error_str(&self, message: &CStr) -> ! {
		unsafe { luaL_error(
			self.l,
			CStr::from_bytes_with_nul_unchecked(b"%s\0").as_ptr(),
			message.as_ptr()
		) }
	}

	/// # Safety
	/// The underlying Lua state may raise a memory [error](crate::errors).
	#[inline(always)]
	pub unsafe fn exec_result(&self, status: c_int) -> c_int {
		unsafe { luaL_execresult(self.l, status) }
	}

	/// # Safety
	/// The underlying Lua state may raise a memory [error](crate::errors).
	#[inline(always)]
	pub unsafe fn file_result(&self, status: c_int, file_name: &CStr) -> c_int {
		unsafe { luaL_fileresult(self.l, status, file_name.as_ptr()) }
	}
	
	/// # Safety
	/// The underlying Lua state may raise a memory [error](crate::errors).
	#[inline(always)]
	pub unsafe fn get_meta_field(&self, obj_index: c_int, event: &CStr) -> Type {
		unsafe { Type::from_c_int_unchecked(luaL_getmetafield(
			self.l, obj_index, event.as_ptr()
		)) }
	}

	/// # Safety
	/// The underlying Lua state may raise a memory [error](crate::errors).
	#[inline(always)]
	pub unsafe fn get_aux_metatable(&self, table_name: &CStr) -> Type {
		unsafe { Type::from_c_int_unchecked(luaL_getmetatable(
			self.l, table_name.as_ptr()
		)) }
	}

	#[inline(always)]
	pub fn load_chars(&self, buffer: &[c_char], name: &CStr) -> Status {
		unsafe { Status::from_c_int_unchecked(
			luaL_loadbuffer(
				self.l,
				buffer.as_ptr(), buffer.len(),
				name.as_ptr()
			)
		) }
	}

	/// Works the same as [`Thread::load_chars`], however it accepts an array of
	/// [`u8`]s instead of [`c_char`]s.
	#[inline(always)]
	pub fn load_byte_str(&self, buffer: &[u8], name: &CStr) -> Status {
		unsafe { Status::from_c_int_unchecked(
			luaL_loadbuffer(
				self.l,
				buffer.as_ptr() as *const _, buffer.len(),
				name.as_ptr()
			)
		) }
	}

	/// # Safety
	/// The underlying Lua state may raise a memory [error](crate::errors).
	#[inline(always)]
	pub unsafe fn load_file(&self, code: &CStr) -> Status {
		unsafe { Status::from_c_int_unchecked(
			luaL_loadfile(self.l, code.as_ptr())
		) }
	}

	/// # Safety
	/// The underlying Lua state may raise a memory [error](crate::errors).
	#[inline(always)]
	pub unsafe fn load_stdin(&self) -> Status {
		unsafe { Status::from_c_int_unchecked(
			luaL_loadfile(self.l, null())
		) }
	}

	#[inline(always)]
	pub fn load_string(&self, code: &CStr) -> Status {
		unsafe { Status::from_c_int_unchecked(
			luaL_loadstring(self.l, code.as_ptr())
		) }
	}

	/// # Safety
	/// The underlying Lua state may raise a memory [error](crate::errors).
	#[inline(always)]
	pub unsafe fn new_lib<const N: usize>(&self, library: &Library<'_, N>) {
		unsafe { luaL_newlib(self.l, library.as_reg_slice()) }
	}

	/// # Safety
	/// The underlying Lua state may raise an [error](crate::errors) if the
	/// argument `arg` isn't a mumber, isn't a `nil` and not absent.
	pub unsafe fn opt_integer(&self, arg: c_int, default: Integer) -> Integer {
		unsafe { luaL_optinteger(self.l, arg, default) }
	}

	/// # Safety
	/// The underlying Lua state may raise an [error](crate::errors) if the
	/// argument `arg` isn't a string, isn't a `nil` and not absent.
	pub unsafe fn opt_chars<'l>(
		&'l self, arg: c_int, default: &'l CStr
	) -> &'l [c_char] {
		let mut len = 0;
		let str_ptr = unsafe { luaL_optlstring(
			self.l, arg, default.as_ptr(),
			&mut len as *mut _
		) };
		unsafe { from_raw_parts(str_ptr, len) }
	}

	/// Works the same as [`Thread::opt_chars`], however it returns an array of
	/// [`u8`]s instead of [`c_char`]s.
	/// 
	/// # Safety
	/// The underlying Lua state may raise an [error](crate::errors) if the
	/// argument `arg` isn't a string, isn't a `nil` and not absent.
	pub unsafe fn opt_byte_str<'l>(
		&'l self, arg: c_int, default: &'l [u8]
	) -> &'l [u8] {
		let mut len = 0;
		let str_ptr = unsafe { luaL_optlstring(
			self.l, arg, default.as_ptr() as *const _,
			&mut len as *mut _
		) };
		unsafe { from_raw_parts(str_ptr as *const _, len) }
	}

	/// # Safety
	/// The underlying Lua state may raise an [error](crate::errors) if the
	/// argument `arg` isn't a mumber, isn't a `nil` and not absent.
	pub unsafe fn opt_number(&self, arg: c_int, default: Number) -> Number {
		unsafe { luaL_optnumber(self.l, arg, default) }
	}

	/// # Safety
	/// The underlying Lua state may raise an [error](crate::errors) if the
	/// argument `arg` isn't a string, isn't a `nil` and not absent.
	pub unsafe fn opt_string<'l>(
		&'l self, arg: c_int, default: &'l CStr
	) -> &'l CStr {
		unsafe { CStr::from_ptr(luaL_optstring(self.l, arg, default.as_ptr())) }
	}

	#[inline(always)]
	pub fn push_fail(&self) {
		unsafe { luaL_pushfail(self.l) }
	}

	#[inline(always)]
	pub unsafe fn create_ref(&self, store_index: c_int) -> c_int {
		unsafe { luaL_ref(self.l, store_index) }
	}

	/// # Safety
	/// The underlying Lua state may raise an arbitrary [error](crate::errors).
	#[inline(always)]
	pub unsafe fn require(
		&self,
		module_name: &CStr,
		open_fn: CFunction,
		into_global: bool
	) {
		unsafe { luaL_requiref(
			self.l,
			module_name.as_ptr(),
			open_fn,
			if into_global { 1 } else { 0 }
		) }
	}

	/// # Safety
	/// The underlying Lua state may raise a memory [error](crate::errors).
	#[inline(always)]
	pub unsafe fn set_funcs<const N: usize>(
		&self, library: &Library<'_, N>, n_upvalues: u8
	) {
		unsafe { luaL_setfuncs(self.l, library.as_ptr(), n_upvalues as _) }
	}

	#[inline(always)]
	pub fn set_aux_metatable(&self, table_name: &CStr) {
		unsafe { luaL_setmetatable(self.l, table_name.as_ptr()) }
	}

	/// # Safety
	/// The underlying Lua state may raise a memory [error](crate::errors).
	#[inline(always)]
	pub unsafe fn test_udata(
		&self, arg: c_int, table_name: &CStr
	) -> Option<NonNull<u8>> {
		NonNull::new(unsafe {
			luaL_testudata(self.l, arg, table_name.as_ptr())  as *mut u8
		})
	}

	/// # Safety
	/// The underlying Lua state may raise a memory [error](crate::errors).
	#[inline(always)]
	pub unsafe fn traceback(&self, of: &Thread, message: &CStr, level: c_int) {
		unsafe { luaL_traceback(self.l, of.as_ptr(), message.as_ptr(), level) }
	}

	// TODO: Is `type_name` safe here?
	#[inline(always)]
	pub fn type_error(&self, arg: c_int, type_name: &CStr) -> ! {
		unsafe { luaL_typeerror(self.l, arg, type_name.as_ptr()) }
	}

	#[inline(always)]
	pub fn type_name_of<'l>(&'l self, index: c_int) -> &'l CStr {
		unsafe { CStr::from_ptr(luaL_typename(self.l, index)) }
	}

	#[inline(always)]
	pub fn destroy_ref(&self, store_index: c_int, ref_idx: c_int) {
		unsafe { luaL_unref(self.l, store_index, ref_idx) }
	}

	/// # Safety
	/// The underlying Lua state may raise a memory [error](crate::errors).
	#[inline(always)]
	pub unsafe fn where_str(&self, level: c_int) {
		unsafe { luaL_where(self.l, level) }
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
		unsafe { Self::from_l(luaL_newstate()) }
	}

	#[inline(always)]
	pub fn new_with_alloc_fn(
		alloc_fn: Alloc, alloc_fn_data: *mut c_void
	) -> Option<Self> {
		unsafe { Self::from_l(lua_newstate(alloc_fn, alloc_fn_data)) }
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
	pub fn close(&mut self) -> Status {
		self.thread.close_as_coroutine()
	}
}

#[macro_export]
macro_rules! push_fmt_string {
	($lua:expr, $fmt:literal $(, $fmt_arg:expr)*) => {{
		let lua: &Thread = &$lua;
		$crate::cdef::lua_pushfstring(
			lua.as_ptr(),
			core::ffi::CStr::from_bytes_with_nul_unchecked(
				concat!($fmt, "\0").as_bytes()
			).as_ptr()
			$(, $fmt_arg)*
		)
	}};
}
