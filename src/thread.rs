//! See [`Thread`].

use crate::{
	Coroutine,
	GcMode,
	cdef::*,
	managed::*
};

#[cfg(feature = "auxlib")]
use crate::{
	aux_options::*,
	cdef::auxlib::*,
	reg::*,
};

use core::{
	ffi::{
		c_char, c_int, c_uint, c_void, CStr,
	},
	marker::PhantomData,
	mem::transmute,
	ptr::{
		null, null_mut, NonNull
	},
	slice::from_raw_parts,
};

macro_rules! lua_is {
	(
		@bool
		$(#[$attr:meta])*
		$vis:vis fn $name:ident(&self, index: c_int) -> bool
		for $ffi_fn:ident
	) => {
		$(#[$attr])*
		$vis fn $name(&self, index: c_int) -> bool {
			unsafe { $ffi_fn(self.as_ptr(), index) }
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
			(unsafe { $ffi_fn(self.as_ptr(), index) }) != 0
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

/// Opaque type that represents a Lua thread, which is used by
/// [`Lua`](crate::Lua) and other structures.
/// 
/// This type can never have an instance made of it; there can only be
/// references to this type, which are the only kind of valid value.
/// 
/// # Borrowing
/// Most methods use `&mut Thread` as `&Thread`, even though, at least
/// *in theory*, they should've borrowed mutably with `&mut Thread`.
/// For instance, [`Thread::push_nil`], even though it modifies the Lua stack by
/// pushing a `nil`, still borrows a [`Thread`] immutably.
/// 
/// In the case for this structure, borrowing immutably means **not in any way
/// being able to trigger the GC to collect garbage**.
/// Any references returned by methods for this structure are simply the same
/// pointers that the C API returns, though they are converted to references for
/// the Rust borrow checker to ensure safety.
/// The Lua garbage collector will not invalidate any pointers if it is stopped.
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
#[derive(Debug)]
#[repr(transparent)]
pub struct Thread {
	_no_new: (),
}

impl Thread {
	/// Construct a reference to [`Thread`] from a raw C pointer to a Lua state.
	/// 
	/// # Safety
	/// `l` must point to a valid Lua state (`lua_State *` in C), for the
	/// duration specified by `'a`.
	pub unsafe fn from_ptr<'a>(l: *mut State) -> &'a Self {
		unsafe { &*(l as *mut Self) }
	}

	/// Construct a _mutable_ reference to [`Thread`] from a raw C pointer to a
	/// Lua state.
	/// 
	/// # Safety
	/// `l` must point to a valid Lua state (`lua_State *` in C), for the
	/// duration specified by `'a`.
	/// 
	/// **You must also, however, abide by Rust's aliasing rules.**
	/// This means that you must guarantee that there
	/// may not be two `&mut Thread`s that point to the same state,
	/// nor a `&Thread` and a `&mut Thread`.
	pub unsafe fn from_ptr_mut<'a>(l: *mut State) -> &'a mut Self {
		unsafe { &mut *(l as *mut Self) }
	}

	/// Return the raw C pointer that represents the underlying Lua state.
	pub fn as_ptr(&self) -> *mut State {
		self as *const Self as *mut State
	}

	/// Return a context that allows to run code
	/// that can restart the GC and potentially invalidate pointers.
	pub fn managed(&mut self) -> Managed<'_> {
		Managed {
			l: self.as_ptr(),
			_life: PhantomData
		}
	}

	/// This is the same as [`Thread::managed`], however it doesn't borrow
	/// mutably by assuming that the garbage collector will not collect (and
	/// thus invalidate) any outside references.
	/// 
	/// # Safety
	/// The returned context must not be used for any operations
	/// which may cause the garbage collector to invalidate pointers.
	/// 
	/// For example, if performing arithmetic does not trigger any metamethods,
	/// or if returned pointers are still on the Lua stack,
	/// then this guarantee is not broken.
	pub unsafe fn managed_no_gc(&self) -> Managed<'_> {
		Managed {
			l: self.as_ptr(),
			_life: PhantomData
		}
	}

	/// Close all active to-be-closed variables in the main thread, release all
	/// objects (calling the corresponding garbage-collection metamethods, if
	/// any), and free all dynamic memory used by this [`Thread`].
	/// 
	/// # Safety
	/// This [`Thread`] must not be used for any further API calls, as the
	/// underlying Lua pointer becomes invalid after this call.
	pub unsafe fn close_as_main(&mut self) {
		unsafe { lua_close(self.as_ptr()) }
	}

	/// Reset a thread, cleaning its call stack and closing all pending
	/// to-be-closed variables.
	/// 
	/// Returns a status code: [`Status::Ok`] for no errors in the thread
	/// (either the original error that stopped the thread or errors in closing
	/// methods), or an error status otherwise.
	/// 
	/// In case of error, leaves the error object on the top of its own stack.
	pub fn close_as_coroutine(&mut self) -> Status {
		unsafe { Status::from_c_int_unchecked(lua_resetthread(self.as_ptr())) }
	}

	/// This behaves similarly to [`Thread::close_as_coroutine`], but allows to specify `from`,
	/// which represents the coroutine that is resetting this one.
	pub fn close_as_coroutine_from(&mut self, from: &Self) -> Status {
		unsafe { Status::from_c_int_unchecked(
			lua_closethread(self.as_ptr(), from.as_ptr())
		) }
	}

	/// Set a new panic function and return the old one.
	pub fn at_panic(&self, func: Option<CFunction>) -> Option<CFunction> {
		unsafe { lua_atpanic(self.as_ptr(), func) }
	}

	/// Raise a Lua error, using the value on the top of the stack as the error
	/// object.
	/// 
	/// This function does a long jump, and therefore never returns.
	pub fn error(&self) -> ! {
		unsafe { lua_error(self.as_ptr()) }
	}

	/// Restart the garbage collector.
	/// 
	/// This by itself does not run a collection.
	pub fn restart_gc(&self) {
		unsafe { lua_gc(self.as_ptr(), GcTask::Restart as _) };
	}

	/// Stop the garbage collector.
	pub fn stop_gc(&self) {
		unsafe { lua_gc(self.as_ptr(), GcTask::Stop as _) };
	}

	/// Return the current amount of memory (in kilobytes) in use by this [`Thread`].
	pub fn mem_kbytes(&self) -> c_uint {
		unsafe { lua_gc(self.as_ptr(), GcTask::CountKbytes as _) }
			.clamp(0, c_int::MAX) as _
	}

	/// Return the remainder of dividing the current amount of bytes of memory in use by this [`Thread`] by `1024`.
	pub fn mem_byte_remainder(&self) -> c_uint {
		unsafe { lua_gc(self.as_ptr(), GcTask::CountBytesRem as _) }
			.clamp(0, c_int::MAX) as _
	}

	/// Return true if the collector is running (i.e. not stopped).
	pub fn is_gc_running(&self) -> bool {
		(unsafe { lua_gc(self.as_ptr(), GcTask::IsRunning as _) }) != 0
	}

	/// Change the collector to either incremental or generational mode (see also [`GcMode`]) with the given parameters.
	pub fn switch_gc_to(&mut self, gc: GcMode) {
		match gc {
			GcMode::Incremental { pause, step_multiplier, step_size } => unsafe {
				lua_gc(
					self.as_ptr(), GcTask::ToIncremental as _,
					pause as c_int, step_multiplier as c_int, step_size
				)
			},
			GcMode::Generational { minor_mul, major_mul } => unsafe {
				lua_gc(
					self.as_ptr(), GcTask::ToGenerational as _,
					minor_mul as c_int, major_mul as c_int
				)
			}
		};
	}

	/// Convert the acceptable index `idx` into an equivalent absolute index
	/// (that is, one that does not depend on the stack size).
	pub fn abs_index(&self, idx: c_int) -> c_int {
		unsafe { lua_absindex(self.as_ptr(), idx) }
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
	pub fn test_stack(&self, n: c_uint) -> bool {
		(unsafe { lua_checkstack(self.as_ptr(), n as _) }) != 0
	}

	/// Copy the element at `from_idx` into the valid index `to_idx`, replacing
	/// the value at that position.
	/// 
	/// Values at other positions are not affected.
	pub fn copy(&self, from_idx: c_int, to_idx: c_int) {
		unsafe { lua_copy(self.as_ptr(), from_idx, to_idx) }
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
	/// # Errors
	/// The underlying Lua state may raise a memory [error](crate::errors).
	pub fn create_table(&self, n_arr: c_uint, n_rec: c_uint) {
		unsafe { lua_createtable(self.as_ptr(), n_arr as _, n_rec as _) }
	}

	/// Dump a function as a binary chunk, and return the status of the
	/// operation.
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
	/// 
	/// # Safety
	/// `writer_data` must be valid to be passed to `writer`.
	pub unsafe fn dump(
		&self,
		writer: Writer, writer_data: *mut c_void,
		strip_debug_info: bool
	) -> c_int {
		unsafe { lua_dump(
			self.as_ptr(),
			writer, writer_data,
			if strip_debug_info { 1 } else { 0 }
		) }
	}

	/// Return the memory-allocation function of this [`Thread`] along with the
	/// opaque pointer given when the memory-allocator function was set.
	pub fn get_alloc_fn(&self) -> (Alloc, *mut c_void) {
		let mut ud = null_mut();
		let alloc_fn = unsafe { lua_getallocf(
			self.as_ptr(), &mut ud as *mut *mut c_void
		) };
		(alloc_fn, ud)
	}

	/// Push onto the stack the value of the global `name`, and return the type
	/// of that value.
	/// 
	/// # Errors
	/// The underlying Lua state may raise an arbitrary [error](crate::errors).
	pub fn get_global(&self, name: &CStr) -> Type {
		unsafe { Type::from_c_int_unchecked(lua_getglobal(self.as_ptr(), name.as_ptr())) }
	}

	/// Push onto the stack the `n`-th user value associated with the full
	/// userdata at the given index and returns the type of the pushed value.
	/// 
	/// If the userdata does not have that value, push `nil` and return [`Type::None`]. 
	pub fn get_i_uservalue(&self, ud_index: c_int, n: c_int) -> Type {
		unsafe { Type::from_c_int_unchecked(
			lua_getiuservalue(self.as_ptr(), ud_index, n)
		) }
	}

	/// If the value at the given index has a metatable, push that metatable
	/// onto the stack and return `true`. Otherwise, push nothing and return
	/// `false`. 
	pub fn get_metatable(&self, obj_index: c_int) -> bool {
		(unsafe { lua_getmetatable(self.as_ptr(), obj_index) }) != 0
	}

	/// Return the index of the top element in the stack.
	/// 
	/// Because indices start at `1`, this result is equal to the number of
	/// elements in the stack; in particular, `0` means an empty stack.
	pub fn top(&self) -> c_int {
		unsafe { lua_gettop(self.as_ptr()) }
	}

	/// Move the top element into the given valid index, shifting up the
	/// elements above that index to open space.
	/// 
	/// This function cannot be called with a pseudo-index, because a
	/// pseudo-index is not an actual stack position.
	pub fn insert(&self, index: c_int) {
		unsafe { lua_insert(self.as_ptr(), index) }
	}

	lua_is! {
		/// Return `true` if the value at the given index is a boolean.
		pub fn is_boolean(&self, index: c_int) -> bool for lua_isboolean -> bool;
	
		/// Return `true` if the value at the given index is a C function.
		pub fn is_c_function(&self, index: c_int) -> bool
			for lua_iscfunction -> c_int;
	
		/// Return `true` if the value at the given index is a function (either
		/// C or Lua).
		pub fn is_function(&self, index: c_int) -> bool
			for lua_isfunction -> bool;
	
		/// Return `true` if the value at the given index is an integer.
		pub fn is_integer(&self, index: c_int) -> bool
			for lua_isinteger -> c_int;
	
		/// Return `true` if the value at the given index is a light userdata.
		pub fn is_light_userdata(&self, index: c_int) -> bool
			for lua_islightuserdata -> bool;
	
		/// Return `true` if the value at the given index is `nil`.
		pub fn is_nil(&self, index: c_int) -> bool for lua_isnil -> bool;
	
		/// Return `true` if the value at the given index is not valid.
		pub fn is_none(&self, index: c_int) -> bool for lua_isnone -> bool;
	
		/// Return `true` if the value at the given index is not valid or is
		/// `nil`.
		pub fn is_none_or_nil(&self, index: c_int) -> bool
			for lua_isnoneornil -> bool;
		/// Return `true` if the value at the given index is a number.
	
		pub fn is_number(&self, index: c_int) -> bool for lua_isnumber -> c_int;
	
		/// Return `true` if the value at the given index is a string *or* a
		/// number, which is always convertible to a string.
		pub fn is_string(&self, index: c_int) -> bool for lua_isstring -> c_int;
	
		/// Return `true` if the value at the given index is a table.
		pub fn is_table(&self, index: c_int) -> bool for lua_istable -> bool;
	
		/// Return `true` if the value at the given index is a thread.
		pub fn is_thread(&self, index: c_int) -> bool for lua_isthread -> bool;
	
		/// Return `true` if the value at the given index is a userdata (either
		/// full or light).
		pub fn is_userdata(&self, index: c_int) -> bool
			for lua_isuserdata -> c_int;
	}

	/// Return `true` if the coroutine can yield.
	pub fn can_yield(&self) -> bool {
		(unsafe { lua_isyieldable(self.as_ptr()) }) != 0
	}

	/// Load a Lua chunk without running it.
	/// 
	/// If there are no errors, push the compiled chunk as a Lua function.
	/// Otherwise, push an error message.
	/// 
	/// This function uses a user-supplied `reader` to read the chunk (see also
	/// [`Reader`]).
	/// `reader_data` is an opaque value passed to the reader function.
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
	/// 
	/// # Safety
	/// `reader_data` must be valid to be passed to `reader`.
	pub unsafe fn load(
		&self,
		reader: Reader, reader_data: *mut c_void,
		chunk_name: &CStr, mode: Option<&CStr>
	) -> Status {
		unsafe { Status::from_c_int_unchecked(
			lua_load(
				self.as_ptr(),
				reader, reader_data,
				chunk_name.as_ptr(),
				mode.map(|cstr| cstr.as_ptr()).unwrap_or(null())
			)
		) }
	}

	/// Create a new empty table and push it onto the stack.
	/// 
	/// See also [`Thread::create_table`].
	/// 
	/// # Errors
	/// The underlying Lua state may raise a memory [error](crate::errors).
	pub fn new_table(&self) {
		unsafe { lua_newtable(self.as_ptr()) }
	}

	/// Create a new thread, push it on the stack, and return a [`Coroutine`]
	/// that represents this new thread.
	/// 
	/// The new thread returned by this function shares with the original thread
	/// its global environment, but has an independent execution stack.
	/// Threads are subject to garbage collection, like any Lua object.
	/// 
	/// # Errors
	/// The underlying Lua state may raise a memory [error](crate::errors).
	pub fn new_thread(&self) -> Coroutine<'_> {
		Coroutine::new(unsafe { Thread::from_ptr_mut(lua_newthread(self.as_ptr())) })
	}

	/// Create and push on the stack a new full userdata, with `n_uservalues`
	/// associated Lua values, called user values, and an associated block of
	/// raw memory of `size` bytes.
	/// 
	/// The function returns a pointer to the block of memory that was allocated
	/// by Lua.
	/// 
	/// The user values can be set and read with the functions
	/// [`Thread::set_i_uservalue`] and [`Thread::get_i_uservalue`].
	/// 
	/// You may use this function if, for instance, the layout of the data in
	/// the allocation changes based on run-time information.
	/// 
	/// # Errors
	/// The underlying Lua state may raise a memory [error](crate::errors).
	/// 
	/// # Safety
	/// Lua ensures that the pointer is valid as long as the corresponding userdata is alive.
	/// Moreover, if the userdata is marked for finalization,
	/// it is valid at least until the call to its finalizer.
	/// The returned pointer must only be used while it's valid.
	/// 
	/// Lua makes no guarantees about the alignment of the pointer.
	/// It depends entirely on the allocator function used.
	pub unsafe fn new_userdata_raw(
		&self,
		size: usize,
		n_uservalues: c_int,
	) -> *mut c_void {
		unsafe { lua_newuserdatauv(self.as_ptr(), size, n_uservalues) }
	}
	
	/// Pop a key from the stack, and push a key–value pair from the table at
	/// the given index, the "next" pair after the given key.
	/// 
	/// This function returns `true` while there are still elements to go
	/// through. If there are no more elements in the table, then this it
	/// returns `false` and pushes nothing.
	/// 
	/// # Note on string conversion functions
	/// While traversing a table, avoid calling [`Thread::to_c_chars`] directly
	/// on a key, unless it is known that the key is actually a **string**.
	/// [`Thread::to_c_chars`] and other similar functions may change the value
	/// at the given index; this confuses the next call to [`Thread::next`].
	/// 
	/// # Errors
	/// The underlying Lua state may raise an [error](crate::errors)
	/// if a given key is neither `nil` nor present in the table.
	pub fn next(&self, index: c_int) -> bool {
		(unsafe { lua_next(self.as_ptr(), index) }) != 0
	}

	/// Push a [`bool`] onto the stack.
	pub fn push_boolean(&self, value: bool) {
		unsafe { lua_pushboolean(self.as_ptr(), if value { 1 } else { 0 }) }
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
	///    (When there are multiple upvalues, the first value is pushed first.)
	/// 2. Call this function with the argument `n_upvalues`
	///    telling how many upvalues will be associated with the function.
	///    The function will also pop these values from the stack.
	/// 
	/// When `n_upvalues == 0`, this function creates a "light" C function,
	/// which is just a pointer to the C function. In that case, it never raises
	/// a memory error.
	/// 
	/// See also [`Thread::push_c_function`].
	/// 
	/// # Errors
	/// The underlying Lua state may raise a memory [error](crate::errors) if `n_upvalues > 0`.
	pub fn push_c_closure(&self, func: CFunction, n_upvalues: c_int) {
		unsafe { lua_pushcclosure(self.as_ptr(), func, n_upvalues) }
	}

	/// Push a light C function onto the stack (that is, a C function with no
	/// upvalues).
	/// 
	/// See also [`Thread::push_c_closure`].
	pub fn push_c_function(&self, func: CFunction) {
		unsafe { lua_pushcfunction(self.as_ptr(), func) }
	}

	/// Push the global environment onto the stack.
	pub fn push_global_table(&self) {
		unsafe { lua_pushglobaltable(self.as_ptr()) }
	}

	/// Push an [`Integer`] onto the stack.
	pub fn push_integer(&self, value: Integer) {
		unsafe { lua_pushinteger(self.as_ptr(), value) }
	}

	/// Push a light userdata onto the stack.
	/// 
	/// A light userdata represents a plain pointer.
	/// It is a value, like a number:
	/// it is not created, it has no individual metatable,
	/// and it is not collected (as it was never created).
	/// 
	/// A light userdata is equal to any light userdata with the same C address.
	/// 
	/// # Safety
	/// `ptr` can be used arbitrarily in Lua,
	/// so this method should only be used for trusted code.
	pub unsafe fn push_light_userdata(&self, ptr: *mut c_void) {
		unsafe { lua_pushlightuserdata(self.as_ptr(), ptr) }
	}

	/// Works the same as [`Thread::push_string`], however it accepts
	/// [`c_char`]s instead of [`u8`]s.
	/// 
	/// # Errors
	/// The underlying Lua state may raise a memory [error](crate::errors).
	pub fn push_c_chars<'l>(&'l self, data: &[c_char]) -> &'l [c_char] {
		let length = data.len();
		unsafe { from_raw_parts(
			lua_pushlstring(self.as_ptr(), data.as_ptr(), length),
			length
		) }
	}

	/// Push a string onto the stack.
	/// 
	/// The string can contain any binary data, including embedded zeros.
	/// 
	/// Lua will make or reuse an internal copy of the given string, so the
	/// memory pointed to by `data` can be safely freed or reused immediately
	/// after the function returns.
	/// 
	/// See also [`Thread::push_c_chars`].
	/// 
	/// # Errors
	/// The underlying Lua state may raise a memory [error](crate::errors).
	pub fn push_string(&self, data: impl AsRef<[u8]>) -> &[u8] {
		let slice = data.as_ref();
		let length = slice.len();
		unsafe { from_raw_parts(
			lua_pushlstring(
				self.as_ptr(),
				slice.as_ptr() as *const _, length
			) as *const _,
			length
		) }
	}

	/// Push `nil` onto the stack.
	pub fn push_nil(&self) {
		unsafe { lua_pushnil(self.as_ptr()) }
	}

	/// Push a [`Number`] onto the stack.
	pub fn push_number(&self, value: Number) {
		unsafe { lua_pushnumber(self.as_ptr(), value) }
	}

	/// Push a zero-terminated string onto the stack.
	/// 
	/// Lua will make or reuse an internal copy of the given string, so the
	/// memory pointed to by `data` can be freed or reused immediately after the
	/// function returns.
	/// 
	/// See also [`Thread::push_c_chars`] and [`Thread::push_string`].
	/// 
	/// # Errors
	/// The underlying Lua state may raise a memory [error](crate::errors).
	pub fn push_c_str<'l>(&'l self, data: &CStr) -> &'l CStr {
		unsafe { CStr::from_ptr(
			lua_pushstring(self.as_ptr(), data.as_ptr())
		) }
	}

	/// Push the Lua thread represented by this [`Thread`] onto its own stack,
	/// and return `true` if this thread is the main thread
	/// (see also [`Lua`](crate::Lua)).
	pub fn push_thread(&self) -> bool {
		(unsafe { lua_pushthread(self.as_ptr()) }) != 0
	}

	/// Push a copy of the element at the given index onto the stack.
	pub fn push_value(&self, index: c_int) {
		unsafe { lua_pushvalue(self.as_ptr(), index) }
	}

	/// Return `true` if the two values in indices `idx_a` and `idx_b` are
	/// primitively equal (that is, equal without calling the `__eq` metamethod).
	/// 
	/// This also returns `false` if any of the indices are not valid.
	pub fn raw_equal(&self, idx_a: c_int, idx_b: c_int) -> bool {
		(unsafe { lua_rawequal(self.as_ptr(), idx_a, idx_b) }) != 0
	}

	/// Without calling metamethods, push `t[k]`, where `t` is the value at the
	/// given index and `k` is the value on the top of the stack.
	/// 
	/// # Safety
	/// The value at `tbl_index` must be a table.
	pub unsafe fn raw_get(&self, tbl_index: c_int) -> Type {
		unsafe { Type::from_c_int_unchecked(
			lua_rawget(self.as_ptr(), tbl_index)
		) }
	}

	/// Without calling metamethods, push `t[i]`, where `t` is the value at the
	/// given index.
	/// 
	/// # Safety
	/// The value at `tbl_index` must be a table.
	pub unsafe fn raw_get_i(&self, tbl_index: c_int, i: Integer) -> Type {
		unsafe { Type::from_c_int_unchecked(
			lua_rawgeti(self.as_ptr(), tbl_index, i)
		) }
	}

	/// Without calling metamethods, push `t[ptr]`, where `t` is the value at
	/// the given index and `ptr` is the given pointer represented as a light
	/// userdata.
	/// 
	/// # Safety
	/// The value at `tbl_index` must be a table.
	pub unsafe fn raw_get_p(&self, tbl_index: c_int, ptr: *const c_void) -> Type {
		unsafe { Type::from_c_int_unchecked(
			lua_rawgetp(self.as_ptr(), tbl_index, ptr)
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
	pub fn raw_length(&self, index: c_int) -> Unsigned {
		unsafe { lua_rawlen(self.as_ptr(), index) }
	}

	/// Without metamethods, do `t[k] = v`, where `t` is the value at the given
	/// index, `v` is the value on the top of the stack, and `k` is the value
	/// just below the top.
	/// 
	/// # Errors
	/// The underlying Lua state may raise a memory [error](crate::errors).
	/// 
	/// # Safety
	/// The value at `tbl_index` must be a table.
	pub unsafe fn raw_set(&self, tbl_index: c_int) {
		unsafe { lua_rawset(self.as_ptr(), tbl_index) }
	}

	/// Without metamethods, do `t[i] = v`, where `t` is the value at the given
	/// index and `v` is the value on the top of the stack.
	/// 
	/// # Errors
	/// The underlying Lua state may raise a memory [error](crate::errors).
	/// 
	/// # Safety
	/// The value at `tbl_index` must be a table.
	pub unsafe fn raw_set_i(&self, tbl_index: c_int, i: Integer) {
		unsafe { lua_rawseti(self.as_ptr(), tbl_index, i) }
	}

	/// Without metamethods, do `t[ptr] = v`, where `t` is the value at the
	/// given index, `v` is the value on the top of the stack, and `ptr` is the
	/// given pointer represented as a light userdata.
	/// 
	/// # Errors
	/// The underlying Lua state may raise a memory [error](crate::errors).
	/// 
	/// # Safety
	/// The value at `tbl_index` must be a table.
	pub unsafe fn raw_set_p(&self, tbl_index: c_int, ptr: *const c_void) {
		unsafe { lua_rawsetp(self.as_ptr(), tbl_index, ptr) }
	}

	/// Remove the element at the given valid index, shifting down the elements
	/// above this index to fill the gap.
	/// 
	/// This function cannot be called with a pseudo-index, because a
	/// pseudo-index is not an actual stack position.
	pub fn remove(&self, index: c_int) {
		unsafe { lua_remove(self.as_ptr(), index) }
	}

	/// Move the top element into the given valid index without shifting any
	/// element (therefore replacing the value at that given index),
	/// and then pop that top element.
	pub fn replace(&self, index: c_int) {
		unsafe { lua_replace(self.as_ptr(), index) }
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
	pub fn rotate(&self, index: c_int, n_values: c_int) {
		unsafe { lua_rotate(self.as_ptr(), index, n_values) }
	}

	/// Pop a value from the stack and set it as the new value of global `name`.
	/// 
	/// # Errors
	/// The underlying Lua state may raise an arbitrary [error](crate::errors).
	pub fn set_global(&self, key: &CStr) {
		unsafe { lua_setglobal(self.as_ptr(), key.as_ptr()) }
	}

	/// Pop a value from the stack and set it as the new `n`-th user value
	/// associated to the full userdata at the given index.
	/// 
	/// Returns `false` if the userdata does not have that value.
	pub fn set_i_uservalue(&self, ud_index: c_int, n: c_int) -> bool {
		(unsafe { lua_setiuservalue(self.as_ptr(), ud_index, n) }) != 0
	}

	/// Pop a table or `nil` from the stack and sets that value as the new
	/// metatable for the value at the given index. (`nil` means no metatable.)
	// NOTE: `lua_setmetatable` always returns a `1`, which isn't useful.
	pub fn set_metatable(&self, obj_index: c_int) {
		unsafe { lua_setmetatable(self.as_ptr(), obj_index) };
	}

	/// Set the warning function to be used by Lua to emit warnings
	/// (see [`WarnFunction`]).
	/// 
	/// See also [`Thread::remove_warn_fn`].
	/// 
	/// # Safety
	/// `warn_data` is the custom data to be passed to the warning function.
	/// It must be valid for `warn`.
	pub unsafe fn set_warn_fn(&self, warn: WarnFunction, warn_data: *mut c_void) {
		unsafe { lua_setwarnf(self.as_ptr(), Some(warn), warn_data) }
	}

	/// Remove the warning function to be used by Lua to emit warnings.
	/// 
	/// See also [`Thread::set_warn_fn`].
	pub fn remove_warn_fn(&self) {
		unsafe { lua_setwarnf(self.as_ptr(), None, null_mut()) }
	}

	/// Return the status of the Lua thread represented by this [`Thread`].
	/// 
	/// The status can be [`Status::Ok`] for a normal thread, an error variant
	/// if the thread finished the execution of a [`Managed::resume`] with an
	/// error, or [`Status::Yielded`] if the thread is suspended.
	/// 
	/// Functions can only be called in threads with status [`Status::Ok`].
	/// Threads with status [`Status::Ok`] or [`Status::Yielded`] can be resumed
	/// (to start a new coroutine or resume an existing one). 
	pub fn status(&self) -> Status {
		unsafe { Status::from_c_int_unchecked(lua_status(self.as_ptr())) }
	}

	/// Convert the Lua value at the given index to a [`bool`].
	/// 
	/// Like all tests in Lua, this returns `true` for any Lua value different
	/// from `false` and `nil`; otherwise it returns `false`.
	/// 
	/// If you want to accept only actual boolean values, use
	/// [`Thread::is_boolean`] to test the value's type first.
	pub fn to_boolean(&self, idx: c_int) -> bool {
		(unsafe { lua_toboolean(self.as_ptr(), idx) }) != 0
	}

	/// Convert a value at the given index to a C function.
	/// If it is not one, return `None`.
	pub fn to_c_function(&self, index: c_int) -> Option<CFunction> {
		unsafe { lua_tocfunction(self.as_ptr(), index) }
	}

	/// Mark the given index in the stack as a to-be-closed slot.
	/// 
	/// Like a to-be-closed variable in Lua, the value at that slot in the stack
	/// will be closed when it goes out of scope.
	/// Here, in the context of a C function, to go out of scope means that the
	/// running function returns to Lua, or there is an error, or the slot is
	/// removed from the stack through [`Managed::set_top`] or [`Managed::pop`],
	/// or there is a call to [`Managed::close_slot`].
	/// 
	/// A slot marked as to-be-closed should not be removed from the stack by
	/// any other function in the API except [`Managed::set_top`] or
	/// [`Managed::pop`], unless previously deactivated by [`Managed::close_slot`].
	/// 
	/// # Errors
	/// The underlying Lua state may raise a memory [error](crate::errors).
	/// 
	/// # Safety
	/// This function should not be called for an index that is equal to or
	/// below an active to-be-closed slot.
	/// 
	/// Note that, both in case of errors and of a regular return, by the time
	/// the `__close` metamethod runs, the C stack was already unwound, so that
	/// any automatic C variable declared in the calling function
	/// (e.g., a buffer) will be out of scope.
	pub unsafe fn to_close(&self, index: c_int) {
		unsafe { lua_toclose(self.as_ptr(), index) }
	}

	/// This behaves exactly the same as [`Thread::to_integer_opt`], however the
	/// return value is `0` if an integer isn't present.
	pub fn to_integer(&self, idx: c_int) -> Integer {
		unsafe { lua_tointeger(self.as_ptr(), idx) }
	}

	/// Convert the Lua value at the given index to the signed integral type
	/// [`Integer`].
	/// 
	/// The Lua value must be an integer, or a number or string convertible to
	/// an integer. Otherwise, this function returns `None`.
	pub fn to_integer_opt(&self, idx: c_int) -> Option<Integer> {
		let mut is_num = 0;
		let result = unsafe { lua_tointegerx(self.as_ptr(), idx, &mut is_num as *mut _) };
		(is_num != 0).then_some(result)
	}

	/// Convert the Lua value at the given index to a slice of [`c_char`]s,
	/// representing a Lua string.
	/// 
	/// This function works like [`Thread::to_string`].
	/// 
	/// # Errors
	/// The underlying Lua state may raise a memory [error](crate::errors).
	pub fn to_c_chars(&self, index: c_int) -> Option<&[c_char]> {
		let mut len = 0;
		let str_ptr = unsafe { lua_tolstring(self.as_ptr(), index, &mut len as *mut _) };
		if !str_ptr.is_null() {
			Some(unsafe { from_raw_parts(str_ptr, len) })
		} else {
			None
		}
	}

	/// Convert the Lua value at the given index to a [`CStr`],
	/// representing a Lua string.
	/// 
	/// This function works like [`Thread::to_string`].
	/// 
	/// # Errors
	/// The underlying Lua state may raise a memory [error](crate::errors).
	pub fn to_c_str(&self, index: c_int) -> Option<&CStr> {
		let str_ptr = unsafe { lua_tostring(self.as_ptr(), index) };
		if !str_ptr.is_null() {
			Some(unsafe { CStr::from_ptr(str_ptr) })
		} else {
			None
		}
	}

	/// Convert the Lua value at the given index to a slice of [`u8`]s,
	/// representing a Lua string.
	/// 
	/// The Lua value must be a string or a number; otherwise, the function
	/// returns `None`.
	/// 
	/// If the value is a number, then this function also changes the *actual
	/// value in the stack* to a string.
	/// 
	/// The function returns a slice to data inside the Lua state.
	/// This string always has a zero (`'\0'`) after its last character (as in C),
	/// but can contain other zeros in its body.
	/// 
	/// # Errors
	/// The underlying Lua state may raise a memory [error](crate::errors).
	pub fn to_string(&self, index: c_int) -> Option<&[u8]> {
		let mut len = 0;
		let str_ptr = unsafe { lua_tolstring(self.as_ptr(), index, &mut len as *mut _) };
		if !str_ptr.is_null() {
			Some(unsafe { from_raw_parts(str_ptr as *const _, len) })
		} else {
			None
		}
	}

	/// This behaves exactly the same as [`Thread::to_number_opt`], however the
	/// return value is `0.0` if a number isn't present.
	pub fn to_number(&self, idx: c_int) -> Number {
		unsafe { lua_tonumber(self.as_ptr(), idx) }
	}

	/// Convert the Lua value at the given index to the floating-point number
	/// type [`Number`].
	/// 
	/// The Lua value must be a number or string convertible to a number.
	/// Otherwise, this function returns `None`.
	pub fn to_number_opt(&self, idx: c_int) -> Option<Number> {
		let mut is_num = 0;
		let result = unsafe { lua_tonumberx(self.as_ptr(), idx, &mut is_num as *mut _) };
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
	pub fn to_pointer(&self, idx: c_int) -> *const c_void {
		unsafe { lua_topointer(self.as_ptr(), idx) }
	}

	/// Convert the value at the given index to a Lua thread, represented by a
	/// `*mut`[`State`].
	/// 
	/// The value must be a thread; otherwise, the function returns null.
	pub fn to_thread(&self, index: c_int) -> *mut State {
		unsafe { lua_tothread(self.as_ptr(), index) }
	}

	/// If the value at the given index is a light or full userdata, return the
	/// address it represents. Otherwise, return null.
	pub fn to_userdata(&self, idx: c_int) -> *mut c_void {
		unsafe { lua_touserdata(self.as_ptr(), idx) }
	}

	/// Return the type of the value in the given valid index, or [`Type::None`]
	/// for a non-valid but acceptable index.
	pub fn type_of(&self, idx: c_int) -> Type {
		unsafe { Type::from_c_int_unchecked(lua_type(self.as_ptr(), idx)) }
	}

	/// Return the name of the type encoded by `type_tag`.
	pub fn type_name(&self, type_tag: Type) -> &CStr {
		unsafe { CStr::from_ptr(lua_typename(self.as_ptr(), type_tag as _)) }
	}

	/// Return the version number of the Lua core.
	pub fn version(&self) -> Number {
		unsafe { lua_version(self.as_ptr()) }
	}

	/// Emit a warning with the given message.
	/// 
	/// A message in a call with `to_be_continued == true` should be continued
	/// in another call to this function.
	pub fn warning(&self, message: &CStr, to_be_continued: bool) {
		unsafe { lua_warning(
			self.as_ptr(), message.as_ptr(), if to_be_continued { 1 } else { 0 }
		) }
	}

	/// Exchange values between different threads of the same state.
	/// 
	/// This function pops `n_values` values from the stack of this thread, and
	/// pushes them onto the stack of the thread `to`.
	pub fn xmove(&self, to: &Self, n_values: c_uint) {
		unsafe { lua_xmove(self.as_ptr(), to.as_ptr(), n_values as _) }
	}

	/// This behaves exactly like [`Thread::yield_k_with`], however there is no
	/// continuation.
	/// 
	/// # Safety
	/// This function should be called *only* outside of hooks.
	/// It is Undefined Behavior if the code after a call to this function is
	/// reachable.
	pub unsafe fn yield_with(&self, n_results: c_int) -> ! {
		unsafe { lua_yield(self.as_ptr(), n_results) }
	}

	/// This behaves exactly like [`Thread::yield_in_hook_k_with`], however
	/// there is no continuation.
	/// 
	/// # Safety
	/// This function should be called *only* outside of hooks.
	/// It is Undefined Behavior if the code after a call to this function is
	/// unreachable.
	pub unsafe fn yield_in_hook_with(&self, n_results: c_int) {
		unsafe { lua_yield_in_hook(self.as_ptr(), n_results) };
	}

	/// Yield this thread (like a coroutine).
	/// 
	/// When this function is called, the running coroutine suspends its
	/// execution, and the call to [`Managed::resume`] that started this
	/// coroutine returns.
	/// 
	/// The parameter `n_results` is the number of values from the stack that
	/// will be passed as results to [`Managed::resume`].
	/// 
	/// When the coroutine is resumed again, Lua calls the given continuation
	/// function `continuation` to continue the execution of the C function that
	/// yielded.
	/// This continuation function receives the same stack from the previous
	/// function, with the `n_results` results removed and replaced by the
	/// arguments passed to [`Managed::resume`].
	/// Moreover, the continuation function receives the value `context` that
	/// was originally passed.
	/// 
	/// Usually, this function does not return; when the coroutine eventually
	/// resumes, it continues executing the continuation function.
	/// However, there is one special case, which is when this function is
	/// called from inside a line or a count hook (see [`Hook`]).
	/// In that case, [`Thread::yield_in_hook_with`] should be called
	/// (thus, no continuation) and no results, and the hook should return
	/// immediately after the call.
	/// Lua will yield and, when the coroutine resumes again, it will continue
	/// the normal execution of the (Lua) function that triggered the hook.
	/// 
	/// # Errors
	/// The underlying Lua thread can raise an error
	/// if the function is called from a thread with a pending C call
	/// with no continuation function (what is called a C-call boundary),
	/// or it is called from a thread that is not running inside a resume
	/// (typically the main thread).
	/// 
	/// # Safety
	/// This function should be called *only* outside of hooks.
	/// It is Undefined Behavior if the code after a call to this function is
	/// reachable.
	pub unsafe fn yield_k_with(
		&self, n_results: c_int,
		continuation: KFunction, context: KContext
	) -> ! {
		unsafe { lua_yieldk(self.as_ptr(), n_results, context, Some(continuation)) }
	}

	/// This behaves exactly like [`Thread::yield_k_with`], however it should
	/// only be called in hooks.
	/// 
	/// # Errors
	/// The underlying Lua thread can raise an error
	/// if the function is called from a thread with a pending C call
	/// with no continuation function (what is called a C-call boundary),
	/// or it is called from a thread that is not running inside a resume
	/// (typically the main thread).
	/// 
	/// # Safety
	/// This function should be called *only* inside of hooks.
	pub unsafe fn yield_in_hook_k_with(
		&self, n_results: c_int,
		continuation: KFunction, context: KContext
	) {
		unsafe { lua_yieldk_in_hook(
			self.as_ptr(), n_results,
			context, Some(continuation)
		) };
	}

	/// Returns a [`ThreadDebug`] structure that exposes various functions operating on [`struct@Debug`] structures.
	/// 
	/// # Safety
	/// `ID_SIZE` must be the appropriate identifier size for the underlying Lua state.
	/// See [`DEFAULT_ID_SIZE`] for the default.
	pub const unsafe fn debug<const ID_SIZE: usize>(&self) -> ThreadDebug<'_, ID_SIZE> {
		ThreadDebug {
			thread: self,
		}
	}

	/// Return the current hook count.
	pub fn hook_count(&self) -> c_int {
		unsafe { lua_gethookcount(self.as_ptr()) }
	}

	/// Return the current hook mask.
	/// 
	/// See also [`HookMask`].
	pub fn hook_mask(&self) -> HookMask {
		unsafe { HookMask::from_c_int_unchecked(lua_gethookmask(self.as_ptr())) }
	}

	/// Get information about the `n`-th upvalue of the closure at index
	/// `func_index`.
	/// 
	/// This function pushes the upvalue's value onto the stack and returns its
	/// name. Returns `None` (and pushes nothing) when the index `n` is greater
	/// than the number of upvalues.
	pub fn get_upvalue(&self, func_index: c_int, n: u8) -> Option<&CStr> {
		let str_ptr = unsafe { lua_getupvalue(self.as_ptr(), func_index, n as _) };
		if !str_ptr.is_null() {
			Some(unsafe { CStr::from_ptr(str_ptr) })
		} else {
			None
		}
	}

	/// Set the value of a closure's upvalue and return its name.
	/// 
	/// Returns `None` (and pops nothing) when the index `n` is greater than the
	/// number of upvalues. 
	/// 
	/// This function assigns the value on the top of the stack to the upvalue.
	/// It also pops the value from the stack.
	pub fn set_upvalue(&self, func_index: c_int, n: u8) -> Option<&CStr> {
		let name_ptr = unsafe { lua_setupvalue(self.as_ptr(), func_index, n as _) };
		if !name_ptr.is_null() {
			unsafe { Some(CStr::from_ptr(name_ptr)) }
		} else {
			None
		}
	}

	/// Return a unique identifier for the upvalue numbered `n` from the closure
	/// at index `func_index`.
	/// 
	/// These unique identifiers allow a program to check whether different
	/// closures share upvalues.
	/// Lua closures that share an upvalue (that is, that access a same external
	/// local variable) will return identical ids for those upvalue indices. 
	/// 
	/// # Safety
	/// The returned pointer may only be used for comparisons.
	pub unsafe fn upvalue_id(&self, func_index: c_int, n: u8) -> *mut c_void {
		unsafe { lua_upvalueid(self.as_ptr(), func_index, n as _) }
	}

	/// Make the
	/// `n_into`-th upvalue of the Lua closure at index `func_into_index`
	/// refer to the
	/// `n_from`-th upvalue of the Lua closure at index `func_from_index`.
	pub fn upvalue_join(
		&self,
		func_into_index: i32, n_into: u8,
		func_from_index: i32, n_from: u8,
	) {
		unsafe { lua_upvaluejoin(
			self.as_ptr(),
			func_into_index, n_into as _,
			func_from_index, n_from as _
		) }
	}
}

#[cfg(feature = "auxlib")]
impl Thread {
	/// Construct a new [`Buffer`] that's initialized with this [`Thread`].
	pub fn new_buffer(&self) -> Buffer<'_> {
		unsafe { Buffer::new_in_raw(self.as_ptr()) }
	}

	/// Raise an error reporting a problem with argument arg of the C function
	/// that called it, using a standard message that includes `extra_message`
	/// as a comment:
	/// 
	/// `bad argument #<argument> to '<function name>' (<message>)`
	/// 
	/// This function never returns. 
	pub fn arg_error(&self, arg: c_int, extra_message: &CStr) -> ! {
		unsafe { luaL_argerror(self.as_ptr(), arg, extra_message.as_ptr()) }
	}

	/// Check whether the function has an argument of any type (including `nil`)
	/// at position `arg`.
	/// 
	/// # Errors
	/// The underlying Lua state may raise an [error](crate::errors) if the
	/// argument `arg`'s type is incorrect.
	pub fn check_any(&self, arg: c_int) {
		unsafe { luaL_checkany(self.as_ptr(), arg) }
	}

	/// Check whether the function argument `arg` is an integer (or can be
	/// converted to an integer) and return this integer.
	/// 
	/// # Errors
	/// The underlying Lua state may raise an [error](crate::errors) if the
	/// argument `arg`'s type is incorrect.
	pub fn check_integer(&self, arg: c_int) -> Integer {
		unsafe { luaL_checkinteger(self.as_ptr(), arg) }
	}

	/// Check whether the function argument `arg` is a string and returns this
	/// string represented as a slice of [`c_char`]s.
	/// 
	/// # Errors
	/// The underlying Lua state may raise an [error](crate::errors) if the
	/// argument `arg` isn't a string.
	pub fn check_c_chars(&self, arg: c_int) -> &[c_char] {
		let mut len = 0;
		let str_ptr = unsafe { luaL_checklstring(self.as_ptr(), arg, &mut len as *mut _) };
		unsafe { from_raw_parts(str_ptr, len) }
	}

	/// Works the same as [`Thread::check_c_chars`], however it returns a slice
	/// of [`u8`]s instead of [`c_char`]s.
	/// 
	/// # Errors
	/// The underlying Lua state may raise an [error](crate::errors) if the
	/// argument `arg` isn't a string.
	pub fn check_string(&self, arg: c_int) -> &[u8] {
		let mut len = 0;
		let str_ptr = unsafe { luaL_checklstring(self.as_ptr(), arg, &mut len as *mut _) };
		unsafe { from_raw_parts(str_ptr as *const _, len) }
	}

	/// Check whether the function argument `arg` is a number and return this
	/// number converted to a [`Number`].
	/// 
	/// # Errors
	/// The underlying Lua state may raise an [error](crate::errors) if the
	/// argument `arg`'s type is incorrect.
	pub fn check_number(&self, arg: c_int) -> Number {
		unsafe { luaL_checknumber(self.as_ptr(), arg) }
	}

	/// Check whether the function argument `arg` is a string, search for this
	/// string in the option list `list` and return the index in the list where
	/// the string was found.
	/// 
	/// If `default` is `Some`, the function uses it as a default value when
	/// there is no argument `arg` or when this argument is `nil`.
	/// 
	/// This is a useful function for mapping strings to C enums.
	/// (The usual convention in Lua libraries is to use strings instead of
	/// numbers to select options.)
	/// 
	/// # Errors
	/// The underlying Lua state may raise an [error](crate::errors) if the
	/// argument `arg` is not a string or if the string cannot be found in `list`. 
	pub fn check_option<const N: usize>(
		&self, arg: c_int,
		default: Option<&CStr>,
		list: &AuxOptions<'_, N>
	) -> usize {
		(unsafe { luaL_checkoption(
			self.as_ptr(), arg,
			default.map(|cstr| cstr.as_ptr()).unwrap_or(null()),
			list.as_ptr()
		) }) as _
	}

	/// Grow the stack size to `top + size` elements, raising an error if the
	/// stack cannot grow to that size.
	/// 
	/// `message` is an additional text to go into the error message
	/// (or `None` for no additional text).
	/// 
	/// # Errors
	/// The underlying Lua state may raise an [error](crate::errors) if the
	/// Lua stack cannot grow to the given size.
	pub fn check_stack(&self, size: c_int, message: Option<&CStr>) {
		unsafe { luaL_checkstack(
			self.as_ptr(),
			size,
			message.map(|cstr| cstr.as_ptr()).unwrap_or(null())
		) }
	}

	/// Check whether the function argument `arg` is a string and return this
	/// string represented by a [`CStr`].
	/// 
	/// # Errors
	/// The underlying Lua state may raise an [error](crate::errors) if the
	/// argument `arg` isn't a string.
	pub fn check_c_str(&self, arg: c_int) -> &CStr {
		let str_ptr = unsafe { luaL_checkstring(self.as_ptr(), arg) };
		unsafe { CStr::from_ptr(str_ptr) }
	}

	/// Check whether the function argument `arg` has type `type_tag`.
	/// 
	/// See also [`Type`].
	/// 
	/// # Errors
	/// The underlying Lua state may raise an [error](crate::errors) if the
	/// argument `arg`'s type is incorrect.
	pub fn check_type(&self, arg: c_int, type_tag: Type) {
		unsafe { luaL_checktype(self.as_ptr(), arg, type_tag as _) }
	}

	/// Check whether the function argument `arg` is a userdata of the type
	/// `table_name` (see also [`Thread::new_metatable`]) and return the
	/// userdata's memory-block address (see [`Thread::to_userdata`]).
	/// 
	/// # Errors
	/// The underlying Lua state may raise an [error](crate::errors) if the
	/// argument `arg`'s type is incorrect.
	/// 
	/// # Safety
	/// The returned pointer must only be used while it's valid.
	/// 
	/// While the metatable of userdata is protected from modification in the Lua standard library,
	/// an unsound implementation of setting the metatable of an object in Lua could change a userdatum's metatable
	/// and make the check for the `table_name` metatable unsound.
	pub unsafe fn check_udata(&self, arg: c_int, table_name: &CStr) -> NonNull<c_void> {
		unsafe { NonNull::new_unchecked(luaL_checkudata(self.as_ptr(), arg, table_name.as_ptr())) }
	}

	/// Check whether the code making the call and the Lua library being called
	/// are using the same version of Lua and the same numeric types.
	/// 
	/// # Errors
	/// The underlying Lua state may raise an [error](crate::errors) if the
	/// above requirements aren't met.
	pub fn check_version(&self) {
		unsafe { luaL_checkversion(self.as_ptr()) }
	}

	/// Raise an error.
	/// 
	/// This function adds the file name and the line number where the error
	/// occurred at the beginning of `message`, if this information is available.
	/// 
	/// This function never returns.
	pub fn error_c_str(&self, message: &CStr) -> ! {
		unsafe { luaL_error(
			self.as_ptr(),
			c"%s".as_ptr(),
			message.as_ptr()
		) }
	}

	/// Produce the return values for process-related functions in the standard
	/// library (`os.execute` and `io.close`).
	/// 
	/// # Errors
	/// The underlying Lua state may raise a memory [error](crate::errors).
	pub fn exec_result(&self, status: c_int) -> c_int {
		unsafe { luaL_execresult(self.as_ptr(), status) }
	}

	/// Produce the return values for file-related functions in the standard
	/// library (`io.open`, `os.rename`, `file:seek`, etc.).
	/// 
	/// # Errors
	/// The underlying Lua state may raise a memory [error](crate::errors).
	pub fn file_result(&self, status: c_int, file_name: &CStr) -> c_int {
		unsafe { luaL_fileresult(self.as_ptr(), status, file_name.as_ptr()) }
	}
	
	/// Push onto the stack the field `event` from the metatable of the object
	/// at index `obj_index` and return the type of the pushed value.
	/// 
	/// If the object does not have a metatable, or if the metatable does not
	/// have this field, this function pushes nothing and returns [`Type::Nil`].
	/// 
	/// # Errors
	/// The underlying Lua state may raise a memory [error](crate::errors).
	pub fn get_meta_field(&self, obj_index: c_int, event: &CStr) -> Type {
		unsafe { Type::from_c_int_unchecked(luaL_getmetafield(
			self.as_ptr(), obj_index, event.as_ptr()
		)) }
	}

	/// Push onto the stack the metatable associated with the name `table_name`
	/// in the registry (see also [`Thread::new_metatable`]), or `nil` if there
	/// is no metatable associated with that name, and return the type of the
	/// pushed value.
	/// 
	/// # Errors
	/// The underlying Lua state may raise a memory [error](crate::errors).
	pub fn get_aux_metatable(&self, table_name: &CStr) -> Type {
		unsafe { Type::from_c_int_unchecked(luaL_getmetatable(
			self.as_ptr(), table_name.as_ptr()
		)) }
	}

	/// Load a buffer as a Lua chunk.
	/// 
	/// This function works like [`Thread::load_string`].
	pub fn load_c_chars(&self, buffer: &[c_char], name: &CStr) -> Status {
		unsafe { Status::from_c_int_unchecked(
			luaL_loadbuffer(
				self.as_ptr(),
				buffer.as_ptr(), buffer.len(),
				name.as_ptr()
			)
		) }
	}

	/// Load a buffer as a Lua chunk.
	/// 
	/// This function uses [`Thread::load`] to load the chunk in the buffer
	/// pointed to by `buffer`, and will return the same results as that
	/// function.
	/// 
	/// `name` is the chunk name, used for debug information and error messages.
	// /// The string mode works as in the function lua_load. 
	pub fn load_string(&self, buffer: impl AsRef<[u8]>, name: &CStr) -> Status {
		let slice = buffer.as_ref();
		unsafe { Status::from_c_int_unchecked(
			luaL_loadbuffer(
				self.as_ptr(),
				slice.as_ptr() as *const _, slice.len(),
				name.as_ptr()
			)
		) }
	}

	/// Load a file as a Lua chunk.
	/// 
	/// This function uses [`Thread::load`] to load the chunk in the file 
	/// `file_name`.
	/// 
	/// The first line in the file is ignored if it starts with a #.
	/// 
	/// # Errors
	/// The underlying Lua state may raise a memory [error](crate::errors).
	pub fn load_file(&self, file_name: &CStr) -> Status {
		unsafe { Status::from_c_int_unchecked(
			luaL_loadfile(self.as_ptr(), file_name.as_ptr())
		) }
	}

	/// Load a Lua chunk from the standard input.
	/// 
	/// This function uses [`Thread::load`] to load the chunk.
	/// 
	/// The first line in the file is ignored if it starts with a `#`.
	/// 
	/// # Errors
	/// The underlying Lua state may raise a memory [error](crate::errors).
	pub fn load_stdin(&self) -> Status {
		unsafe { Status::from_c_int_unchecked(
			luaL_loadfile(self.as_ptr(), null())
		) }
	}

	/// Load a string as a Lua chunk.
	/// 
	/// This function uses [`Thread::load`] to load `code`.
	pub fn load_c_str(&self, code: &CStr) -> Status {
		unsafe { Status::from_c_int_unchecked(
			luaL_loadstring(self.as_ptr(), code.as_ptr())
		) }
	}

	/// Create a new table and register there the functions in the list `library`.
	/// 
	/// _Unlike_ this function's C counterpart, this will _not_ call
	/// [`Thread::check_version`].
	/// 
	/// # Errors
	/// The underlying Lua state may raise a memory [error](crate::errors).
	pub fn new_lib<const N: usize>(&self, library: &Library<'_, N>) {
		unsafe {
			let l = self.as_ptr();
			lua_createtable(l, 0, N as _);
			luaL_setfuncs(l, library.as_ptr(), 0);
		}
	}

	/// Create a new table with a size optimized to store all entries in
	/// `library`, but does not actually store them.
	/// 
	/// This function is intended to be used in conjunction with
	/// [`Thread::set_funcs`].
	/// 
	/// # Errors
	/// The underlying Lua state may raise a memory [error](crate::errors).
	pub fn new_lib_table<const N: usize>(&self, library: &Library<'_, N>) {
		let _ = library;
		unsafe { lua_createtable(self.as_ptr(), 0, N as _) }
	}

	/// If the registry already doesn't have the key `table_name`, create a new
	/// table to be used as a metatable for userdata and return `true`.
	/// Otherwise, return `false`.
	/// 
	/// In both cases, the function pushes onto the stack the final value
	/// associated with `table_name` in the registry. 
	/// 
	/// The function adds to this new table the pair `__name = table_name`,
	/// adds to the registry the pair `[table_name] = table`, and returns `true`.
	/// 
	/// # Errors
	/// The underlying Lua state may raise a memory [error](crate::errors).
	pub fn new_metatable(&self, table_name: &CStr) -> bool {
		(unsafe { luaL_newmetatable(self.as_ptr(), table_name.as_ptr()) }) != 0
	}

	/// If the function argument `arg` is an integer (or it is convertible to an
	/// integer), return this integer, or return `default`.
	/// 
	/// # Errors
	/// The underlying Lua state may raise an [error](crate::errors) if the
	/// argument `arg` isn't a number, isn't a `nil` and not absent.
	pub fn opt_integer(&self, arg: c_int, default: Integer) -> Integer {
		unsafe { luaL_optinteger(self.as_ptr(), arg, default) }
	}

	/// If the function argument `arg` is a string, return this string, or
	/// return `default`.
	/// 
	/// This function works like [`Thread::opt_string`].
	/// 
	/// # Errors
	/// The underlying Lua state may raise an [error](crate::errors) if the
	/// argument `arg` isn't a string, isn't a `nil` and not absent.
	pub fn opt_c_chars<'l>(
		&'l self, arg: c_int, default: &'l CStr
	) -> &'l [c_char] {
		let mut len = 0;
		let str_ptr = unsafe { luaL_optlstring(
			self.as_ptr(), arg, default.as_ref().as_ptr(),
			&mut len as *mut _
		) };
		unsafe { from_raw_parts(str_ptr, len) }
	}

	/// If the function argument `arg` is a string, return this string, or
	/// return `default`.
	/// 
	/// This function works like [`Thread::opt_string`].
	/// 
	/// # Errors
	/// The underlying Lua state may raise an [error](crate::errors) if the
	/// argument `arg` isn't a string, isn't a `nil` and not absent.
	pub fn opt_c_str<'l>(&'l self, arg: c_int, default: &'l CStr) -> &'l CStr {
		unsafe { CStr::from_ptr(
			luaL_optstring(self.as_ptr(), arg, default.as_ptr())
		) }
	}

	/// If the function argument `arg` is a string, return this string, or
	/// return `default`.
	/// 
	/// This function uses [`Thread::to_string`] to get its result, so all
	/// conversions and caveats of that function apply here. 
	/// 
	/// # Errors
	/// The underlying Lua state may raise an [error](crate::errors) if the
	/// argument `arg` isn't a string, isn't a `nil` and not absent.
	pub fn opt_string<'l>(&'l self, arg: c_int, default: &'l [u8]) -> &'l [u8] {
		let mut len = 0;
		let str_ptr = unsafe { luaL_optlstring(
			self.as_ptr(), arg, default.as_ptr() as *const _,
			&mut len as *mut _
		) };
		unsafe { from_raw_parts(str_ptr as *const _, len) }
	}

	/// If the function argument `arg` is a number, return this number as a
	/// [`Number`], or return `default`.
	/// 
	/// # Errors
	/// The underlying Lua state may raise an [error](crate::errors) if the
	/// argument `arg` isn't a number, isn't a `nil` and not absent.
	pub fn opt_number(&self, arg: c_int, default: Number) -> Number {
		unsafe { luaL_optnumber(self.as_ptr(), arg, default) }
	}

	/// Pushes the `fail` value onto the stack.
	pub fn push_fail(&self) {
		unsafe { luaL_pushfail(self.as_ptr()) }
	}

	/// Create and return a reference, in the table at index `store_index`, for
	/// the object on the top of the stack (popping the object).
	/// 
	/// A reference is a unique integer key.
	/// As long as you do not manually add integer keys into the table
	/// `store_index`, this function ensures the uniqueness of the key it
	/// returns.
	/// 
	/// You can retrieve an object referred by the reference `ref_idx` by
	/// calling [`thread.raw_get_i(store_index, ref_idx)`](Thread::raw_get_i).
	/// See also [`Thread::destroy_ref`], which frees a reference.
	/// 
	/// If the object on the top of the stack is nil, this returns the constant
	/// [`REF_NIL`].
	/// The constant [`NO_REF`] is guaranteed to be different from any reference
	/// returned.
	/// 
	/// # Errors
	/// The underlying Lua state may raise a memory [error](crate::errors).
	pub fn create_ref(&self, store_index: c_int) -> c_int {
		unsafe { luaL_ref(self.as_ptr(), store_index) }
	}

	/// Registers all functions in the list `library` into the table on the top
	/// of the stack (below optional upvalues).
	/// 
	/// When `n_upvalues` is not zero, all functions are created with
	/// `n_upvalues` upvalues, initialized with copies of the values previously
	/// pushed on the stack on top of the library table.
	/// These values are popped from the stack after the registration.
	/// 
	/// See also [`Library`].
	/// 
	/// A value with a `None` value represents a placeholder, which is filled
	/// with `false`.
	/// 
	/// # Errors
	/// The underlying Lua state may raise a memory [error](crate::errors).
	pub fn set_funcs<const N: usize>(&self, library: &Library<'_, N>, n_upvalues: u8) {
		unsafe { luaL_setfuncs(self.as_ptr(), library.as_ptr(), n_upvalues as _) }
	}

	/// Set the metatable of the object on the top of the stack as the metatable
	/// associated with name `table_name` in the registry.
	/// 
	/// See also [`Thread::new_metatable`].
	pub fn set_aux_metatable(&self, table_name: &CStr) {
		unsafe { luaL_setmetatable(self.as_ptr(), table_name.as_ptr()) }
	}

	/// This function works like [`Thread::check_udata`], except that, when the
	/// test fails, it returns `None` instead of raising an error.
	/// 
	/// # Safety
	/// The returned pointer must only be used while it's valid.
	/// 
	/// While the metatable of userdata is protected from modification in the Lua standard library,
	/// an unsound implementation of setting the metatable of an object in Lua could change a userdatum's metatable
	/// and make the check for the `table_name` metatable unsound.
	pub unsafe fn test_udata(&self, arg: c_int, table_name: &CStr) -> Option<NonNull<c_void>> {
		NonNull::new(unsafe {luaL_testudata(self.as_ptr(), arg, table_name.as_ptr())})
	}

	/// Create and push a traceback of the stack of thread `of`.
	/// 
	/// If message is `Some`, it is appended at the beginning of the traceback.
	/// 
	/// `level` tells at which level to start the traceback.
	/// 
	/// # Errors
	/// The underlying Lua state may raise a memory [error](crate::errors).
	pub fn traceback(
		&self, of: &Self,
		message: Option<&CStr>,
		level: c_int
	) {
		unsafe { luaL_traceback(
			self.as_ptr(), of.as_ptr(),
			message.map(|cstr| cstr.as_ptr()).unwrap_or(null()),
			level
		) }
	}

	/// Create and push a traceback of the stack of this thread to its own stack.
	/// 
	/// This function works like [`Thread::traceback`].
	/// 
	/// # Errors
	/// The underlying Lua state may raise a memory [error](crate::errors).
	pub fn traceback_self(&self, message: Option<&CStr>, level: c_int) {
		unsafe { luaL_traceback(
			self.as_ptr(), self.as_ptr(),
			message.map(|cstr| cstr.as_ptr()).unwrap_or(null()),
			level
		) }
	}

	/// Raise a type error for the argument `arg` of the C function that called
	/// it, using a standard message;
	/// `type_name` is a "name" for the expected type.
	/// 
	/// This function never returns.
	pub fn type_error(&self, arg: c_int, type_name: &CStr) -> ! {
		unsafe { luaL_typeerror(self.as_ptr(), arg, type_name.as_ptr()) }
	}

	/// Return the name of the type of the value at the given index.
	pub fn type_name_of(&self, index: c_int) -> &CStr {
		unsafe { CStr::from_ptr(luaL_typename(self.as_ptr(), index)) }
	}

	/// Release the reference `ref_idx` from the table at index `store_index`.
	/// 
	/// If `ref_idx` is [`NO_REF`] or [`REF_NIL`], this function does nothing.
	/// 
	/// The entry is removed from the table, so that the referred object can be
	/// collected.
	/// The reference `ref_idx` is also freed to be used again.
	/// 
	/// See also [`Thread::create_ref`].
	pub fn destroy_ref(&self, store_index: c_int, ref_idx: c_int) {
		unsafe { luaL_unref(self.as_ptr(), store_index, ref_idx) }
	}

	/// Push onto the stack a string identifying the current position of the
	/// control at level `level` in the call stack.
	/// 
	/// Typically, this string has the following format:
	/// 
	/// `chunkname:currentline:`
	/// 
	/// Level `0` is the running function, level `1` is the function that called
	/// the running function, etc.
	/// 
	/// This function is used to build a prefix for error messages.
	/// 
	/// # Errors
	/// The underlying Lua state may raise a memory [error](crate::errors).
	pub fn where_string(&self, level: c_int) {
		unsafe { luaL_where(self.as_ptr(), level) }
	}
}

/// Utility type for operating on [`struct@Debug`] structures.
#[repr(transparent)]
pub struct ThreadDebug<'a, const ID_SIZE: usize> {
	thread: &'a Thread,
}

impl<const ID_SIZE: usize> ThreadDebug<'_, ID_SIZE> {
	/// Return the current hook function.
	/// 
	/// See also [`Hook`].
	pub fn hook_fn(&self) -> Hook<ID_SIZE> {
		let hook_fn = unsafe { lua_gethook(self.thread.as_ptr()) };
		unsafe { transmute(hook_fn) }
	}

	/// Gets information about a specific function or function invocation.
	/// 
	/// See also [`DebugWhat`](crate::dbg_what::DebugWhat) for generating `what`.
	pub fn get_info(&self, what: &CStr, ar: &mut Debug<ID_SIZE>) -> bool {
		(unsafe { lua_getinfo(self.thread.as_ptr(), what.as_ptr(), ar as *mut _ as *mut _) }) != 0
	}

	/// Get information about a local variable or a temporary value of a given
	/// activation record or function.
	/// 
	/// The function pushes the variable's value onto the stack and returns its
	/// name.
	/// It returns `None` (and pushes nothing) when the index is greater than
	/// the number of active local variables. 
	/// 
	/// # Activation records
	/// For activation records, the parameter `ar` must be a valid activation
	/// record that was filled by a previous call to [`ThreadDebug::get_stack`] or
	/// given as argument to a hook (see [`Hook`]).
	/// The index `n` selects which local variable to inspect.
	/// 
	/// # Functions
	/// For functions, `ar` must be `None` and the function to be inspected must
	/// be on the top of the stack.
	/// In this case, only parameters of Lua functions are visible (as there is
	/// no information about what variables are active) and no values are pushed
	/// onto the stack.
	pub fn get_local<'dbg>(&self, ar: Option<&'dbg Debug<ID_SIZE>>, n: c_int) -> Option<&'dbg CStr> {
		let str_ptr = unsafe { lua_getlocal(
			self.thread.as_ptr(),
			ar.map(|ar| ar as *const _ as *const _).unwrap_or(null()),
			n
		) };

		if !str_ptr.is_null() {
			Some(unsafe { CStr::from_ptr(str_ptr) })
		} else {
			None
		}
	}

	/// Set the debugging hook function.
	/// 
	/// `hook` is the hook function.
	/// 
	/// `mask` specifies on which events the hook will be called: it is formed
	/// by [`HookMask`].
	/// 
	/// `count` is only meaningful when the mask includes the count hook
	/// (with [`HookMask::with_instructions`]).
	/// 
	/// For each event, the hook is called as explained below:
	/// - The **call** hook is called when the interpreter calls a function.
	///   The hook is called just after Lua enters the new function.
	/// - The **return** hook is called when the interpreter returns from a function.
	///   The hook is called just before Lua leaves the function.
	/// - The **line** hook is called when the interpreter is about to start the execution of a new line of code,
	///   or when it jumps back in the code (even to the same line).
	///   This event only happens while Lua is executing a Lua function.
	/// - The **count** hook is called after the interpreter executes every `count` instructions.
	///   This event only happens while Lua is executing a Lua function.
	/// 
	/// Hooks are disabled by supplying an empty `mask`.
	pub fn set_hook_fn(&self, hook_fn: Hook<ID_SIZE>, mask: HookMask, count: c_int) {
		let hook_fn = unsafe { transmute::<Hook<ID_SIZE>, Hook<DEFAULT_ID_SIZE>>(hook_fn) };
		unsafe { lua_sethook(self.thread.as_ptr(), hook_fn, mask.into_c_int(), count) }
	}

	/// Get information about the interpreter runtime stack.
	/// 
	/// This function fills parts of a [`struct@Debug`] structure with an
	/// identification of the activation record of the function executing at a
	/// given level.
	/// 
	/// Level `0` is the current running function, whereas level `n + 1` is the
	/// function that has called level `n` (except for tail calls, which do not
	/// count in the stack).
	/// When called with a level greater than the stack depth, this function
	/// returns `None`.
	pub fn get_stack(&self, level: c_int) -> Option<Debug<ID_SIZE>> {
		let mut ar = Debug::<ID_SIZE>::zeroed();
		if unsafe { lua_getstack(self.thread.as_ptr(), level, &mut ar as *mut _ as *mut _) } != 0 {
			Some(ar)
		} else {
			None
		}
	}

	/// Set the value of a local variable of a given activation record and
	/// return its name.
	/// 
	/// Returns `None` (and pops nothing) when the index is greater than the
	/// number of active local variables. 
	/// 
	/// This function assigns the value on the top of the stack to the variable.
	/// It also pops the value from the stack.
	pub fn set_local<'dbg>(&self, ar: &'dbg Debug<ID_SIZE>, n: c_int) -> Option<&'dbg CStr> {
		let str_ptr = unsafe { lua_setlocal(self.thread.as_ptr(), ar as *const _ as *const _, n) };
		if !str_ptr.is_null() {
			Some(unsafe { CStr::from_ptr(str_ptr) })
		} else {
			None
		}
	}
}
