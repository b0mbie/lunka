//! Definitions for FFI.
//! 
//! This has the main API defined, although there *may be* re-exports:
//! - If the `auxlib` feature is enabled, then there will be definitions from `lauxlib.h`.
//! - If the `stdlibs` feature is enabled, then there will be definitions from `lualib.h`.
//! 
//! # Safety
//! Functions that raise an error *will not run any Rust drop glue upon doing so*.
//! While it is possible to implement [`Result`] wrappers around those functions,
//! doing so has a performance cost.
//! Lua currently does not allow you to immediately catch API errors.
//! 
//! In unsafe code, if you are not sure whether Lua may raise an error:
//! - do not make any allocations that aren't garbage-collected in Lua (such as with `Box`), and
//! - do not use locks even with RAII guards, because they suffer from the same problem as non-Lua allocations.

use core::{
	ffi::{
		c_char, c_double, c_int, c_long, c_uchar, c_uint, c_ushort, c_void,
	},
	ptr::{
		null_mut, null,
	},
};

#[cfg(feature = "auxlib")]
pub mod auxlib;

#[cfg(feature = "stdlibs")]
pub mod stdlibs;

/// Lua version number.
pub const VERSION_NUM: Number = 504 as _;

/// Option for multiple returns in `lua_pcall` and `lua_call`.
pub const MULT_RET: c_int = -1;

mod dependent {
	#![allow(unused_imports)]

	use core::ffi::c_int;

	#[cfg(any(target_pointer_width = "32", target_pointer_width = "64"))]
	pub const MAX_STACK: c_int = 1000000;

	#[cfg(not(any(target_pointer_width = "32", target_pointer_width = "64")))]
	pub const MAX_STACK: c_int = 15000;

	#[cfg(feature = "use-32-bits")]
	mod on_32_bits {
		use core::ffi::{
			c_float,
			c_int,
			c_long,
			c_uint,
			c_ulong
		};

		// Use `c_int` if big enough.
		#[cfg(any(target_pointer_width = "32", target_pointer_width = "64"))]
		pub type Integer = c_int;

		#[cfg(any(target_pointer_width = "32", target_pointer_width = "64"))]
		pub type Unsigned = c_uint;

		// Otherwise, use `c_long`.
		#[cfg(not(any(target_pointer_width = "32", target_pointer_width = "64")))]
		pub type Integer = c_long;

		#[cfg(not(any(target_pointer_width = "32", target_pointer_width = "64")))]
		pub type Unsigned = c_ulong;

		pub type Number = c_float;
	}

	#[cfg(not(feature = "use-32-bits"))]
	mod on_32_bits {
		use core::ffi::{
			c_double,
			c_longlong,
			c_ulonglong
		};

		pub type Integer = c_longlong;
		pub type Unsigned = c_ulonglong;

		pub type Number = c_double;
	}

	pub use on_32_bits::{
		Integer,
		Unsigned,
		Number,
	};
}

/// Type of signed Lua integers.
/// Also known as `lua_Integer`.
/// 
/// The actual definition for this type depends on the `use-32-bits` feature.
/// If that feature is enabled, then
/// - if `c_int` is big enough, then this is `c_int`,
/// - otherwise, this is `c_long`.
/// 
/// If the feature is not enabled, then this is `c_longlong`.
pub use dependent::Integer;

/// Type of unsigned Lua integers.
/// Also known as `lua_Unsigned`.
/// 
/// This type, effectively, is just [`Integer`], though unsigned.
/// Refer to its documentation.
pub use dependent::Unsigned;

/// Type of Lua numbers.
/// Also known as `lua_Number`.
/// 
/// The actual definition for this type depends on the `use-32-bits` feature.
/// If that feature is enabled, then this is `c_float`. Otherwise, it's
/// `c_double`.
pub use dependent::Number;

/// Type of the context used for continuation functions.
/// Also known as `lua_KContext`.
/// 
/// The original Lua C header uses `ptrdiff_t` or `intptr_t`.
/// Those types are practically the same, even though the intention for using
/// them differs. The closest analogue to those is [`isize`].
pub type KContext = isize;

/// Size limit for the Lua stack.
/// This cannot be changed for Lua that's already compiled.
/// 
/// This limit is arbitrary; its only purpose is to stop Lua from consuming
/// unlimited stack space (and to reserve some numbers for pseudo-indices).
pub use dependent::MAX_STACK;

/// Pseudo-index that points to a Lua global state's registry.
pub const REGISTRY_INDEX: c_int = -MAX_STACK - 1000;

/// Calculate a pseudo-index for the `i`-th upvalue, *starting from `1`*.
/// 
/// Equivalent to the `lua_upvalueindex` C macro.
/// 
/// Even with the above, this constant function will never panic.
pub const fn lua_upvalueindex(i: c_int) -> c_int {
	REGISTRY_INDEX - i
}

macro_rules! c_int_enum {
	(
		$(#[$attr:meta])*
		$vis:vis enum $name:ident {
			$(
				$(#[$variant_attr:meta])*
				$variant:ident = $def:expr,
			)*
		}
	) => {
		$(#[$attr])*
		$vis enum $name {
			$(
				$(#[$variant_attr])*
				$variant = $def as c_int as _
			),*
		}

		impl $name {
			/// Construct an instance of this enum from a [`c_int`], but without
			/// checking if that value is valid.
			/// 
			/// # Safety
			/// It is undefined behavior to use a value that doesn't correspond
			/// to a valid variant.
			pub const unsafe fn from_c_int_unchecked(value: c_int) -> Self {
				match value {
					$($def => Self::$variant,)*
					_ => unsafe { ::core::hint::unreachable_unchecked() }
				}
			}
		}

		impl From<$name> for c_int {
			fn from(value: $name) -> c_int {
				value as c_int
			}
		}
		
		impl TryFrom<c_int> for $name {
			type Error = ();
			fn try_from(value: c_int) -> Result<Self, Self::Error> {
				match value {
					$(
						$def => Ok(Self::$variant),
					)*
					_ => Err(())
				}
			}
		}
	};
}
pub(crate) use c_int_enum;

c_int_enum! {
	/// Lua status code enumeration.
	/// 
	/// This status usually indicates a success or some sort of failure in the
	/// form of a caught raised error.
	/// Read more about errors in the [documentation](crate::errors).
	#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
	pub enum Status {
		/// No errors.
		/// Also known as `LUA_OK`.
		Ok = 0,
		/// Yielded.
		/// Also known as `LUA_YIELD`.
		Yielded = 1,
		/// Encountered a runtime error.
		/// Also known as `LUA_ERRRUN`.
		RuntimeError = 2,
		/// Encountered a syntax error.
		/// Also known as `LUA_ERRSYNTAX`.
		SyntaxError = 3,
		/// Encountered a memory-related error.
		/// Also known as `LUA_ERRMEM`.
		MemoryError = 4,
		/// Encountered some error while handling an error.
		/// Also known as `LUA_ERRERR`.
		HandlerError = 5,
		/// Encountered a file-related error.
		/// Also known as `LUA_ERRFILE`.
		/// 
		/// This is only present with the `auxlib` feature enabled, since this
		/// status code is only used there for
		/// [`luaL_loadfilex`](crate::cdef::auxlib::luaL_loadfilex).
		#[cfg(feature = "auxlib")]
		FileError = 6,
	}
}

impl Status {
	/// Return true if the status represents no error.
	/// 
	/// # Examples
	/// ```
	/// use lunka::cdef::Status;
	/// assert!(Status::Ok.is_ok());
	/// assert!(Status::Yielded.is_ok());
	/// assert!(!Status::MemoryError.is_ok());
	/// ```
	pub const fn is_ok(self) -> bool {
		matches!(self, Self::Ok | Self::Yielded)
	}

	/// Return true if the status represents the fact that the thread yielded.
	/// 
	/// # Examples
	/// ```
	/// use lunka::cdef::Status;
	/// assert!(Status::Yielded.is_yield());
	/// assert!(!Status::Ok.is_yield());
	/// ```
	pub const fn is_yield(self) -> bool {
		matches!(self, Self::Yielded)
	}

	pub fn then<T>(self, func: impl FnOnce(Self) -> T) -> Option<T> {
		match self {
			Self::Ok => Some(func(self)),
			Self::Yielded => Some(func(self)),
			_ => None
		}
	}

	pub fn then_some<T>(self, value: T) -> Option<T> {
		match self {
			Self::Ok => Some(value),
			Self::Yielded => Some(value),
			_ => None
		}
	}

	pub fn or_else<E>(self, func: impl FnOnce(Self) -> E) -> Result<(), E> {
		match self {
			Self::Ok => Ok(()),
			Self::Yielded => Ok(()),
			_ => Err(func(self))
		}
	}

	pub fn or<E>(self, err: E) -> Result<(), E> {
		match self {
			Self::Ok => Ok(()),
			Self::Yielded => Ok(()),
			_ => Err(err)
		}
	}
}

c_int_enum! {
	/// Lua basic type enumeration.
	#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
	pub enum Type {
		/// "Pseudo-type" that indicates that there's *nothing* somewhere.
		None = -1,
		/// `nil`.
		Nil = 0,
		/// Boolean - `true` and `false`.
		Boolean = 1,
		/// Light userdata - plain pointer.
		LightUserdata = 2,
		/// Number, which can also mean "integer".
		Number = 3,
		/// Garbage-collected string.
		String = 4,
		/// Table.
		Table = 5,
		/// Function, which can mean a Lua function or a C function.
		Function = 6,
		/// Full userdata - garbage-collected pointer.
		Userdata = 7,
		/// Thread - a Lua state, or coroutine.
		Thread = 8,
		/// Lua type count.
		Count = 9,
	}
}

/// Index in a Lua global state's registry where the main thread is stored.
pub const REGISTRY_MAIN_THREAD: Integer = 1;

/// Index in a Lua global state's registry where the global environment is
/// stored.
pub const REGISTRY_GLOBALS: Integer = 2;

/// Last occupied index in a Lua global state's registry.
pub const REGISTRY_LAST: Integer = REGISTRY_GLOBALS;

/// Opaque type that represents a Lua state.
/// Also known as `lua_State`.
/// 
/// This type is *always* used behind a pointer, and does not store any
/// information - it's always a ZST.
#[repr(C)]
#[derive(Debug)]
pub struct State {
	_data: [u8; 0],
	_marker: core::marker::PhantomData<(*mut u8, core::marker::PhantomPinned)>
}

/// C function registered with Lua.
/// Also known as `lua_CFunction`.
/// 
/// This is still called a *C function*, because Rust has to speak the language
/// of C to be able to use this.
/// 
/// C functions accept a pointer to a Lua state that they can manipulate.
/// If a C function pushes some values onto the Lua stack that it wishes to
/// return, then it must return the number of values it wants to return.
/// 
/// # Safety
/// When a C function is called from Lua, `l` always points to a valid Lua state.
/// However, **it is not guaranteed that the garbage collector is off**.
/// 
/// If code requires that the garbage collector is off (i.e. if pointers from
/// Lua are used after a call to
/// [`Thread::run_managed_no_gc`](crate::Thread::run_managed_no_gc)), then
/// garbage collection must be manually stopped.
pub type CFunction = unsafe extern "C-unwind" fn(l: *mut State) -> c_int;

/// Continuation function.
/// Also known as `lua_KFunction`.
/// 
/// # Safety
/// When a continuation is called from Lua, `l` always points to a valid Lua
/// state, and `ctx` is always the continuation context that was passed along
/// with the continuation function.
/// 
/// `status` is generally also a valid [`Status`].
pub type KFunction = unsafe extern "C-unwind" fn (
	l: *mut State, status: c_int, ctx: KContext
) -> c_int;

/// Function that reads blocks when loading Lua chunks.
/// Also known as `lua_Reader`.
/// 
/// # Safety
/// When a reader function is used by Lua, `l` always points to a valid Lua
/// state, `ud` is always the user-defined data that was passed along with the
/// reader function, and `sz` is always a pointer to [`usize`] that's valid for
/// writes.
/// 
/// The returned value must be a valid pointer to a string, or a null pointer if
/// no data is available. The pointer must be valid for reading at least until
/// the next usage of the function.
pub type Reader = unsafe extern "C-unwind" fn (
	l: *mut State, ud: *mut c_void, sz: *mut usize
) -> *const c_char;

/// Function that writes blocks when dumping Lua chunks.
/// Also known as `lua_Writer`.
/// 
/// # Safety
/// When a writer function is used by Lua, `l` always points to a valid Lua
/// state, `ud` is always the user-defined data that was passed along with the
/// reader function, and `p` is always a pointer that's valid for reading that
/// points to a memory block of size `sz` bytes.
pub type Writer = unsafe extern "C-unwind" fn (
	l: *mut State, p: *const c_void, sz: usize, ud: *mut c_void
) -> c_int;

/// Memory allocation function.
/// Also known as `lua_Alloc`.
pub type Alloc = unsafe extern "C-unwind" fn (
	ud: *mut c_void,
	ptr: *mut c_void, osize: usize,
	nsize: usize
) -> *mut c_void;

/// Function called by Lua to emit warnings.
/// Also known as `lua_WarnFunction`.
/// 
/// `tocont` is a boolean that indicates
/// whether the message is to be continued with the string passed in the next call.
/// 
/// # Safety
/// `ud` must be the userdata passed at the point of setting the warning function, and
/// `msg` must point to a valid C string.
pub type WarnFunction = unsafe extern "C-unwind" fn (
	ud: *mut c_void, msg: *const c_char, tocont: c_int
);

/// Default maximum size for the description of the source of a function in a
/// [`struct@Debug`].
/// 
/// Also known as `LUA_IDSIZE`.
/// 
/// This cannot be changed for Lua that's already compiled.
pub const DEFAULT_ID_SIZE: usize = 60;

/// Structure used to carry different pieces of information about a function or
/// an activation record.
/// 
/// Also known as `lua_Debug`.
/// 
/// This structure is used in Lua debug hooks, and has some private data.
/// The size of this structure in C code depends on the `LUA_IDSIZE` macro,
/// however that can always be changed, so a generic const is used here instead.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
#[repr(C)]
pub struct Debug<const ID_SIZE: usize = DEFAULT_ID_SIZE> {
	pub event: c_int,
	pub name: *const c_char,
	pub name_what: *const c_char,
	pub what: *const c_char,
	pub source: *const c_char, pub source_len: usize,
	pub current_line: c_int,
	pub line_defined: c_int, pub last_line_defined: c_int,
	pub n_upvalues: c_uchar,
	pub n_params: c_uchar,
	pub is_vararg: c_char,
	pub is_tail_call: c_char,
	pub first_transferred: c_ushort,
	pub n_transferred: c_ushort,
	pub short_src: [c_char; ID_SIZE],
	// This is used internally.
	pub active_function: *const c_void,
}

impl<const ID_SIZE: usize> Debug<ID_SIZE> {
	pub const fn zeroed() -> Self {
		Self {
			event: 0,
			name: null(),
			name_what: null(),
			what: null(),
			source: null(), source_len: 0,
			current_line: -1,
			line_defined: -1, last_line_defined: -1,
			n_upvalues: 0,
			n_params: 0,
			is_vararg: 0,
			is_tail_call: 0,
			first_transferred: 0,
			n_transferred: 0,
			short_src: [0; ID_SIZE],
			active_function: null()
		}
	}
}

/// Function to be called by the Lua debugger in specific events.
/// Also known as `lua_Hook`.
/// 
/// The exact signature of this function depends on the size of
/// `activation_record` behind a pointer - see [`struct@Debug`].
pub type Hook<const ID_SIZE: usize = DEFAULT_ID_SIZE> = unsafe extern "C-unwind" fn (
	l: *mut State, activation_record: *mut Debug<ID_SIZE>
);

/// Default size of a raw memory area associated with a Lua state with very fast
/// access.
/// 
/// Also known as `LUA_EXTRASPACE`.
/// 
/// This cannot be changed for Lua that's already compiled.
pub const DEFAULT_EXTRA_SPACE: usize = core::mem::size_of::<*mut c_void>();

c_int_enum! {
	/// Operation types for [`lua_arith`].
	#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
	pub enum Arith {
		Add = 0,
		Sub = 1,
		Mul = 2,
		Mod = 3,
		Pow = 4,
		Div = 5,
		IntDiv = 6,
		BitAnd = 7,
		BitOr = 8,
		BitXor = 9,
		ShiftLeft = 10,
		ShiftRight = 11,
		UnaryMinus = 12,
		BitNot = 13,
	}
}

c_int_enum! {
	/// Operation types for [`lua_compare`].
	#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
	pub enum Compare {
		Equal = 0,
		LessThan = 1,
		LessOrEqual = 2,
	}
}

c_int_enum! {
	/// Tasks for [`lua_gc`].
	/// 
	/// This enum does not include the arguments associated with a GC task.
	/// See the manual for more information on the arguments:
	/// <https://www.lua.org/manual/5.4/manual.html#lua_gc>
	#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
	pub enum GcTask {
		Stop = 0,
		Restart = 1,
		Collect = 2,
		CountKbytes = 3,
		CountBytesRem = 4,
		Step = 5,
		IsRunning = 6,
		ToIncremental = 7,
		ToGenerational = 8,
	}
}

macro_rules! lua_state_func {
	(
		$(
			$(#[$attr:meta])*
			$vis:vis fn $name:ident(self $($param:tt)*) $( -> $ret:ty )?;
		)*
	) => {
		$(
			$(#[$attr])*
			$vis fn $name(l: *mut $crate::cdef::State $($param)*) $( -> $ret )?;
		)*
	};
}
pub(crate) use lua_state_func;

#[cfg_attr(all(feature = "link-system", feature = "link-dynamic", target_os = "windows"), link(name = "lua54", kind = "raw-dylib"))]
#[cfg_attr(all(feature = "link-system", feature = "link-dynamic", not(target_os = "windows")), link(name = "lua5.4", kind = "dylib"))]
#[cfg_attr(all(feature = "link-system", not(feature = "link-dynamic"), target_os = "windows"), link(name = "lua54", kind = "static"))]
#[cfg_attr(all(feature = "link-system", not(feature = "link-dynamic"), not(target_os = "windows")), link(name = "lua5.4", kind = "static"))]
unsafe extern "C-unwind" {
	pub fn lua_newstate(f: Alloc, ud: *mut c_void) -> *mut State;
	pub fn lua_close(l: *mut State);

	pub fn lua_xmove(from: *mut State, to: *mut State, n: c_int);

	lua_state_func! {
		pub fn lua_newthread(self) -> *mut State;
		pub fn lua_closethread(self, from: *mut State) -> c_int;
		/// # Deprecated in Lua 5.4.6
		/// Since Lua 5.4.6, this function is deprecated and [`lua_closethread`]
		/// should be used instead.
		pub fn lua_resetthread(self) -> c_int;

		pub fn lua_atpanic(
			self, panicf: Option<CFunction>
		) -> Option<CFunction>;

		pub fn lua_version(self) -> Number;
	
		pub fn lua_absindex(self, idx: c_int) -> c_int;
		pub fn lua_gettop(self) -> c_int;
		pub fn lua_settop(self, idx: c_int);
		pub fn lua_pushvalue(self, idx: c_int);
		pub fn lua_rotate(self, idx: c_int, n: c_int);
		pub fn lua_copy(self, from_idx: c_int, to_idx: c_int);
		pub fn lua_checkstack(self, n: c_int) -> c_int;

		pub fn lua_isnumber(self, idx: c_int) -> c_int;
		pub fn lua_isstring(self, idx: c_int) -> c_int;
		pub fn lua_iscfunction(self, idx: c_int) -> c_int;
		pub fn lua_isinteger(self, idx: c_int) -> c_int;
		pub fn lua_isuserdata(self, idx: c_int) -> c_int;
		pub fn lua_type(self, idx: c_int) -> c_int;
		pub fn lua_typename(self, type_tag: c_int) -> *const c_char;

		pub fn lua_tonumberx(self, idx: c_int, is_num: *mut c_int) -> Number;
		pub fn lua_tointegerx(self, idx: c_int, is_num: *mut c_int) -> Integer;
		pub fn lua_toboolean(self, idx: c_int) -> c_int;
		pub fn lua_tolstring(
			self, idx: c_int, len: *mut usize
		) -> *const c_char;
		pub fn lua_rawlen(self, idx: c_int) -> Unsigned;
		pub fn lua_tocfunction(self, idx: c_int) -> Option<CFunction>;
		pub fn lua_touserdata(self, idx: c_int) -> *mut c_void;
		pub fn lua_tothread(self, idx: c_int) -> *mut State;
		pub fn lua_topointer(self, idx: c_int) -> *const c_void;

		pub fn lua_arith(self, op: c_int);
		pub fn lua_rawequal(self, idx_a: c_int, idx_b: c_int) -> c_int;
		pub fn lua_compare(
			self,
			idx_a: c_int, idx_b: c_int,
			op: c_int
		) -> c_int;

		pub fn lua_pushnil(self);
		pub fn lua_pushnumber(self, n: Number);
		pub fn lua_pushinteger(self, n: Integer);
		pub fn lua_pushlstring(
			self, s: *const c_char, len: usize
		) -> *const c_char;
		pub fn lua_pushstring(self, s: *const c_char) -> *const c_char;
		// Can't create `VaList`s...
		pub fn lua_pushvfstring(
			self, fmt: *const c_char, argp: *mut c_void
		) -> *const c_char;
		pub fn lua_pushfstring(
			self, fmt: *const c_char, ...
		) -> *const c_char;
		pub fn lua_pushcclosure(self, func: CFunction, n: c_int);
		pub fn lua_pushboolean(self, b: c_int);
		pub fn lua_pushlightuserdata(self, p: *mut c_void);
		pub fn lua_pushthread(self) -> c_int;

		pub fn lua_getglobal(self, name: *const c_char) -> c_int;
		pub fn lua_gettable(self, idx: c_int) -> c_int;
		pub fn lua_getfield(self, idx: c_int, k: *const c_char) -> c_int;
		pub fn lua_geti(self, idx: c_int, i: Integer) -> c_int;
		pub fn lua_rawget(self, idx: c_int) -> c_int;
		pub fn lua_rawgeti(self, idx: c_int, n: Integer) -> c_int;
		pub fn lua_rawgetp(self, idx: c_int, p: *const c_void) -> c_int;

		pub fn lua_createtable(self, n_arr: c_int, n_rec: c_int);
		pub fn lua_newuserdatauv(
			self, sz: usize, n_uvalue: c_int
		) -> *mut c_void;
		pub fn lua_getmetatable(self, obj_index: c_int) -> c_int;
		pub fn lua_getiuservalue(self, idx: c_int, n: c_int) -> c_int;

		pub fn lua_setglobal(self, name: *const c_char);
		pub fn lua_settable(self, idx: c_int);
		pub fn lua_setfield(self, idx: c_int, k: *const c_char);
		pub fn lua_seti(self, idx: c_int, n: Integer);
		pub fn lua_rawset(self, idx: c_int);
		pub fn lua_rawseti(self, idx: c_int, n: Integer);
		pub fn lua_rawsetp(self, idx: c_int, p: *const c_void);
		pub fn lua_setmetatable(self, obj_index: c_int) -> c_int;
		pub fn lua_setiuservalue(self, idx: c_int, n: c_int) -> c_int;

		pub fn lua_callk(
			self,
			n_args: c_int, n_results: c_int,
			ctx: KContext, k: Option<KFunction>
		);
		pub fn lua_pcallk(
			self,
			n_args: c_int, n_results: c_int,
			err_func: c_int,
			ctx: KContext, k: Option<KFunction>
		) -> c_int;
		pub fn lua_load(
			self,
			reader: Reader, dt: *mut c_void,
			chunk_name: *const c_char,
			mode: *const c_char
		) -> c_int;
		pub fn lua_dump(
			self,
			writer: Writer, data: *mut c_void,
			strip: c_int
		) -> c_int;

		/// # Note
		/// The documentation states that this function *returns in hooks*.
		/// This signature assumes calls outside of hooks, where they **will not**
		/// return.
		/// 
		/// Use [`lua_yieldk_in_hook`] if you are *absolutely sure* that this
		/// function will return.
		/// 
		/// See the manual for more information:
		/// <https://www.lua.org/manual/5.4/manual.html#lua_yieldk>
		pub fn lua_yieldk(
			self,
			n_results: c_int,
			ctx: KContext, k: Option<KFunction>
		) -> !;

		/// # Note
		/// This function is linked to the same symbol as [`lua_yieldk`],
		/// however, it should only be called in hooks, since the signature
		/// says that this function **will** return.
		/// 
		/// Use [`lua_yieldk`] if you are *absolutely sure* that this function
		/// will never return.
		/// 
		/// See the manual for more information:
		/// <https://www.lua.org/manual/5.4/manual.html#lua_yieldk>
		#[allow(clashing_extern_declarations)]
		#[link_name = "lua_yieldk"]
		pub fn lua_yieldk_in_hook(
			self,
			n_results: c_int,
			ctx: KContext, k: Option<KFunction>
		) -> c_int;

		pub fn lua_resume(
			self, from: *mut State,
			n_arg: c_int,
			n_res: *mut c_int
		) -> c_int;
		pub fn lua_status(self) -> c_int;
		pub fn lua_isyieldable(self) -> c_int;

		pub fn lua_setwarnf(self, f: Option<WarnFunction>, ud: *mut c_void);
		pub fn lua_warning(self, msg: *const c_char, to_cont: c_int);

		pub fn lua_gc(self, what: c_int, ...) -> c_int;

		/// # Note
		/// The return type should be [`c_int`] judging from the C header,
		/// however the documentation states that this function *never* returns.
		/// 
		/// See the manual for more information:
		/// <https://www.lua.org/manual/5.4/manual.html#lua_error>
		pub fn lua_error(self) -> !;

		pub fn lua_next(self, idx: c_int) -> c_int;

		pub fn lua_concat(self, n: c_int);
		pub fn lua_len(self, idx: c_int);
	
		pub fn lua_stringtonumber(self, s: *const c_char) -> usize;

		pub fn lua_getallocf(self, ud: *mut *mut c_void) -> Alloc;
		pub fn lua_setallocf(self, f: Alloc, ud: *mut c_void);

		pub fn lua_toclose(self, idx: c_int);
		pub fn lua_closeslot(self, idx: c_int);

		pub fn lua_getupvalue(
			self, func_index: c_int, n: c_int
		) -> *const c_char;
		pub fn lua_setupvalue(
			self, func_index: c_int, n: c_int
		) -> *const c_char;

		pub fn lua_upvalueid(
			self, func_index: c_int, n: c_int
		) -> *mut c_void;
		pub fn lua_upvaluejoin(
			self,
			func_into_index: c_int, n_into: c_int,
			func_from_index: c_int, n_from: c_int
		);

		pub fn lua_gethookmask(self) -> c_int;
		pub fn lua_gethookcount(self) -> c_int;
	
		pub fn lua_setcstacklimit(self, limit: c_uint) -> c_int;

		pub fn lua_getstack(self, level: c_int, ar: *mut Debug<DEFAULT_ID_SIZE>) -> c_int;
		pub fn lua_getinfo(self, what: *const c_char, ar: *mut Debug<DEFAULT_ID_SIZE>) -> c_int;
		pub fn lua_getlocal(self, ar: *const Debug<DEFAULT_ID_SIZE>, n: c_int) -> *const c_char;
		pub fn lua_setlocal(self, ar: *const Debug<DEFAULT_ID_SIZE>, n: c_int) -> *const c_char;
		pub fn lua_sethook(self, func: Hook<DEFAULT_ID_SIZE>, mask: c_int, count: c_int);
		pub fn lua_gethook(self) -> Hook<DEFAULT_ID_SIZE>;
	}
}

/// Equivalent to the `lua_call` C macro.
/// 
/// # Safety
/// `l` must be a valid pointer to a Lua state.
pub unsafe fn lua_call(l: *mut State, n_args: c_int, n_results: c_int) {
	unsafe { lua_callk(l, n_args, n_results, 0, None) }
}

/// Equivalent to the `lua_pcall` C macro.
/// 
/// # Safety
/// `l` must be a valid pointer to a Lua state.
pub unsafe fn lua_pcall(
	l: *mut State,
	n_args: c_int, n_results: c_int,
	err_func: c_int
) -> c_int {
	unsafe { lua_pcallk(l, n_args, n_results, err_func, 0, None) }
}

/// *Almost* equivalent to the `lua_yield` C macro, however this function
/// specifically uses [`lua_yieldk`].
/// 
/// # Safety
/// `l` must be a valid pointer to a Lua state.
pub unsafe fn lua_yield(l: *mut State, n_results: c_int) -> ! {
	unsafe { lua_yieldk(l, n_results, 0, None) }
}

/// *Almost* equivalent to the `lua_yield` C macro, however this function
/// specifically uses [`lua_yieldk_in_hook`].
/// 
/// # Safety
/// `l` must be a valid pointer to a Lua state.
pub unsafe fn lua_yield_in_hook(l: *mut State, n_results: c_int) -> c_int {
	unsafe { lua_yieldk_in_hook(l, n_results, 0, None) }
}

/// Get a pointer to the extra space of a Lua state.
/// 
/// This is practically equivalent to the `lua_getextraspace` C macro.
/// 
/// The amount of extra space is defined in `LUA_EXTRASPACE` in the C header,
/// however, it can always be changed.
/// This is what the `extra_space` parameter is for.
/// 
/// # Safety
/// `l` must be a valid pointer to a Lua state,
/// and `extra_space` must be valid for it.
/// The returned pointer will point to completely arbitrary data that can change at any point.
pub const unsafe fn lua_getextraspace(l: *mut State, extra_space: usize) -> *mut c_void {
	unsafe { l.byte_sub(extra_space) as *mut c_void }
}

/// Equivalent to the `lua_tonumber` C macro.
/// 
/// # Safety
/// `l` must be a valid pointer to a Lua state.
pub unsafe fn lua_tonumber(l: *mut State, idx: c_int) -> Number {
	unsafe { lua_tonumberx(l, idx, null_mut()) }
}

/// Equivalent to the `lua_tointeger` C macro.
/// 
/// # Safety
/// `l` must be a valid pointer to a Lua state.
pub unsafe fn lua_tointeger(l: *mut State, idx: c_int) -> Integer {
	unsafe { lua_tointegerx(l, idx, null_mut()) }
}

/// Equivalent to the `lua_pop` C macro.
/// 
/// # Safety
/// `l` must be a valid pointer to a Lua state.
pub unsafe fn lua_pop(l: *mut State, n: c_int) {
	unsafe { lua_settop(l, -n - 1) }
}

/// Equivalent to the `lua_newtable` C macro.
/// 
/// # Safety
/// `l` must be a valid pointer to a Lua state.
pub unsafe fn lua_newtable(l: *mut State) {
	unsafe { lua_createtable(l, 0, 0) }
}

/// Equivalent to the `lua_pushcfunction` C macro.
/// 
/// # Safety
/// `l` must be a valid pointer to a Lua state.
pub unsafe fn lua_pushcfunction(l: *mut State, func: CFunction) {
	unsafe { lua_pushcclosure(l, func, 0) }
}

/// Equivalent to the `lua_register` C macro.
/// 
/// # Safety
/// `l` must be a valid pointer to a Lua state,
/// and `name` must be a valid C string.
pub unsafe fn lua_register(l: *mut State, name: *const c_char, func: CFunction) {
	unsafe {
		lua_pushcfunction(l, func);
		lua_setglobal(l, name)
	}
}

macro_rules! lua_is {
	(
		$(
			$vis:vis fn $name:ident for $type:expr;
		)*
	) => {
		$(
			/// Equivalent to the C macro of the same name.
			/// 
			/// # Safety
			/// `l` must be a valid pointer to a Lua state.
			$vis unsafe fn $name(l: *mut State, idx: c_int) -> bool {
				(unsafe { lua_type(l, idx) }) == ($type as _)
			}
		)*
	};
}

lua_is! {
	pub fn lua_isfunction for Type::Function;
	pub fn lua_istable for Type::Table;
	pub fn lua_islightuserdata for Type::LightUserdata;
	pub fn lua_isnil for Type::Nil;
	pub fn lua_isboolean for Type::Boolean;
	pub fn lua_isthread for Type::Thread;
	pub fn lua_isnone for Type::None;
}

/// Equivalent to the `lua_isnoneornil` C macro.
/// 
/// # Safety
/// `l` must be a valid pointer to a Lua state.
pub unsafe fn lua_isnoneornil(l: *mut State, idx: c_int) -> bool {
	unsafe { lua_type(l, idx) <= 0 }
}

// `lua_pushliteral` omitted here because it is *only* ever useful as a macro,
// and there are currently no optimizations in Lua to warrant it being here.
// If only...

/// Equivalent to the `lua_pushglobaltable` C macro.
/// 
/// # Safety
/// `l` must be a valid pointer to a Lua state.
pub unsafe fn lua_pushglobaltable(l: *mut State) {
	unsafe { lua_rawgeti(l, REGISTRY_INDEX, REGISTRY_GLOBALS) };
}

/// Equivalent to the `lua_tostring` C macro.
/// 
/// # Safety
/// `l` must be a valid pointer to a Lua state.
pub unsafe fn lua_tostring(l: *mut State, idx: c_int) -> *const c_char {
	unsafe { lua_tolstring(l, idx, null_mut()) }
}

/// Equivalent to the `lua_insert` C macro.
/// 
/// # Safety
/// `l` must be a valid pointer to a Lua state.
pub unsafe fn lua_insert(l: *mut State, idx: c_int) {
	unsafe { lua_rotate(l, idx, 1) }
}

/// Equivalent to the `lua_remove` C macro.
/// 
/// # Safety
/// `l` must be a valid pointer to a Lua state.
pub unsafe fn lua_remove(l: *mut State, idx: c_int) {
	unsafe {
		lua_rotate(l, idx, -1);
		lua_pop(l, 1)
	}
}

/// Equivalent to the `lua_replace` C macro.
/// 
/// # Safety
/// `l` must be a valid pointer to a Lua state.
pub unsafe fn lua_replace(l: *mut State, idx: c_int) {
	unsafe {
		lua_copy(l, -1, idx);
		lua_pop(l, 1)
	}
}

c_int_enum! {
	/// Lua event code enumeration.
	/// 
	/// This is used in Lua debug hooks.
	#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
	pub enum Event {
		Call = 0,
		Return = 1,
		Line = 2,
		Count = 3,
		TailCall = 4,
	}
}

/// Structure representing a Lua event mask.
/// 
/// This is used in Lua debug hooks.
#[derive(Default, Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
#[repr(transparent)]
pub struct HookMask {
	mask: c_int
}

impl HookMask {
	pub const INT_CALL: c_int = 1 << Event::Call as c_int;
	pub const INT_RETURN: c_int = 1 << Event::Return as c_int;
	pub const INT_LINE: c_int = 1 << Event::Line as c_int;
	pub const INT_COUNT: c_int = 1 << Event::Count as c_int;

	/// Construct a [`HookMask`] with no events that are listened for.
	/// 
	/// # Examples
	/// ```
	/// use lunka::cdef::HookMask;
	/// assert_eq!(HookMask::empty().into_c_int(), 0);
	/// ```
	pub const fn empty() -> Self {
		Self {
			mask: 0
		}
	}

	/// Create an instance of this structure using an already-known integer mask.
	/// 
	/// # Safety
	/// The mask must be valid for [`lua_sethook`].
	/// 
	/// # Examples
	/// ```
	/// use lunka::cdef::HookMask;
	/// unsafe {
	/// 	assert_eq!(HookMask::from_c_int_unchecked(0), HookMask::empty());
	/// }
	/// ```
	pub const unsafe fn from_c_int_unchecked(mask: c_int) -> Self {
		Self {
			mask
		}
	}

	/// Create an instance of this structure using an already-known integer mask,
	/// and process the mask to only have bits that are valid.
	pub const fn from_c_int(mask: c_int) -> Self {
		Self {
			mask: mask & (
				Self::INT_CALL | Self::INT_RETURN |
				Self::INT_LINE | Self::INT_COUNT
			)
		}
	}

	/// Consume this structure and return its underlying mask integer.
	/// 
	/// # Examples
	/// ```
	/// use lunka::cdef::HookMask;
	/// assert_eq!(HookMask::empty().into_c_int(), 0);
	/// ```
	pub const fn into_c_int(self) -> c_int {
		self.mask
	}

	/// Consume this structure, including in it a flag for function calls.
	/// 
	/// # Examples
	/// ```
	/// use lunka::cdef::HookMask;
	/// assert_eq!(
	/// 	HookMask::empty().with_calls().into_c_int(),
	/// 	HookMask::INT_CALL
	/// );
	/// ```
	pub const fn with_calls(self) -> Self {
		Self {
			mask: self.mask | Self::INT_CALL
		}
	}

	/// Consume this structure, including in it a flag for function returns.
	/// 
	/// # Examples
	/// ```
	/// use lunka::cdef::HookMask;
	/// assert_eq!(
	/// 	HookMask::empty().with_returns().into_c_int(),
	/// 	HookMask::INT_RETURN
	/// );
	/// ```
	pub const fn with_returns(self) -> Self {
		Self {
			mask: self.mask | Self::INT_RETURN
		}
	}

	/// Consume this structure, including in it a flag for advancing lines.
	/// 
	/// # Examples
	/// ```
	/// use lunka::cdef::HookMask;
	/// assert_eq!(
	/// 	HookMask::empty().with_lines().into_c_int(),
	/// 	HookMask::INT_LINE
	/// );
	/// ```
	pub const fn with_lines(self) -> Self {
		Self {
			mask: self.mask | Self::INT_LINE
		}
	}

	/// Consume this structure, including in it a flag for advancing
	/// instructions.
	/// 
	/// # Examples
	/// ```
	/// use lunka::cdef::HookMask;
	/// assert_eq!(
	/// 	HookMask::empty().with_instructions().into_c_int(),
	/// 	HookMask::INT_COUNT
	/// );
	/// ```
	/// instructions.
	pub const fn with_instructions(self) -> Self {
		Self {
			mask: self.mask | Self::INT_COUNT
		}
	}
}

/// Type that ensures maximum alignment for all of its fields.
/// Referenced with `LUAI_MAXALIGN`.
#[repr(C)]
pub union MaxAlign {
	pub n: Number,
	pub u: c_double,
	pub s: *mut c_void,
	pub i: Integer,
	pub l: c_long,
}
