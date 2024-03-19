//! Definitions for FFI.
//! 
//! This has the main API defined, although there *may be* re-exports:
//! - If the `auxlib` feature is enabled, then there will be definitions from
//! `lauxlib.h`.
//! - If the `stdlibs` feature is enabled, then there will be definitions from
//! `lualib.h`.

use core::ffi::c_char;
use core::ffi::c_int;
use core::ffi::c_void;

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

	pub use on_32_bits::Integer;
	pub use on_32_bits::Unsigned;
	pub use on_32_bits::Number;
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

/// Size limit for the Lua stack. This cannot be changed for Lua that's already
/// compiled.
/// 
/// This limit is arbitrary; its only purpose is to stop Lua from consuming
/// unlimited stack space (and to reserve some numbers for pseudo-indices).
pub use dependent::MAX_STACK;

/// Pseudo-index that points to a Lua global state's registry.
pub const REGISTRY_INDEX: c_int = -MAX_STACK - 1000;

/// Calculate a pseudo-index for the `i`-th upvalue, *starting from `1`*.
/// 
/// Even with the above, this constant function will never panic.
pub const fn upvalue_index(i: c_int) -> c_int {
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

		impl Into<c_int> for $name {
			fn into(self) -> c_int {
				self as c_int
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

c_int_enum! {
	/// Lua thread status.
	#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
	pub enum ThreadStatus {
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
	}
}

impl ThreadStatus {
	/// Return true if the status represents no error.
	/// 
	/// # Examples
	/// ```
	/// use lunka::ThreadStatus;
	/// assert!(ThreadStatus::Ok.is_ok());
	/// assert!(ThreadStatus::Yielded.is_ok());
	/// assert!(!ThreadStatus::MemoryError.is_ok());
	/// ```
	pub const fn is_ok(&self) -> bool {
		match self {
			Self::Ok => true,
			Self::Yielded => true,
			_ => false
		}
	}

	/// Return true if the status represents the fact that the thread yielded.
	/// 
	/// # Examples
	/// ```
	/// use lunka::ThreadStatus;
	/// assert!(ThreadStatus::Yielded.is_yield());
	/// assert!(!ThreadStatus::Ok.is_yield());
	/// ```
	pub const fn is_yield(&self) -> bool {
		match self {
			Self::Yielded => true,
			_ => false
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
/// 
/// TODO: Examples?
pub const REGISTRY_MAIN_THREAD: c_int = 1;

/// Index in a Lua global state's registry where the global environment is
/// stored.
/// 
/// TODO: Examples?
pub const REGISTRY_GLOBALS: c_int = 2;

/// Last occupied index in a Lua global state's registry.
pub const REGISTRY_LAST: c_int = REGISTRY_GLOBALS;

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
/// TODO: Examples.
pub type CFunction = unsafe extern "C" fn (l: *mut State) -> c_int;

/// Continuation function.
/// Also known as `lua_KFunction`.
/// 
/// TODO: Documentation of what the parameters and return value mean, examples.
pub type KFunction = unsafe extern "C" fn (
	l: *mut State, status: c_int, ctx: KContext
) -> c_int;

/// Function that reads blocks when loading Lua chunks.
/// Also known as `lua_Reader`.
/// 
/// TODO: Explanation of parameters, the return value lifetime, examples.
pub type Reader = unsafe extern "C" fn (
	l: *mut State, ud: *mut c_void, sz: *mut usize
) -> *const c_char;

/// Function that writes blocks when dumping Lua chunks.
/// Also known as `lua_Writer`.
/// 
/// TODO: Explanation of parameters, the return value lifetime, examples.
pub type Writer = unsafe extern "C" fn (
	l: *mut State, p: *const c_void, sz: usize, ud: *mut c_void
) -> *const c_char;

/// Memory allocation function.
/// Also known as `lua_Alloc`.
/// 
/// TODO: Explanation of parameters, the return value lifetime, examples.
pub type Alloc = unsafe extern "C" fn (
	ud: *mut c_void,
	ptr: *mut c_void, osize: usize,
	nsize: usize
) -> *mut c_void;

/// Warning handler function.
/// Also known as `lua_WarnFunction`.
/// 
/// TODO: Explanation of parameters and their lifetimes, examples.
pub type Warn = unsafe extern "C" fn (
	ud: *mut c_void, msg: *const c_char, tocont: c_int
);

// Lua API definitions.
extern "C" {
	pub fn lua_newstate(f: Alloc, ud: *mut c_void) -> *mut State;
	pub fn lua_close(l: *mut State);
}
