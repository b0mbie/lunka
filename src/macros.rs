/// Push a formatted string with [`lua_pushfstring`](crate::cdef::lua_pushfstring).
/// 
/// The "signature" for this function is
/// `lua_push_fmt_string!(lua: &Thread, fmt: <string>, ...)`, where `fmt` is a
/// literal format string, and `...` are the format arguments.
/// 
/// It is similar to the ISO C function `sprintf`, however you do not have to
/// allocate space for the result; the result is a Lua string and Lua takes care
/// of memory allocation (and deallocation, through garbage collection).
/// 
///	# Conversion specifiers
/// There are no flags, widths, or precisions.
/// The conversion specifiers can only be:
/// - `%%` - insert the character `%`.
/// - `%s` - insert a zero-terminated string using [`*const c_char`](core::ffi::c_char), with no size restrictions.
/// - `%f` - insert a [`Number`](crate::cdef::Number).
/// - `%I` - insert an [`Integer`](crate::cdef::Integer).
/// - `%p` - insert a *thin* pointer, like [`*mut c_void`](core::ffi::c_void).
/// - `%d` - insert a [`c_int`](core::ffi::c_int).
/// - `%c` - insert a [`c_int`](core::ffi::c_int) as a one-byte character.
/// - `%U` - insert a [`c_long`](core::ffi::c_long) as a UTF-8 byte sequence.
/// 
/// # Safety
/// The macro uses an unsafe function, and is itself unsafe to use; there have
/// to be sufficient format arguments, and they must be of the correct type.
#[macro_export]
macro_rules! lua_push_fmt_string {
	($lua:expr, $fmt:expr $(, $($fmt_arg:tt)*)?) => {{
		let lua: &$crate::Thread = &$lua;
		let fmt: &::core::ffi::CStr = $fmt;
		$crate::cdef::lua_pushfstring(lua.as_ptr(), fmt.as_ptr()$(, $($fmt_arg)*)?)
	}};
}

/// Raise a formatted error with [`luaL_error`](crate::cdef::auxlib::luaL_error).
/// 
/// The "signature" for this function is
/// `lua_fmt_error!(lua: &Thread, fmt: <string>, ...)`, where `fmt` is a
/// literal format string, and `...` are the format arguments.
/// 
/// This function follows the same rules as [`lua_push_fmt_string!`].
/// 
/// # Safety
/// The macro uses an unsafe function, and is itself unsafe to use; there have
/// to be sufficient format arguments, and they must be of the correct type.
#[macro_export]
macro_rules! lua_fmt_error {
	($lua:expr, $fmt:literal $(, $fmt_arg:expr)*) => {{
		let lua: &$crate::Thread = &$lua;
		$crate::cdef::auxlib::luaL_error(
			lua.as_ptr(),
			core::ffi::CStr::from_bytes_with_nul_unchecked(
				concat!($fmt, "\0").as_bytes()
			).as_ptr()
			$(, $fmt_arg)*
		)
	}};
}

/// Create a [`Library`](crate::reg::Library) with a more understandable syntax.
/// 
/// The macro accepts a `struct` construction-like syntax, to construct an
/// instance from a static array of pairs of [`CStr`](core::ffi::CStr) and
/// [`Option<CFunction>`](crate::cdef::CFunction), where a field with a value creates a pair
/// `("name", Some(func_name))`, and a field with no value specified creates a
/// pair `("name", None)`.
/// 
/// # Examples
/// ```
/// use lunka::prelude::*;
/// 
/// unsafe extern "C-unwind" fn l_get_pi(l: *mut LuaState) -> core::ffi::c_int {
/// 	let lua = LuaThread::from_ptr(l);
/// 	lua.push_number(3.14);
/// 	1
/// }
/// 
/// // This will create a `LuaLibrary` that, when used with `Thread::set_funcs`,
/// // will set a table's field `get_pi` to the `l_get_pi` function, and `set_pi`
/// // to `false`.
/// let library = lua_library! {
/// 	get_pi: l_get_pi,
/// 	set_pi
/// };
/// ```
#[cfg(feature = "auxlib")]
#[macro_export]
macro_rules! lua_library {
	{$(
		$field:ident $(: $fn:expr)?
	),*} => {
		$crate::Library::new([
			$(lua_library!(@field $field $($fn)?)),*
		])
	};

	(@field $field:ident $fn:expr) => {
		(unsafe { ::core::ffi::CStr::from_bytes_with_nul_unchecked(
			concat!(stringify!($field), "\0").as_bytes()
		) }, Some($fn))
	};

	(@field $field:ident) => {
		(unsafe { ::core::ffi::CStr::from_bytes_with_nul_unchecked(
			concat!(stringify!($field), "\0").as_bytes()
		) }, None)
	};
}

/// Create an unnamed function that conforms to the signature of [`CFunction`](crate::cdef::CFunction).
/// 
/// The macro accepts the pattern for the [`State`](crate::cdef::State) argument,
/// followed by `=>` and the function body.
/// The function is not a closure; it may not capture any variables.
/// 
/// # Examples
/// ```
/// use lunka::prelude::*;
/// 
/// #[unsafe(no_mangle)]
/// unsafe extern "C-unwind" fn luaopen_mylib(l: *mut LuaState) -> core::ffi::c_int {
/// 	let lua = unsafe { LuaThread::from_ptr(l) };
/// 	lua.new_lib(&lua_library! {
/// 		sqr: lua_function!(l => {
/// 			let lua = LuaThread::from_ptr(l);
/// 			let x = lua.check_number(1);
///				lua.push_number(x * x);
/// 			1
///			}),
/// 		do_nothing: lua_function!(_ => 0)
/// 	});
/// 	1
/// }
/// ```
#[macro_export]
macro_rules! lua_function {
	($l:pat => $body:expr) => {{
		unsafe extern "C-unwind" fn __lua_function_inner($l: *mut $crate::cdef::State) -> ::core::ffi::c_int {
			$body
		}
		__lua_function_inner
	}};
}
