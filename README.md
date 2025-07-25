# lunka
Pretty thin bindings to Lua 5.4.

This crate is still a *work-in-progress*.

Please check the latest documentation here:
[Documentation on `docs.rs`](https://docs.rs/lunka/).

# Examples
Creating a Lua "C" library:
```rust
use core::ffi::c_int;
use lunka::prelude::*;

unsafe extern "C-unwind" fn l_hello(l: *mut LuaState) -> c_int {
	// SAFETY: Caller ensures `l` is valid.
	let lua = unsafe { LuaThread::from_ptr(l) };

	// SAFETY: An error being raised will not skip any important pieces of code.
	let n = unsafe { lua.check_number(1) };

	// SAFETY: Ditto.
	unsafe { lua.push_string("Hello, world!") };
	lua.push_number(n * core::f64::consts::PI as LuaNumber);

	2
}

const LIBRARY: LuaLibrary<1> = lua_library! {
	hello: l_hello
};

#[unsafe(no_mangle)]
unsafe extern "C-unwind" fn luaopen_hello(l: *mut LuaState) -> c_int {
	// SAFETY: Caller ensures `l` is valid.
	let lua = unsafe { LuaThread::from_ptr(l) };

	// SAFETY: An error being raised will not skip any important pieces of code.
	unsafe { lua.new_lib(&LIBRARY) };

	1
}
```

For some more examples, check the `examples` directory in the crate's repository.
They are comprehensive enough for actual usage.
