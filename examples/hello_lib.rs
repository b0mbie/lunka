use lunka::prelude::*;

lua_export_fn!(luaopen_hello => |lua| {
	lua.new_lib(&LIBRARY);
	1
});

const LIBRARY: LuaLibrary = lua_library! {
	hello: l_hello,
};

extern "C-unwind" fn l_hello(mut lua: LuaCtx<'_>) -> LuaRets {
	let n = lua.check_number(1);

	lua.push_string("Hello, world!");
	lua.push_number(n * core::f64::consts::PI as LuaNumber);

	LuaRets::new(2)
}
