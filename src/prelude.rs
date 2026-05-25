//! Prelude that re-exports useful things, but prepends `Lua` or `lua_` to
//! them to prevent name clashes.

#[cfg(feature = "auxlib")]
pub use crate::{
	cdef::auxlib::luaL_Reg as LuaReg,
	AuxOptions as LuaAuxOptions,
	Library as LuaLibrary,
};

pub use crate::{
	cdef::{
		lua_Alloc as LuaAlloc,
		Arith as LuaArith,
		lua_CFunction as LuaCFunction,
		Compare as LuaCompare,
		lua_Debug as LuaDebug,
		Integer as LuaInteger,
		KContext as LuaKContext,
		lua_KFunction as LuaKFunction,
		Number as LuaNumber,
		lua_Reader as LuaReader,
		lua_State as LuaState,
		Status as LuaStatus,
		Type as LuaType,
		Unsigned as LuaUnsigned,
		lua_WarnFunction as LuaWarnFunction,
		lua_Writer as LuaWriter,
		DEFAULT_ID_SIZE as LUA_DEFAULT_ID_SIZE,
		lua_upvalueindex as lua_upvalue_index
	},
	dbg_what::DebugWhat as LuaDebugWhat,
	Lua,
	Coroutine as LuaCoroutine,
	Thread as LuaThread,
	fmt_error,
	function,
	library,
	push_fmt_string
};
