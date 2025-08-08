//! Prelude that re-exports useful things, but prepends `Lua` or `lua_` to
//! them to prevent name clashes.

#[cfg(feature = "auxlib")]
pub use crate::{
	cdef::auxlib::Reg as LuaReg,
	aux_options::AuxOptions as LuaAuxOptions,
	reg::Library as LuaLibrary
};

pub use crate::{
	cdef::{
		Alloc as LuaAlloc,
		Arith as LuaArith,
		CFunction as LuaCFunction,
		Compare as LuaCompare,
		Debug as LuaDebug,
		Integer as LuaInteger,
		KContext as LuaKContext,
		KFunction as LuaKFunction,
		Number as LuaNumber,
		Reader as LuaReader,
		State as LuaState,
		Status as LuaStatus,
		Type as LuaType,
		Unsigned as LuaUnsigned,
		WarnFunction as LuaWarnFunction,
		Writer as LuaWriter,
		DEFAULT_ID_SIZE as LUA_DEFAULT_ID_SIZE,
		lua_upvalueindex as lua_upvalue_index
	},
	dbg_what::DebugWhat as LuaDebugWhat,
	Lua,
	Coroutine as LuaCoroutine,
	Thread as LuaThread,
	lua_fmt_error,
	lua_function,
	lua_library,
	lua_push_fmt_string
};
