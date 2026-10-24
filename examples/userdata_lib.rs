use lunka::prelude::*;

lua_export_fn!(luaopen_userdata_lib => move |lua| {
	lua.register_udata::<StringBuffer>();
	lua.new_lib(&LIBRARY);
	1
});

const LIBRARY: LuaLibrary = lua_library! {
	buffer: lua_func!(lua => {
		lua.push_udata(StringBuffer::default());
		1
	}),
};

#[derive(Default)]
struct StringBuffer {
	pub bytes: Vec<u8>,
}
lua_impl_userdata!(StringBuffer);
impl LuaUserData for StringBuffer {
	fn init_metatable(lua: &mut LuaThread) {
		const INDEX: LuaLibrary = lua_library! {
			tostring: lua_method!(StringBuffer => mut lua => {
				let this = unsafe { lua.check_self_ptr().as_ref() };
				lua.push_string(&this.bytes);
				1
			}),
			pushbyte: lua_method!(StringBuffer => mut lua => {
				let byte = lua.check_integer(2) as u8;
				lua.check_self_mut().bytes.push(byte);
			}),
			pushutf8: lua_method!(StringBuffer => mut lua => {
				let codepoint = lua.check_integer(2) as u32;
				let Some(c) = char::from_u32(codepoint) else {
					lua.error_c_str(c"invalid codepoint")
				};

				let mut buf = [0u8; 4];
				lua.check_self_mut()
					.bytes.extend_from_slice(c.encode_utf8(&mut buf).as_bytes())
					;
			}),
			pushstring: lua_method!(StringBuffer => lua => {
				unsafe {
					lua.no_gc().check_self_mut()
						.bytes.extend_from_slice(lua.no_gc().check_string(2))
						;
				}
			}),
		};
		lua.new_lib(&INDEX);
		lua.set_field(-2, c"__index");
	}
}
