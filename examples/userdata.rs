use lunka::prelude::*;

fn main() {
	let mut lua = Lua::new();
	lua.register_udata::<Vector>();
	lua.push_udata(Vector {
		x: 42.0,
		y: -123.456,
		z: 10003.333,
	});
	assert_eq!(lua.to_c_str_meta(-1), c"(42.000, -123.456, 10003.333)");
}

struct Vector {
	pub x: f32,
	pub y: f32,
	pub z: f32,
}
lua_impl_userdata!(Vector);
impl LuaUserData for Vector {
	fn init_metatable(lua: &mut LuaThread) {
		lua.push_function(lua_method!(Vector => mut lua => {
			let Vector { x, y, z } = *lua.check_self();
			lua.push_display(&format_args!("({x:.3}, {y:.3}, {z:.3})"));
			1
		}));
		lua.set_field(-2, c"__tostring");
	}
}
