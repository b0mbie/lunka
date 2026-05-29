use lunka::prelude::*;

fn main() {
	std::panic::catch_unwind(move || {
		let mut lua = Lua::new();
		lua.at_panic(Some(lunka::lua_panic_handler));
		lua.push_function(lua_func!(lua => {
			struct Guard;
			impl Drop for Guard {
				fn drop(&mut self) {
					println!("`Guard` dropped");
				}
			}

			// May or may not be dropped!
			#[allow(unused_variables)]
			let guard = Guard;

			if true {
				lua.error_c_str(c"uh oh!");
			}
		}));
		unsafe { lua.managed().call(0, 0) }
	}).unwrap_err();
}
