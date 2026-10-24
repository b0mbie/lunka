use lunka::prelude::*;

fn main() {
	let mut lua = Lua::new();
	lua.open_libs();

	assert_eq!(lua.load_string(CODE, c"=<embedded>"), LuaStatus::Ok, "failed to load embedded code");
	{
		let dbg = unsafe { lua.debug() };
		let info = dbg.get_func_info(LuaDebugFlags::everything())
			.expect("should be able to get information for our code")
			;
		println!("{info:#?}");
	}

	assert_eq!(lua.pcall(0, 1, 0), LuaStatus::Ok);
	{
		let dbg = unsafe { lua.debug() };
		let info = dbg.get_func_info(LuaDebugFlags::nothing().with_prototype())
			.expect("should be able to get information for our code")
			;
		assert_eq!(info.n_parameters(), 2, "there should be 2 parameters in the returned function");
		assert!(info.is_variadic(), "the returned function should be variadic");
	}
}

const CODE: &str = r#"
-- Example of a script that can be inspected with the debug interface.
print("Returning a variadic function with 2 initial parameters.")
return function (a, b, ...) end
"#;
