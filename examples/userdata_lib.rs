//! Example of how to integrate userdata into a library.

use core::{
	ffi::{
		CStr, c_int,
	},
	fmt::{
		Display,
		Formatter,
		Result as FmtResult,
		Write
	}
};
use lunka::prelude::*;

/// Simple tagged logger.
pub struct Logger {
	pub tag: Vec<u8>,
}

impl Logger {
	/// Log an informational message.
	pub fn info<T: Display>(&self, message: T) {
		println!(
			"[{}] info: {}",
			LossyStrDisplay(&self.tag), message
		);
	}
}

/// Shim for displaying bytes with possibly-invalid UTF-8 sequences.
#[repr(transparent)]
struct LossyStrDisplay<'a>(pub &'a [u8]);

impl Display for LossyStrDisplay<'_> {
	fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
		for chunk in self.0.utf8_chunks() {
			f.write_str(chunk.valid())?;
			if !chunk.invalid().is_empty() {
				f.write_char(char::REPLACEMENT_CHARACTER)?;
			}
		}
		Ok(())
	}
}

/// Name of the metatable associated with [`Logger`].
const LOGGER_MT_NAME: &CStr = c"Logger";
/// Metatable for [`Logger`], which is responsible for method call support and
/// proper garbage collection.
const LOGGER_MT: LuaLibrary<2> = lua_library! {
	__gc: lua_function!(l => {
		let lua = LuaThread::from_ptr(l);
		lua.check_udata(1, LOGGER_MT_NAME)
			.cast::<Logger>()
			.as_ptr().drop_in_place();
		0
	}),
	__index
};
/// Methods for interacting with [`Logger`]s from Lua.
const LOGGER_LIB: LuaLibrary<2> = lua_library! {
	set_tag: lua_function!(l => {
		let lua = LuaThread::from_ptr(l);
		let this = lua.check_udata(1, LOGGER_MT_NAME).cast::<Logger>().as_mut();

		this.tag.clear();
		this.tag.extend_from_slice(lua.to_string(2).unwrap_or(b""));

		0
	}),
	info: lua_function!(l => {
		let lua = LuaThread::from_ptr(l);
		let this = lua.check_udata(1, LOGGER_MT_NAME).cast::<Logger>().as_ref();

		this.info(LossyStrDisplay(lua.to_string(2).unwrap_or(b"")));

		0
	})
};

unsafe extern "C" fn luaopen_logging(l: *mut LuaState) -> c_int {
	let lua = LuaThread::from_ptr(l);
	lua.new_metatable(LOGGER_MT_NAME);
	{
		lua.set_funcs(&LOGGER_MT, 0);

		// `__index` is set to `false` by default.
		lua.push_string(b"__index");
		lua.new_lib(&LOGGER_LIB);
		lua.raw_set(-3);
	}

	/// `logging` library exposed to Lua.`
	const USERDATA_LIB: LuaLibrary<1> = lua_library! {
		new_logger: lua_function!(l => {
			let lua = LuaThread::from_ptr(l);
			let tag = lua.check_string(1);
			lua.new_userdata_t::<Logger>(0)
				.write(Logger {
					tag: tag.to_vec()
				});
			lua.set_aux_metatable(LOGGER_MT_NAME);
			1
		})
	};
	lua.new_lib(&USERDATA_LIB);

	1
}

unsafe extern "C" fn lua_main(l: *mut LuaState) -> c_int {
	let lua = LuaThread::from_ptr_mut(l);

	lua.run_managed(move |mut mg| {
		mg.require(
			c"logging",
			luaopen_logging,
			true
		);
		mg.pop(1);
	});

	if !lua.load_string(
		r#"
local logger = logging.new_logger("test")
logger:info("Hello, world!")
logger:set_tag("test (modified)")
logger:info("Hello again!")
		"#,
		c"=<embedded>"
	).is_ok() {
		lua.error()
	}

	lua.run_managed(move |mut mg| {
		mg.restart_gc();
		mg.switch_gc_to(lunka::GcMode::Generational {
			minor_mul: 0,
			major_mul: 0
		});
		mg.call(0, 0)
	});

	0
}

fn main() {
	let mut lua = Lua::new();
	lua.run_managed(move |mut mg| {
		mg.push_c_function(lua_main);
		mg.pcall(0, 0, 0);
	});
}
