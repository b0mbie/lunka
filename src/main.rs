//! Lua runtime stuff.

use lunka::*;

use core::ffi::CStr;

const TEST_CODE: &CStr = unsafe { CStr::from_bytes_with_nul_unchecked(
	b"print(\"I'm difficult-icult\")\0"
) };

fn main() -> Result<(), Box<dyn std::error::Error>> {
	let mut lua = Lua::new_auxlib_default().ok_or("couldn't allocate Lua state")?;
	println!("Running Lua {}", lua.version());
	
	let status = lua.load_string(TEST_CODE);
	if status.is_ok() {
		println!("load OK");
		let status = lua.run_managed(|mut mg| {
			mg.pcall(0, 0, 0)
		});
		if status.is_ok() {
			println!("  run OK");
		} else {
			println!("  run FAILED");
			if let Some(message) = unsafe { lua.to_string(-1) } {
				let message = String::from_utf8_lossy(message.to_bytes());
				println!("    {message}");
			} else {
				println!("    <no available error message>");
			}
			lua.pop(1);
		}
	} else {
		println!("load FAILED");
		if let Some(message) = unsafe { lua.to_string(-1) } {
			lua.pop(1);
			let message = String::from_utf8_lossy(message.to_bytes());
			println!("  {message}");
		} else {
			println!("  <no available error message>");
		}
		lua.pop(1);
	}

	Ok(())
}
