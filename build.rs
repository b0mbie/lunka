//! Build script to link against `lua54`.

fn main() {
	println!("cargo:rustc-link-search={}/build", env!("LUA_DIR"));
	println!("cargo:rustc-link-lib=lua54");
}
