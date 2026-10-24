fn main() {
	#[cfg(feature = "link-vendored")]
	{
		let mut lua = ::lunka_src::Build::for_current();
		lua.add_lunka_src();
		if cfg!(feature = "link-vendored-api-checks") {
			lua.api_checks();
		}
		lua.compile("lua");
	}
}
