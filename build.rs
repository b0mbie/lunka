fn main() {
	#[cfg(feature = "link-vendored")]
	{
		::lunka_src::Build::for_current()
			.add_lunka_src()
			.compile("lua");
	}
}
