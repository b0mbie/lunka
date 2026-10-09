use core::ffi::{
	CStr, c_char,
};

pub const unsafe fn opt_c_str<'a>(ptr: *const c_char) -> Option<&'a CStr> {
	if !ptr.is_null() {
		unsafe { Some(CStr::from_ptr(ptr)) }
	} else {
		None
	}
}

macro_rules! lunka_attrs {
	{
		@impl
		{$($meta:tt)*}
		[$(,)?]

		$($t:tt)*
	} => {
		$($meta)*
		$($t)*
	};
	{
		@impl
		$meta:tt
		[may_raise(arbitrary), $($m:tt)*]

		$($t:tt)*
	} => {
		$crate::util::lunka_attrs! {
			@impl
			$meta
			[$($m)*]
			$($t)*
		}
	};
	{
		@impl
		$meta:tt
		[may_raise(memory), $($m:tt)*]

		$($t:tt)*
	} => {
		$crate::util::lunka_attrs! {
			@impl
			$meta
			[$($m)*]
			$($t)*
		}
	};
	{
		@impl
		$meta:tt
		[runs_code, $($m:tt)*]

		$($t:tt)*
	} => {
		$crate::util::lunka_attrs! {
			@impl
			$meta
			[$($m)*]
			$($t)*
		}
	};

	{
		@collect
		{$($m:tt)*}
		$attrs:tt

		#[$meta:meta]
		$($rest:tt)*
	} => {
		$crate::util::lunka_attrs! {
			@collect
			{$($m)* #[$meta]}
			$attrs

			$($rest)*
		}
	};

	{
		@collect
		$meta:tt
		$attrs:tt

		$($rest:tt)*
	} => {
		$crate::util::lunka_attrs! {
			@impl
			$meta
			$attrs

			$($rest)*
		}
	};

	{
		[$($m:tt)*]
		$($t:tt)*
	} => {
		$crate::util::lunka_attrs! {
			@collect
			{}
			[$($m)*,]
			$($t)*
		}
	};
}
pub(crate) use lunka_attrs;
