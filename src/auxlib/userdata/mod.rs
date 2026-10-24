use core::{
	ffi::CStr,
	mem::MaybeUninit,
	ptr::NonNull,
};

use crate::{
	AcceptableIndex,
	Thread,
	UserValueIdx,
};

mod func;
pub use func::*;
mod gc_drop;
pub use gc_drop::*;

pub use crate::cdef::MAX_ALIGN;

impl Thread {
	/// Registers a [`UserData`] and pushes its metatable onto the stack,
	/// returning `true` if registering for the first time.
	pub fn register_udata<T: UserData>(&mut self) -> bool {
		let is_init = T::with_table_name(self, move |lua, table_name| unsafe {
			lua.no_gc().new_metatable(table_name)
		});

		if is_init {
			T::init_metatable(self);
		}

		is_init
	}

	/// Pushes a [`UserData`] `value` onto the stack.
	pub fn push_udata<T: UserData>(&mut self, value: T) -> &mut T {
		unsafe { self.create_udata_with(move |_, init| { init.write(value); }) }
	}

	/// Allocates and initializes a [`UserData`] using the given `init` function.
	/// 
	/// # Safety
	/// `init` must initialize the value.
	pub unsafe fn create_udata_with<T: UserData, F: FnOnce(&mut Self, &mut MaybeUninit<T>)>(
		&mut self, init: F,
	) -> &mut T {
		let n_uservalues = T::n_uservalues(self);
		unsafe {
			let mut ptr = self.new_userdata_raw(size_of::<T>(), n_uservalues).cast::<MaybeUninit<T>>();
			init(self, ptr.as_mut());
			T::with_table_name(self, move |lua, table_name| {
				lua.set_aux_metatable(table_name)
			});
			ptr.cast::<T>().as_mut()
		}
	}

	pub fn check_udata<T: UserData>(&self, arg: AcceptableIndex) -> &T {
		unsafe { self.check_udata_ptr(arg).as_ref() }
	}

	pub fn check_udata_mut<T: UserData>(&mut self, arg: AcceptableIndex) -> &mut T {
		unsafe { self.check_udata_ptr(arg).as_mut() }
	}

	pub fn test_udata<T: UserData>(&self, arg: AcceptableIndex) -> Option<&T> {
		unsafe { self.test_udata_ptr(arg).map(move |p| p.as_ref()) }
	}

	pub fn test_udata_mut<T: UserData>(&mut self, arg: AcceptableIndex) -> Option<&mut T> {
		unsafe { self.test_udata_ptr(arg).map(move |mut p| p.as_mut()) }
	}

	pub fn check_udata_ptr<T: UserData>(&self, arg: AcceptableIndex) -> NonNull<T> {
		T::with_table_name(self, move |lua, table_name| unsafe {
			lua.check_udata_raw(arg, table_name).cast::<T>()
		})
	}

	pub fn test_udata_ptr<T: UserData>(&self, arg: AcceptableIndex) -> Option<NonNull<T>> {
		T::with_table_name(self, move |lua, table_name| unsafe {
			lua.test_udata_raw(arg, table_name).map(move |p| p.cast::<T>())
		})
	}
}

/// Implements [`UserDataBase`] for the given type.
#[macro_export]
macro_rules! impl_userdata {
	($n_uservalues:expr => $Type:ty) => {
		const _: () = {
			unsafe impl $crate::userdata::UserDataBase for $Type {
				fn n_uservalues(_: &$crate::Thread) -> $crate::UserValueIdx {
					$n_uservalues
				}
				fn with_table_name<'l, F: ::core::ops::FnOnce(&'l $crate::Thread, &::core::ffi::CStr) -> R, R>(
					lua: &'l $crate::Thread, f: F,
				) -> R {
					let table_name = unsafe {
						::core::ffi::CStr::from_bytes_with_nul_unchecked(
							::core::concat! {
								::core::module_path!(), "::", ::core::stringify! {$Type}, '\0'
							}.as_bytes()
						)
					};
					f(lua, table_name)
				}
			}

			const _ASSERT_USER_DATA_BASE_ALIGNMENT: () = ::core::assert! {
				::core::mem::align_of::<$Type>() <= $crate::userdata::MAX_ALIGN,
				::core::concat! {
					'`', ::core::stringify! {$Type}, "` does not meet alignment requirement for `UserDataBase`"
				}
			};
		};
	};
	($Type:ty) => {
		$crate::impl_userdata! {0 => $Type}
	};
	{$($whatever:tt)*} => {
		::core::compile_error! {
			"expected `[<# of uservalues> =>] <type to implement for>`"
		}
	};
}

/// # Safety
/// The metatable name returned by `with_table_name` must
/// *uniquely* (on a best-effort basis) identify the implementing type,
/// the type *must not* be generic,
/// and it must have an alignment `<=` [`MAX_ALIGN`].
pub unsafe trait UserDataBase {
	fn n_uservalues(lua: &Thread) -> UserValueIdx;
	fn with_table_name<'l, F: FnOnce(&'l Thread, &CStr) -> R, R>(lua: &'l Thread, f: F) -> R;
}

pub trait UserData: UserDataBase {
	/// Initializes the Lua type's metatable on the top of the stack.
	fn init_metatable(lua: &mut Thread) {
		let _ = lua;
	}
}
