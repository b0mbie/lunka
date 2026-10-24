use core::{
	ffi::CStr,
	mem::needs_drop,
};

use crate::{
	Thread, UserValueIdx,
	Rets,
};

use super::{
	UserDataBase, UserData,
	SelfCtx,
};

#[repr(transparent)]
pub struct Gc<T> {
	inner: Option<T>,
}

impl<T: GcCollect> Gc<T> {
	pub const fn new(inner: T) -> Self {
		Self {
			inner: Some(inner),
		}
	}

	pub const fn as_inner(&self) -> Option<&T> {
		self.inner.as_ref()
	}

	pub const fn as_mut_inner(&mut self) -> Option<&mut T> {
		self.inner.as_mut()
	}

	extern "C-unwind" fn mt_gc(mut cx: SelfCtx<'_, Self>) -> Rets {
		let this = unsafe { cx.check_self_ptr().as_mut() };
		if let Some(this) = this.inner.as_mut() {
			T::collect(DoCollectCtx {
				this,
				thread: &mut cx,
			});
		}
		drop(this.inner.take());
		Rets::ZERO
	}
}

unsafe impl<T: GcCollect> UserDataBase for Gc<T> {
	fn n_uservalues(lua: &Thread) -> UserValueIdx {
		T::n_uservalues(lua)
	}
	fn with_table_name<'l, F: FnOnce(&'l Thread, &CStr) -> R, R>(lua: &'l Thread, f: F) -> R {
		f(lua, T::TABLE_NAME)
	}
}

impl<T: GcCollect> UserData for Gc<T> {
	fn init_metatable(lua: &mut Thread) {
		let mut needs_collect = false;
		T::init_metatable(lua);
		T::collect(ReportCtx {
			needs_collect: &mut needs_collect,
		});
		if needs_drop::<T>() || needs_collect {
			lua.push_method(Self::mt_gc);
			lua.set_field(-2, c"__gc");
		}
	}
}

pub unsafe trait GcCollectBase {
	const TABLE_NAME: &CStr;
	fn n_uservalues(lua: &Thread) -> UserValueIdx;
}

#[macro_export]
macro_rules! impl_gc_collect {
	($n_uservalues:expr => $Type:ty) => {
		const _: () = {
			unsafe impl $crate::userdata::GcCollectBase for $Type {
				const TABLE_NAME: &::core::ffi::CStr = unsafe {
					::core::ffi::CStr::from_bytes_with_nul_unchecked(
						::core::concat! {
							::core::module_path!(), "::", ::core::stringify! {$Type}, '\0'
						}.as_bytes()
					)
				};
				fn n_uservalues(_: &$crate::Thread) -> $crate::UserValueIdx {
					$n_uservalues
				}
			}

			const _ASSERT_GC_COLLECT_BASE_ALIGNMENT: () = ::core::assert! {
				::core::mem::align_of::<$Type>() <= $crate::userdata::MAX_ALIGN,
				::core::concat! {
					'`', ::core::stringify! {$Type}, "` does not meet alignment requirement for `GcCollectBase`"
				}
			};
		};
	};
	($Type:ty) => {
		$crate::impl_gc_collect! {0 => $Type}
	};
	{$($whatever:tt)*} => {
		::core::compile_error! {
			"expected `[<# of uservalues> =>] <type to implement for>`"
		}
	};
}

pub trait GcCollect: GcCollectBase {
	/// Initializes the Lua type's metatable on the top of the stack.
	/// 
	/// You do not need to set `__gc` to handle destruction -
	/// the given metatable already has `__gc` set to run the type's destructor if needed.
	fn init_metatable(lua: &mut Thread) {
		let _ = lua;
	}

	/// Collects an instance of this type,
	/// given the [`Thread`] it's in.
	/// 
	/// The implementation should call [`CollectCtx::collect`]
	/// if it desires special destruction logic.
	/// This function is called two times:
	/// 1. during metatable initialization, to check whether
	///    the type desires collection if it does not already implement [`Drop`];
	/// 2. by the `__gc` metamethod provided by [`Gc<Self>`].
	/// 
	/// In the first case, `cx` will not actually run the collection callback,
	/// but will report that a collection is desired to the metatable construction logic.
	fn collect<C: CollectCtx<Self>>(cx: C) {
		let _ = cx;
	}
}

pub trait CollectCtx<T: ?Sized> {
	fn collect<F: FnOnce(&mut T, &mut Thread)>(self, f: F);
}

struct ReportCtx<'a> {
	needs_collect: &'a mut bool,
}
impl<'a, T: ?Sized> CollectCtx<T> for ReportCtx<'a> {
	fn collect<F: FnOnce(&mut T, &mut Thread)>(self, _: F) {
		*self.needs_collect = true
	}
}

struct DoCollectCtx<'a, T: ?Sized> {
	this: &'a mut T,
	thread: &'a mut Thread,
}
impl<'a, T: ?Sized> CollectCtx<T> for DoCollectCtx<'a, T> {
	fn collect<F: FnOnce(&mut T, &mut Thread)>(self, f: F) {
		f(self.this, self.thread)
	}
}
