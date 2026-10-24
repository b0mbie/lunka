use core::{
	marker::PhantomData,
	mem::transmute,
	ops::{
		Deref, DerefMut,
	},
	ptr::NonNull,
};

use crate::{
	Func, Ctx, Rets,
	Thread,
};

use super::UserData;

impl Thread {
	/// Pushes the given method function onto the stack.
	pub fn push_method<T: UserData>(&mut self, f: MethodFunc<T>) {
		self.push_function(method_to_func(f))
	}
}

#[repr(transparent)]
pub struct SelfThread<T> {
	thread: Thread,
	_t: PhantomData<fn() -> T>,
}

impl<T: UserData> SelfThread<T> {
	pub(crate) const fn from_thread(l: &Thread) -> &Self {
		unsafe { &*(l as *const Thread as *const _) }
	}

	pub(crate) const fn from_mut_thread(l: &mut Thread) -> &mut Self {
		unsafe { &mut *(l as *mut Thread as *mut _) }
	}

	#[allow(clippy::mut_from_ref)]
	pub const unsafe fn no_gc(&self) -> &mut Self {
		unsafe { Self::from_mut_thread(Thread::from_ptr_mut(self.thread.as_ptr_no_gc())) }
	}

	/// Returns a pointer to `self` as a `T`.
	/// 
	/// # Errors
	/// The inner Lua state may raise an [error](crate::errors)
	/// if the `self` argument is not `T`.
	pub fn check_self_ptr(&self) -> NonNull<T> {
		self.check_udata_ptr(1)
	}

	/// Returns an immutable reference to `self` as a `T`.
	/// 
	/// # Errors
	/// The inner Lua state may raise an [error](crate::errors)
	/// if the `self` argument is not `T`.
	pub fn check_self(&self) -> &T {
		self.check_udata(1)
	}

	/// Returns a mutable reference to `self` as a `T`.
	/// 
	/// # Errors
	/// The inner Lua state may raise an [error](crate::errors)
	/// if the `self` argument is not `T`.
	pub fn check_self_mut(&mut self) -> &mut T {
		self.check_udata_mut(1)
	}
}

impl<T> Deref for SelfThread<T> {
	type Target = Thread;
	fn deref(&self) -> &Self::Target {
		&self.thread
	}
}
impl<T> DerefMut for SelfThread<T> {
	fn deref_mut(&mut self) -> &mut Self::Target {
		&mut self.thread
	}
}

/// # Layout
/// This type has the same layout and ABI as [`Ctx<'a>`].
#[repr(transparent)]
pub struct SelfCtx<'a, T> {
	cx: Ctx<'a>,
	_t: PhantomData<fn() -> T>,
}

impl<T: UserData> Deref for SelfCtx<'_, T> {
	type Target = SelfThread<T>;
	fn deref(&self) -> &Self::Target {
		SelfThread::from_thread(&self.cx)
	}
}
impl<T: UserData> DerefMut for SelfCtx<'_, T> {
	fn deref_mut(&mut self) -> &mut Self::Target {
		SelfThread::from_mut_thread(&mut self.cx)
	}
}

impl<'a, T: UserData> SelfCtx<'a, T> {
	/// Converts this context into a mutable [`SelfThread<T>`].
	pub fn lua(self) -> &'a mut SelfThread<T> {
		SelfThread::from_mut_thread(self.cx.lua())
	}
}

/// Returns a [`MethodFunc`] converted to a [`Func`] that can be called by Lua.
#[macro_export]
macro_rules! method {
	($($t:tt)*) => {
		$crate::userdata::method_to_func($crate::method_func! {$($t)*})
	};
}

/// Returns a [`MethodFunc`] that can be called by Lua.
#[macro_export]
macro_rules! method_func {
	($T:ty => $lua:pat => {$($t:tt)*}) => {{
		extern "C-unwind" fn __lunka_method_inline($lua: $crate::userdata::SelfCtx<'_, $T>) -> $crate::Rets {
			<$crate::Rets as ::core::convert::From<_>>::from((move || {$($t)*})())
		}
		__lunka_method_inline
	}};

	{$($whatever:tt)*} => {
		::core::compile_error! {
			"expected `<Type> => <pattern> => <body>`"
		}
	};
}

/// [`Func`] that is intended to be called on a `self` of type `T`.
pub type MethodFunc<T> = extern "C-unwind" fn(SelfCtx<'_, T>) -> Rets;

/// Converts a [`MethodFunc<T>`] to [`Func`].
pub const fn method_to_func<T: UserData>(f: MethodFunc<T>) -> Func {
	unsafe { transmute(f) }
}
