use core::{
	ffi::{
		c_int, c_void,
	},
	num::NonZero,
	ops::ControlFlow,
	slice::from_raw_parts,
};

use crate::{
	cdef::lua_State,
	util::lunka_attrs,
	Thread,
};

/// Types that Lua can dump the binary representation of functions into.
pub trait Writer<'l> {
	/// Status returned after writing a chunk. See also [`WriterStatus`].
	type Status: WriterStatus;
	/// Writes the next binary chunk.
	fn write_chunk(&mut self, chunk: &[u8], lua: &'l mut Thread) -> Self::Status;

	/// Returns `true` if this writer expects stripped debug information.
	fn strip_debug_info(&mut self) -> bool {
		false
	}
}

const _ASSERT_DYN_WRITER_IS_A_THING: () = {
	let _: Option<&dyn Writer<'static, Status = ()>> = None;
};

/// Type for the status used by the C API.
pub type RawStatus = c_int;

/// Types that report a [`RawStatus`] for Lua's function dumping API.
pub trait WriterStatus {
	/// Converts `Self` into a [`RawStatus`].
	fn into_raw(self) -> RawStatus;
	/// Converts a [`RawStatus`] into `Self`.
	/// 
	/// # Safety
	/// `raw` must have been previously returned by [`into_raw`](WriterStatus::into_raw)
	/// implemented for this type.
	unsafe fn from_raw(raw: RawStatus) -> Self;
}
/// `()` always reports "OK".
impl WriterStatus for () {
	fn into_raw(self) -> RawStatus {OK}
	unsafe fn from_raw(_: RawStatus) -> Self {}
}
impl WriterStatus for RawStatus {
	fn into_raw(self) -> RawStatus {self}
	unsafe fn from_raw(raw: RawStatus) -> Self {raw}
}
impl WriterStatus for ControlFlow<NonZero<RawStatus>, ()> {
	fn into_raw(self) -> c_int {
		match self {
			Self::Continue(..) => OK,
			Self::Break(status) => status.get(),
		}
	}
	unsafe fn from_raw(raw: c_int) -> Self {
		if let Some(status) = NonZero::new(raw) {
			Self::Break(status)
		} else {
			Self::Continue(())
		}
	}
}

const OK: c_int = 0;

impl Thread {
	lunka_attrs! {
		[may_raise(arbitrary), runs_code]
		/// Dumps a function as a binary chunk,
		/// and returns the status of the operation.
		/// 
		/// This function receives a Lua function on the top of the stack
		/// and produces a binary chunk that, if loaded again,
		/// results in a function equivalent to the one dumped.
		/// 
		/// # Errors
		/// The underlying Lua state may raise an arbitrary [error](crate::errors).
		pub fn dump<'l, W>(&'l mut self, writer: &mut W) -> W::Status
		where
			W: Writer<'l>,
		{
			let strip_debug_info = writer.strip_debug_info();
			let ud = writer as *mut W as _;
			unsafe {
				let raw = self.dump_raw(l_writer::<'l, W>, ud, strip_debug_info);
				<W::Status>::from_raw(raw)
			}
		}
	}
}

unsafe extern "C-unwind" fn l_writer<'l, W>(
	l: *mut lua_State, p: *const c_void, sz: usize, ud: *mut c_void
) -> c_int
where
	W: Writer<'l>,
{
	let l = unsafe { Thread::from_ptr_mut(l) };
	let chunk = unsafe { from_raw_parts(p.cast::<u8>(), sz) };
	let reader = unsafe { ud.cast::<W>().as_mut_unchecked() };
	let status = reader.write_chunk(chunk, l);
	status.into_raw()
}
