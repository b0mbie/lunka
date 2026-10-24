use core::ffi::{
	CStr, c_char, c_void,
};

use crate::{
	cdef::{
		lua_State, Status,
	},
	util::lunka_attrs,
	Thread,
};

/// Types that Lua can read source code or a binary dump of a function from.
pub trait Reader<'l> {
	/// Reads the next chunk.
	fn read_chunk(&mut self, lua: &'l mut Thread) -> &[u8];

	/// Returns the [`ChunkFormat`] that should be expected from this reader,
	/// or `None` if there is no particular format that should be expected.
	// N.B. Mode is checked *after* the reader has been called at least once,
	// so the returned string has to be disconnected from the load mode.
	fn chunk_format(&mut self) -> Option<ChunkFormat> {
		None
	}
}

/// Mode for data that can be returned by a [`Reader`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ChunkFormat {
	Binary,
	Text,
	Either,
}

impl ChunkFormat {
	/// Returns the mode string corresponding to this chunk format.
	pub const fn to_mode_str(&self) -> &'static CStr {
		match self {
			Self::Binary => c"b",
			Self::Text => c"t",
			Self::Either => c"bt",
		}
	}
}

const _ASSERT_DYN_READER_IS_A_THING: () = {
	let _: Option<&dyn Reader<'static>> = None;
};

impl Thread {
	lunka_attrs! {
		[may_raise(arbitrary), runs_code]
		/// Loads a Lua chunk without running it.
		/// 
		/// If there are no errors, pushes the compiled chunk as a Lua function.
		/// Otherwise, pushes an error message.
		/// 
		/// # Errors
		/// The underlying Lua state may raise an arbitrary [error](crate::errors).
		pub fn load<'l, R>(&'l mut self, chunk_name: &CStr, reader: &mut R) -> Status
		where
			R: Reader<'l>,
		{
			let mode = reader.chunk_format().map(move |c| c.to_mode_str());
			let ud = reader as *mut R as _;
			unsafe { self.load_raw(l_reader::<'l, R>, ud, chunk_name, mode) }
		}
	}
}

// TODO: Figure out if `dyn Reader<'l>` would be better here somehow.
unsafe extern "C-unwind" fn l_reader<'l, R>(
	l: *mut lua_State, ud: *mut c_void, sz: *mut usize
) -> *const c_char
where
	R: Reader<'l>,
{
	let l = unsafe { Thread::from_ptr_mut(l) };
	let reader = unsafe { ud.cast::<R>().as_mut_unchecked() };
	let data = reader.read_chunk(l);
	unsafe { sz.write(data.len()) }
	data.as_ptr().cast()
}
