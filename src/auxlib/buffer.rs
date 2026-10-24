use core::{
	ffi::{
		CStr, c_char,
	},
	fmt::{
		self, Write,
	},
	marker::{
		PhantomData, PhantomPinned,
	},
	pin::{
		Pin, pin,
	},
	ptr::null_mut,
};

use crate::{
	cdef::auxlib::*,
	Thread,
};

/// String buffer that allows code to build Lua strings piecemeal.
#[derive(Debug)]
#[repr(transparent)]
pub struct Buffer<'l> {
	raw: luaL_Buffer,
	thread: PhantomData<&'l mut Thread>,
	_pinned: PhantomPinned,
}

const fn uninit_buffer() -> luaL_Buffer {
	luaL_Buffer {
		b: null_mut(),
		size: 0,
		n: 0,
		L: null_mut(),
		init: luaL_Buffer_init {
			_alignment: [], b: [0; _],
		},
	}
}

impl<'l> Buffer<'l> {
	/// Returns a mutable pointer to the inner [`luaL_Buffer`] structure.
	pub const fn as_mut_ptr(&mut self) -> *mut luaL_Buffer {
		&mut self.raw
	}

	const unsafe fn from_raw(raw: luaL_Buffer) -> Self {
		Self {
			raw,
			thread: PhantomData,
			_pinned: PhantomPinned,
		}
	}

	/// # Safety
	/// The returned buffer requires initialization before it can be used.
	const unsafe fn uninit() -> Self {
		unsafe { Self::from_raw(uninit_buffer()) }
	}

	/// # Safety
	/// `self` must be uninitialized.
	unsafe fn init_in(&mut self, lua: &'l mut Thread) {
		unsafe { luaL_buffinit(lua.as_ptr(), self.as_mut_ptr()) };
	}

	/// # Safety
	/// `self` must be uninitialized.
	unsafe fn init_with_capacity_in(&mut self, lua: &'l mut Thread, capacity: usize) {
		unsafe { luaL_buffinitsize(lua.as_ptr(), self.as_mut_ptr(), capacity) };
	}
	
	/// # Safety
	/// `self` must not be used for any other operations after this call.
	unsafe fn finish(self: Pin<&mut Self>) {
		debug_assert!(
			self.raw.n <= self.raw.size,
			"buffer length is bigger than its capacity"
		);
		unsafe { luaL_pushresult(self.get_unchecked_mut().as_mut_ptr()) }
	}

	/// Allocates enough space in the buffer for a given number of C characters,
	/// and returns a pointer to it.
	/// 
	/// # Errors
	/// The underlying Lua state may raise a memory [error](crate::errors).
	/// 
	/// # Safety
	/// The returned pointer may only be used while the buffer is valid.
	pub unsafe fn prep(self: Pin<&mut Self>, size: usize) -> *mut c_char {
		unsafe { luaL_prepbuffsize(self.get_unchecked_mut().as_mut_ptr(), size) }
	}

	/// Allocates enough space in the buffer for [`LUAL_BUFFERSIZE`] C characters,
	/// and returns a pointer to it.
	/// 
	/// See also [`prep`](Self::prep).
	/// 
	/// # Errors
	/// The underlying Lua state may raise a memory [error](crate::errors).
	/// 
	/// # Safety
	/// The returned pointer may only be used while the buffer is valid.
	pub unsafe fn prep_default(self: Pin<&mut Self>) -> *mut c_char {
		unsafe { self.prep(LUAL_BUFFERSIZE) }
	}

	/// Returns the current length of the buffer.
	pub const fn len(&self) -> usize {
		self.raw.n
	}

	/// Returns `true` if the buffer is empty.
	pub const fn is_empty(&self) -> bool {
		self.raw.n == 0
	}

	/// Sets the current length of the buffer.
	/// 
	/// # Safety
	/// `len` must be less than or equal to the reported capacity,
	/// and all bytes in range should be initialized.
	pub const unsafe fn set_len(self: Pin<&mut Self>, len: usize) {
		unsafe { self.get_unchecked_mut().raw.n = len }
	}

	/// Returns the current capacity of the buffer.
	pub const fn capacity(&self) -> usize {
		self.raw.size
	}

	/// Returns an immutable reference to the [`Thread`].
	pub fn thread(&self) -> &'l Thread {
		unsafe { Thread::from_ptr(self.raw.L) }
	}

	/// Returns a mutable reference to the [`Thread`].
	pub fn thread_mut(self: Pin<&mut Self>) -> &'l mut Thread {
		unsafe { Thread::from_ptr_mut(self.raw.L) }
	}

	/// Adds one C character to the buffer.
	/// 
	/// # Errors
	/// The underlying Lua state may raise a memory [error](crate::errors).
	pub fn add_char(mut self: Pin<&mut Self>, ch: c_char) {
		let len = self.as_ref().len();
		if len >= self.as_ref().capacity() {
			unsafe { luaL_prepbuffsize(self.as_mut().get_unchecked_mut().as_mut_ptr(), 1) };
		}
		unsafe { *self.as_mut().raw.b.add(len) = ch }
		unsafe { self.set_len(len.wrapping_add(1)) }
	}

	/// Adds one byte to the buffer.
	/// 
	/// # Errors
	/// The underlying Lua state may raise a memory [error](crate::errors).
	pub fn add_byte(self: Pin<&mut Self>, b: u8) {
		self.add_char(b as _)
	}

	/// Removes a given number of C characters from the buffer.
	pub fn remove(self: Pin<&mut Self>, n: usize) {
		let new_len = self.as_ref().len().saturating_sub(n);
		unsafe { self.set_len(new_len) }
	}

	/// Adds a string to the buffer.
	/// 
	/// # Errors
	/// The underlying Lua state may raise a memory [error](crate::errors).
	pub fn add_string<S: AsRef<[u8]>>(self: Pin<&mut Self>, data: S) {
		let data = data.as_ref();
		unsafe { luaL_addlstring(
			self.get_unchecked_mut().as_mut_ptr(),
			data.as_ptr() as *const _, data.len(),
		) }
	}

	/// Adds a C string to the buffer.
	/// 
	/// # Errors
	/// The underlying Lua state may raise a memory [error](crate::errors).
	pub fn add_c_str(self: Pin<&mut Self>, data: &CStr) {
		unsafe { luaL_addstring(self.get_unchecked_mut().as_mut_ptr(), data.as_ptr()) }
	}

	/// Converts a value on top of the associated Lua stack to a string,
	/// and pops the result into the buffer.
	pub fn add_value(self: Pin<&mut Self>) {
		unsafe { luaL_addvalue(self.get_unchecked_mut().as_mut_ptr()) }
	}
}

impl fmt::Write for Pin<&mut Buffer<'_>> {
	fn write_str(&mut self, s: &str) -> fmt::Result {
		self.as_mut().add_string(s.as_bytes());
		Ok(())
	}

	fn write_char(&mut self, c: char) -> fmt::Result {
		let mut char_data = [0u8; 4];
		c.encode_utf8(&mut char_data);
		self.as_mut().add_string(char_data);
		Ok(())
	}
}

impl Thread {
	/// Fills a [`Buffer`]
	/// with the given closure
	/// and pushes it onto the stack.
	pub fn push_buffer<F: FnOnce(Pin<&mut Buffer<'_>>)>(&mut self, f: F) {
		unsafe {
			let mut buffer = pin!(Buffer::uninit());
			buffer.as_mut().get_unchecked_mut().init_in(self);
			f(buffer.as_mut());
			buffer.finish()
		}
	}

	/// Fills a [`Buffer`] of a known capacity
	/// with the given closure
	/// and pushes it onto the stack.
	pub fn push_buffer_with_capacity<F: FnOnce(Pin<&mut Buffer<'_>>)>(&mut self, capacity: usize, f: F) {
		unsafe {
			let mut buffer = pin!(Buffer::uninit());
			buffer.as_mut().get_unchecked_mut().init_with_capacity_in(self, capacity);
			f(buffer.as_mut());
			buffer.finish()
		}
	}

	/// Pushes a [`Display`](fmt::Display) representation of `T` onto the stack
	/// as a Lua string.
	pub fn push_display<T: ?Sized + fmt::Display>(&mut self, t: &T) {
		self.push_buffer(move |mut buffer| {
			let _ = write!(buffer, "{t}");
		})
	}

	/// Pushes a [`Debug`](fmt::Debug) representation of `T` onto the stack
	/// as a Lua string.
	pub fn push_debug<T: ?Sized + fmt::Debug>(&mut self, t: &T) {
		self.push_buffer(move |mut buffer| {
			let _ = write!(buffer, "{t:?}");
		})
	}
}
