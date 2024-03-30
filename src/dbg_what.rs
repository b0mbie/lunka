//! See [`DebugWhat`].

use core::ffi::c_char;

/// Helper structure for [`lua_getinfo`](crate::cdef::lua_getinfo).
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct DebugWhat {
	what_flags: u8,
	/// Use a function from the stack instead of an activation record.
	pub using_function: bool
}

const fn has_bit(flags: u8, mask: u8) -> bool{
	(flags & mask) != 0
}

impl DebugWhat {
	const FLAG_FUNC: u8 = (1 << 0);
	const FLAG_CURRENT_LINE: u8 = (1 << 1);
	const FLAG_NAME: u8 = (1 << 2);
	const FLAG_TRANSFER: u8 = (1 << 3);
	const FLAG_SOURCE: u8 = (1 << 4);
	const FLAG_TAIL_CALL: u8 = (1 << 5);
	const FLAG_PROTO: u8 = (1 << 6);
	const FLAG_LINES: u8 = (1 << 7);

	/// Construct an instance with no information required.
	pub const fn nothing() -> Self {
		Self {
			what_flags: 0,
			using_function: false
		}
	}

	/// Write out a "what" string into `buffer` and return the slice that
	/// contains it.
	/// 
	/// The maximum number of C characters that can be written to `buffer` is
	/// `10`, including the zero-terminator.
	pub fn write_string<'a>(&self, buffer: &'a mut [c_char]) -> &'a [c_char] {
		let flags = self.what_flags;
	
		let mut i = 0;
	
		if self.using_function {
			buffer[i] = b'>' as _;
			i += 1;
		}
		if has_bit(flags, Self::FLAG_FUNC) {
			buffer[i] = b'f' as _;
			i += 1;
		}
		if has_bit(flags, Self::FLAG_CURRENT_LINE) {
			buffer[i] = b'l' as _;
			i += 1;
		}
		if has_bit(flags, Self::FLAG_NAME) {
			buffer[i] = b'n' as _;
			i += 1;
		}
		if has_bit(flags, Self::FLAG_TRANSFER) {
			buffer[i] = b'r' as _;
			i += 1;
		}
		if has_bit(flags, Self::FLAG_SOURCE) {
			buffer[i] = b'S' as _;
			i += 1;
		}
		if has_bit(flags, Self::FLAG_TAIL_CALL) {
			buffer[i] = b't' as _;
			i += 1;
		}
		if has_bit(flags, Self::FLAG_PROTO) {
			buffer[i] = b'u' as _;
			i += 1;
		}
		if has_bit(flags, Self::FLAG_LINES) {
			buffer[i] = b'L' as _;
			i += 1;
		}
		buffer[i] = 0;

		&buffer[0..=i]
	}

	/// Require function (push function onto the stack).
	pub const fn with_func(self) -> Self {
		Self {
			what_flags: self.what_flags | Self::FLAG_FUNC,
			..self
		}
	}

	/// Require current line (`current_line`).
	pub const fn with_current_line(self) -> Self {
		Self {
			what_flags: self.what_flags | Self::FLAG_CURRENT_LINE,
			..self
		}
	}

	/// Require name information (`name`, `name_what`).
	pub const fn with_name(self) -> Self {
		Self {
			what_flags: self.what_flags | Self::FLAG_NAME,
			..self
		}
	}

	/// Require transfer information (`first_transferred`, `n_transferred`).
	pub const fn with_transfer_info(self) -> Self {
		Self {
			what_flags: self.what_flags | Self::FLAG_TRANSFER,
			..self
		}
	}

	/// Require source information (`source`, `source_len`, `short_src`,
	/// `line_defined`, `last_line_defined`, `what`).
	pub const fn with_source_info(self) -> Self {
		Self {
			what_flags: self.what_flags | Self::FLAG_SOURCE,
			..self
		}
	}

	/// Require tall call information (`is_tail_call`).
	pub const fn with_tail_call_info(self) -> Self {
		Self {
			what_flags: self.what_flags | Self::FLAG_TAIL_CALL,
			..self
		}
	}

	/// Require function prototype information (`n_upvalues`, `n_params`,
	/// `is_vararg`).
	pub const fn with_prototype(self) -> Self {
		Self {
			what_flags: self.what_flags | Self::FLAG_PROTO,
			..self
		}
	}

	/// Require source code lines (push table of them onto the stack).
	pub const fn with_lines(self) -> Self {
		Self {
			what_flags: self.what_flags | Self::FLAG_LINES,
			..self
		}
	}
}
