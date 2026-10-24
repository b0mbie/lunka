use lunka::prelude::*;
use std::{
	io::Write,
	ops::RangeInclusive,
};

fn main() {
	let mut lua = Lua::new();

	let iter = -2..=5;
	let mut reader = ReturnRange {
		state: State::Return,
		buffer: vec![],
		iter: iter.clone(),
	};
	assert_eq!(lua.load(c"=ReturnRange", &mut reader), LuaStatus::Ok);

	let mut dump = DumpBuffer(vec![]);
	lua.dump(&mut dump);
	lua.pop(1);

	assert_eq!(lua.load(c"=ReturnRange", &mut LoadBuffer(&dump.0)), LuaStatus::Ok);

	assert_eq!(lua.pcall(0, iter.clone().count() as _, 0), LuaStatus::Ok);

	for (stack_index, expected) in (1..).zip(iter) {
		let real = lua.to_integer(stack_index).expect("stack should only have integers");
		assert_eq!(expected, real, "incorrect value at stack index {stack_index}");
	}
}

/// Reads a chunk of the form
/// `return n, n+1, ..., m`, where
/// `n` and `m` are the limits of its inner [`RangeInclusive`] iterator.
struct ReturnRange {
	state: State,
	buffer: Vec<u8>,
	iter: RangeInclusive<LuaInteger>,
}

enum State {
	Return,
	ValueFirst,
	Value,
}

impl<'l> LuaReader<'l> for ReturnRange {
	fn read_chunk(&mut self, _: &'l mut LuaThread) -> &[u8] {
		match self.state {
			State::Return => {
				self.state = State::ValueFirst;
				b"return".as_slice()
			}
			State::ValueFirst => {
				self.state = State::Value;
				self.buffer.clear();
				if let Some(n) = self.iter.next() {
					let _ = write!(self.buffer, " {n}");
				}
				&self.buffer
			}
			State::Value => {
				self.buffer.clear();
				if let Some(n) = self.iter.next() {
					let _ = write!(self.buffer, ", {n}");
				}
				&self.buffer
			}
		}
	}

	fn chunk_format(&mut self) -> Option<LuaChunkFormat> {
		Some(LuaChunkFormat::Text)
	}
}

struct DumpBuffer(pub Vec<u8>);
impl<'l> LuaWriter<'l> for DumpBuffer {
	type Status = ();
	fn write_chunk(&mut self, chunk: &[u8], _: &'l mut LuaThread) -> Self::Status {
		self.0.extend_from_slice(chunk)
	}
}

struct LoadBuffer<'a>(pub &'a [u8]);
impl<'l> LuaReader<'l> for LoadBuffer<'_> {
	fn read_chunk(&mut self, _: &'l mut LuaThread) -> &[u8] {
		std::mem::take(&mut self.0)
	}
}
