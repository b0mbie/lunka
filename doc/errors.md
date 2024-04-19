# Guide for handling Lua errors.
Lua state operations that may involve memory allocation or unprotected execution
of metamethods or other arbitrary code, can raise Lua errors.

# Error handling in Lua
By default, Lua uses `setjmp` and `longjmp` in C, and exceptions in C++.
These error mechanisms may or may not unwind the stack, depending on the
implementation.
(See `ldo.c` for more information, specifically the macros `LUAI_THROW` and
`LUAI_TRY`.)

A Lua state raising an error in Rust code is Undefined Behavior.
For example, raising an error can:
- leak memory.
- put data structures into invalid states.
- unwind the Rust stack safely and cause no further issues whatsoever.
This *can* happen if Lua was compiled with the proper mechanisms in place to
safely unwind Rust stacks.

Therefore, any function that can raise *any* sort of error is **unsafe**,
because the compiler cannot guarantee that the function was called in an
environment that's *entirely* safe to unwind.
(This is where the [`UnwindSafe`](core::panic::UnwindSafe) trait may
potentially prove useful somehow.)

One exception to this is the function [`lua_error`](crate::cdef::lua_error),
since it is defined to *always* raise an error, therefore the compiler can
correctly anticipate that code after a call of this function is unreachable.

# Error safety
Rust code can use potentially-error-raising functions safely.
There are a few aspects to keep in mind, however.

## Non-userdata memory can be leaked
Data structures like `Box` will not free used memory if they are not dropped in
code.
However, userdata is properly managed by Lua, and will be collected if an error
occurs.
Rust code can also use finalizers to run drop glue if the type isn't simply
[`Copy`].

## Data structures can be put into invalid states
If a Lua error is raised during the initialization process of a structure, then
that structure can be left in an invalid state, which can later be observed
externally.

As an extension of the above, structures that have important [`Drop`]
implementations, such as mutex RAII locks, will not have them run.
With a mutex, this may mean that the mutex will be poisoned, which can be
observed when attempting to access its data again.
