--- @diagnostic disable: undefined-global
-- Test code for Lua to run.

print("I'm difficult-icult", ...)
rs.print("Hello, Rust!", ...)

rs.raise("bee") -- bug