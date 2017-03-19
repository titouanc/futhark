-- Check that shape annotations are checked when output shape is determined
-- statically but does not match expression shape
-- ==
-- input { [42, 34, 21, 7] }
-- error:

fun main(_: [n]i32): [n]i32 = iota 42
