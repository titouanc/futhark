-- Check that shape annotations are checked when input and output shape
-- are the same
-- ==
-- input { [42, 34, 21, 7] }
-- output { [0, 1, 2, 3] }

fun main(_: [n]i32): [n]i32 = iota n
