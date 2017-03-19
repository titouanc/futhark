-- Check that shape annotations are checked when output shape is the sum
-- of both input shapes
-- ==
-- input { [42, 27, 12] [13] }
-- output { [0, 1, 2, 3] }

fun main(_: [n]i32, _: [m]i32): [m+n]i32 = iota (m + n)
