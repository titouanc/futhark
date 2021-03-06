-- ==
-- input {
--   [1,2,3,4,5,6,7,8,9]
-- }
-- output {
--   [[1, 2, 3], [4, 5, 6], [7, 8, 9]]
-- }

import "futlib/math"

fun intsqrt(x: i32): i32 =
    i32(f32.sqrt(f32(x)))

fun main (a: [n]i32): [][]i32 =
    reshape (intsqrt(n), intsqrt(n)) a
