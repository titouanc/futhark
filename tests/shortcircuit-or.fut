-- && must be short-circuiting.
--
-- ==
-- input { 0 [false, false] } output { false }
-- input { 1 [false, false] } output { false }
-- input { 2 [false, false] } output { true }

fun main(i: i32, bs: [n]bool): bool =
  i >= n || bs[i]
