-- Nasty loop whose size cannot be predicted in advance.
-- ==
-- input {
--   [1,2,3]
--   4
-- }
-- output {
--   [1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3]
-- }

fun main(xs: []i32, n: i32): []i32 =
  loop (xs) = for i < n do
    concat xs xs
  in xs
