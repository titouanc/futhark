-- ==
-- input {
--   [[1,2,3], [4,5,6], [7,8,9]]
--   [6,5,4,3,2,1]
--   1
-- }
-- output {
--   [[1,2,3], [6,5,4], [7,8,9]]
-- }
fun main(a: *[][n]i32, b: []i32, i: i32): [][]i32 =
  let (br, _) = split (n) b
  let a[i] = br in
  a
