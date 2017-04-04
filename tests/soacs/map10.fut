-- Test that a simple consuming map works.
-- ==
-- input {
--   [[1.0,2.0],[1.0,2.0]]
-- }
-- output {
--   [[1.000000, 2.000000], [1.000000, 2.000000]]
-- }
let main(a: *[][]f64): [][]f64 =
  map (\(r: *[]f64): *[]f64  ->
        r) a
