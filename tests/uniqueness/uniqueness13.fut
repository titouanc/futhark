-- ==
-- input {
--   42
-- }
-- output {
--   [1.000000]
--   [2.000000]
-- }
let f(b_1: *[]i32): ([]f64,[]f64) =
  ([1.0],[2.0])

let main(n: i32): ([]f64, []f64) =
  let a = iota(n)
  let x = f(a) in
  x
