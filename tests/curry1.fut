-- Test that we can curry even "complex" arguments.
-- ==
-- input {
--   [1.0,6.0,3.0,4.0,1.0,0.0]
-- }
-- output {
--   252.000000
-- }

let f(x: (i32, f64)) (y: f64): f64 =
    let (a,b) = x in y*f64(a)+b

let g(x: [](f64,f64)) (y: f64): f64 =
    let (a,b) = unzip(x) in
    y + reduce (+) (0.0) a + reduce (+) (0.0) b

let main(a: []f64): f64 =
  let b = map (f ((5,6.0))) a
  let c = map (g (zip ([1.0,2.0,3.0]) ([4.0,5.0,6.0]))) a in
  reduce (+) (0.0) b + reduce (+) (0.0) c
