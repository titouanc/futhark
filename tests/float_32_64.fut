-- Test that float32s and float64s can both be used in a program.
--
-- This program does not really test their semantics, but mostly that
-- the parser permits them.
--
-- ==
-- input { 3.14f64 } output { 3.0f32 }

let main(x: f64): f32 =
  f32(i32(x))
