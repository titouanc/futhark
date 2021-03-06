-- Tests that the code generator does not choke on terrible names that
-- are not valid in C.
--
-- ==
-- input { false 2 }
-- output { 12 }

fun f(r: bool, x: i32): i32 = x+1 + if r then f(r,x) else 0
fun f'(r: bool, x: i32): i32 = x+2 + if r then f'(r,x) else 0
fun f_(r: bool, x: i32): i32 = x+3 + if r then f_(r,x) else 0

fun main(r: bool, x: i32): i32 =
  let x'_ = x + 1
  let x'' = x'_ + x'_ in
  f_(r, f'(r, f(r, x'')))
