-- Check that unique components of a return tuple do not alias each
-- other.
-- ==
-- error:

let main(n: i32): (*[]i32, *[]i32) =
  let a = iota(n) in
  (a, a)
