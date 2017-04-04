-- Slicing a multidimensional array across the outer dimension.
--
-- ==
-- input { [[1,2,3],[4,5,6]] 1 3 }
-- output { [[2,3],[5,6]] }
-- input { [[1,2,3],[4,5,6]] 0 3 }
-- output { [[1,2,3],[4,5,6]] }
-- input { [[1,2,3],[4,5,6]] 1 1 }
-- output { empty([]i32) }
-- input { [[1,2,3],[4,5,6]] 1 0 }
-- error: Assertion.*failed

let main(as: [n][m]i32, i: i32, j: i32): [n][]i32 =
  as[0:n,i:j]
