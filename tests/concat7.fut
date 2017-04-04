-- Indexing into a concat across inner dimension.  The simplifier
-- should remove the concat.
--
-- ==
-- input { [[1,1],[2,2],[3,3]] [[4],[5],[6]] 1 2 } output { 5 }
-- structure { Concat 0 }

let main(as: [][]i32, bs: [][]i32, i: i32, j: i32): i32 =
  let cs = concat@1 as bs
  in cs[i,j]
