-- A local function whose free variable has been consumed, but the
-- function is never called!
-- ==
-- input { 2 [1,2,3] } output { 2}

let main(y: i32, QUUX: *[]i32) =
  let f (x: i32) = x + QUUX[0]
  let QUUX[1] = 2
  in y
