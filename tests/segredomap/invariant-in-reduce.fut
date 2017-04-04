-- This example explores what happens when we use an invariant variable in the
-- reduction operator of a segmented reduction.
--
-- Currently this is not turned into a segmented reduction

let add_if_smaller (const : i32) (acc : i32) (x : i32) : i32 =
  if x < const
  then acc + x
  else acc

let main (xss : [m][n]i32, consts : [m]i32): [m]i32 =
--  let xss = map (\xs -> map (2*) xs) xss in
  map (\c xs -> reduce (add_if_smaller c) 0 xs) consts xss
