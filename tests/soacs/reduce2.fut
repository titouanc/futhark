-- ==
-- input {
--   [1,2,3,4,5,6,7,8,9]
--   [1,2,3,4,5,6,7,8,9]
-- }
-- output {
--   285
-- }
let main(a: []i32, b: []i32): i32 =
    reduce (+) 0 (map (*) a b)
