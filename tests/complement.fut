-- Test that complement works properly.
-- ==
-- input {
--   [1, 255, 0]
-- }
-- output {
--   [-2, -256, -1]
-- }
let main(a: []i32): []i32 =
    map (~) a
