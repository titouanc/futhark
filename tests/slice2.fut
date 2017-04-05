-- An index inside of a map should be turned into a slice, rather than
-- a kernel by itself.
-- ==
--
-- input { [[[[0.74242944f32, 0.1323092f32], [1.3599575e-2f32,
-- 0.42590684f32]], [[0.28189754f32, 0.71788645f32], [0.120514154f32,
-- 0.3523355f32]], [[0.97101444f32, 0.8475803f32], [0.88611674f32,
-- 0.9148224f32]], [[0.94415265f32, 0.14399022f32], [0.5325674f32,
-- 0.659268f32]]], [[[0.7296194f32, 0.6609876f32], [6.526101e-2f32,
-- 6.5751016e-2f32]], [[ 0.95010173f32, 0.14800721f32],
-- [0.94630295f32, 0.53180677f32]], [[0.50352955f32, 0.8683887f32],
-- [0.52372944f32, 0.56981534f32]], [[0.89906573f32, 0.28717548f32],
-- [0.33396137f32, 0.1774621f32]]], [[[0.38886482f32, 0.9896543f32],
-- [0.46158296f32, 0.3661f32]], [[0.3473122f32, 0.3432145f32],
-- [0.8394218f32, 0.99296236f32]], [[0.121897876f32, 9.7216845e-2f32],
-- [0.9392534f32, 0.21994972f32]], [[0.48229688f32, 0.655326f32],
-- [0.7612596f32, 0.87178886f32]]], [[[0.6982439f32, 0.3648432f32],
-- [0.2956829f32, 0.64948434f32]], [[0.9514074f32, 0.5657658f32],
-- [0.96731836f32, 0.2870463f32]], [[0.24546045f32, 0.5121502f32],
-- [2.8573096e-2f32, 0.8905163f32]], [[0.11413413f32, 0.758343f32], [
-- 6.598133e-2f32, 0.34899563f32]]]] }
-- output {
-- [[[-0.12878528f32, -0.4338454f32],
--  [-0.4932002f32, -0.28704658f32]],
-- [[-0.13519031f32, -0.16950619f32],
--  [-0.4673695f32, -0.4671245f32]],
-- [[-0.3055676f32, -5.1728487e-3f32],
--  [-0.26920852f32, -0.31695f32]],
-- [[-0.15087804f32, -0.3175784f32],
--  [-0.35215855f32, -0.17525783f32]]]
-- }
-- structure distributed { Kernel 1 }

let main(mat: [#m][#m][#b][#b]f32): [m][b][b]f32 =
  let mat_rows = map (\(mat_row: [#m][#b][#b]f32): [b][b]f32  ->
                       mat_row[0]) mat
  in map  (\(blk: *[#b][#b]f32): [b][b]f32  ->
            map (\(row0: *[#b]f32): [b]f32  ->
                  loop(row=row0) = for j < b do
                    let row[j] = (row[j] - 1.0f32) / 2.0f32
                    in  row
                  in row) blk) (
          mat_rows)
