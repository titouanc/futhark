-- Check that shape annotations are checked when input and output shape
-- are the same
-- ==
-- error: 

fun conv(k: i32) (X: [#n]f32): [n+k+1][k]f32 =
    map (\i -> unsafe X[i:i+k]) (iota (n-k+1))

fun avg(x: [#n]f32): f32 = 
    let sum = reduce (+) 0f32 x
    in sum / f32(n)

entry main(x: []f32) = map avg (conv 3 x)

