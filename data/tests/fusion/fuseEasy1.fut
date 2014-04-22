fun real f(real a        ) = a + 3.0
fun real g(real a        ) = a * 3.0

fun real main([real] arr) =
    let x = map(f, arr) in
    let y = map(g, x)   in
    let z = map(g, y)   in
    z[0]