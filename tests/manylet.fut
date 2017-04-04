-- Parser test.  'in' is optional except at the end of a chain of
-- let/loop-bindings.

let main(a: *[n]i32, x: i32): [n]i32 =
  let y = x + 2
  let z = y + 3 + x
  loop ((a,z)) = for i < n do
    let tmp = z * z
    let a[i] = tmp
    let x = [a[i]-1]
    let b = write ([i]) x a
    in (b, tmp+2)
  in a
