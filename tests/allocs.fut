-- Nasty program that tries to leak memory.  If we can run this
-- without leaking, then we're doing well.
-- ==
-- input { [0, 1000, 42, 1001, 50000] }
-- output { 1300103225i32 }

let main(a: [n]i32): i32 =
  loop(b = iota(10)) = for i < n do
    (let m = a[i]
     in if m < (shape b)[0]
        then b
        else map (\(j: i32): i32  ->
                   j + unsafe b[j % (shape b)[0]]) (
                 iota(m)))
  in reduce (+) 0 b
