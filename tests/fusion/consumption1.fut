-- After fusion, consumes a free variable.  Fixed with copy().
--
-- ==
-- structure { Map 1 }

let main(as: [n]i32, bs: [m]bool): [m][n]i32 =
  let css = map (\(b: bool): [n]i32  ->
                  if b then iota(n) else as) bs
  let dss = map  (\(cs: *[n]i32): [n]i32  ->
                   let cs[0] = 42
                   in cs) css
  in dss
