-- At one point, usage of SOAC array arguments when mapping with an
-- operator was not registered properly.
--
-- ==
-- error:

let main(row : *[w]i32) : [w]u8 =
  let b = row -- b now aliases row
  let row[0] = 2 -- consume row
  in map u8 b -- fail, because row has been consumed
