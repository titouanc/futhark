-- Can we match a module with an unnamed signature?
-- ==
-- input { 5 } output { 7 }

module M: {val x: i32} = {
  val x: i32 = 2
  val y: i32 = 3
}

fun main(x: i32) = M.x + x
