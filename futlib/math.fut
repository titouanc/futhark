module type numeric = {
  type t

  val +: t -> t -> t
  val -: t -> t -> t
  val *: t -> t -> t
  val /: t -> t -> t

  val from_i32: i32 -> t

  val ==: t -> t -> bool
  val <: t -> t -> bool
  val >: t -> t -> bool

  val max: t -> t -> t
  val min: t -> t -> t

  val abs: t -> t

  val sgn: t -> t
}

module type integral = {
  include numeric

  val %: t -> t -> t
  val //: t -> t -> t
  val %%: t -> t -> t
}

module type real = {
  include numeric

  val from_fraction: i32 -> i32 -> t
  val to_i32: t -> i32

  val sqrt: t -> t
  val exp: t -> t
  val cos: t -> t
  val sin: t -> t
  val asin: t -> t
  val acos: t -> t
  val atan: t -> t
  val atan2: t -> t -> t

  val log: t -> t

  val isinf: t -> bool
  val isnan: t -> bool

  val inf: t
  val nan: t

  val pi: t
  val e: t
}

module i8: (integral with t = i8) = {
  type t = i8

  let (x: i8) + (y: i8) = intrinsics.add8 x y
  let (x: i8) - (y: i8) = intrinsics.sub8 x y
  let (x: i8) * (y: i8) = intrinsics.mul8 x y
  let (x: i8) / (y: i8) = intrinsics.sdiv8 x y
  let (x: i8) % (y: i8) = intrinsics.smod8 x y
  let (x: i8) // (y: i8) = intrinsics.squot8 x y
  let (x: i8) %% (y: i8) = intrinsics.srem8 x y

  let from_i32(x: i32) = i8 x

  let (x: i8) == (y: i8) = intrinsics.eq_i8 x y
  let (x: i8) < (y: i8) = intrinsics.slt8 x y
  let (x: i8) > (y: i8) = intrinsics.slt8 y x

  let sgn (x: i8) = intrinsics.ssignum8 x
  let abs (x: i8) = intrinsics.abs8 x

  let max (x: t) (y: t) = intrinsics.smax8 x y
  let min (x: t) (y: t) = intrinsics.smin8 x y
}

module i16: (integral with t = i16) = {
  type t = i16

  let (x: i16) + (y: i16) = intrinsics.add16 x y
  let (x: i16) - (y: i16) = intrinsics.sub16 x y
  let (x: i16) * (y: i16) = intrinsics.mul16 x y
  let (x: i16) / (y: i16) = intrinsics.sdiv16 x y
  let (x: i16) % (y: i16) = intrinsics.smod16 x y
  let (x: i16) // (y: i16) = intrinsics.squot16 x y
  let (x: i16) %% (y: i16) = intrinsics.srem16 x y

  let from_i32(x: i32) = i16 x

  let (x: i16) == (y: i16) = intrinsics.eq_i16 x y
  let (x: i16) < (y: i16) = intrinsics.slt16 x y
  let (x: i16) > (y: i16) = intrinsics.slt16 y x

  let sgn (x: i16) = intrinsics.ssignum16 x
  let abs (x: i16) = intrinsics.abs16 x

  let max (x: t) (y: t) = intrinsics.smax16 x y
  let min (x: t) (y: t) = intrinsics.smin16 x y
}

module i32: (integral with t = i32) = {
  type t = i32

  let (x: i32) + (y: i32) = intrinsics.add32 x y
  let (x: i32) - (y: i32) = intrinsics.sub32 x y
  let (x: i32) * (y: i32) = intrinsics.mul32 x y
  let (x: i32) / (y: i32) = intrinsics.sdiv32 x y
  let (x: i32) % (y: i32) = intrinsics.smod32 x y
  let (x: i32) // (y: i32) = intrinsics.squot32 x y
  let (x: i32) %% (y: i32) = intrinsics.srem32 x y

  let from_i32(x: i32) = x

  let (x: i32) == (y: i32) = intrinsics.eq_i32 x y
  let (x: i32) < (y: i32) = intrinsics.slt32 x y
  let (x: i32) > (y: i32) = intrinsics.slt32 y x

  let sgn (x: i32) = intrinsics.ssignum32 x
  let abs (x: i32) = intrinsics.abs32 x

  let max (x: t) (y: t) = intrinsics.smax32 x y
  let min (x: t) (y: t) = intrinsics.smin32 x y
}

module i64: (integral with t = i64) = {
  type t = i64

  let (x: i64) + (y: i64) = intrinsics.add64 x y
  let (x: i64) - (y: i64) = intrinsics.sub64 x y
  let (x: i64) * (y: i64) = intrinsics.mul64 x y
  let (x: i64) / (y: i64) = intrinsics.sdiv64 x y
  let (x: i64) % (y: i64) = intrinsics.smod64 x y
  let (x: i64) // (y: i64) = intrinsics.squot64 x y
  let (x: i64) %% (y: i64) = intrinsics.srem64 x y

  let from_i32(x: i32) = i64 x

  let (x: i64) == (y: i64) = intrinsics.eq_i64 x y
  let (x: i64) < (y: i64) = intrinsics.slt64 x y
  let (x: i64) > (y: i64) = intrinsics.slt64 y x

  let sgn (x: i64) = intrinsics.ssignum64 x
  let abs (x: i64) = intrinsics.abs64 x

  let max (x: t) (y: t) = intrinsics.smax64 x y
  let min (x: t) (y: t) = intrinsics.smin64 x y
}

module u8: (integral with t = u8) = {
  type t = u8

  let (x: u8) + (y: u8) = u8 (intrinsics.add8 (i8 x) (i8 y))
  let (x: u8) - (y: u8) = u8 (intrinsics.sub8 (i8 x) (i8 y))
  let (x: u8) * (y: u8) = u8 (intrinsics.mul8 (i8 x) (i8 y))
  let (x: u8) / (y: u8) = u8 (intrinsics.udiv8 (i8 x) (i8 y))
  let (x: u8) % (y: u8) = u8 (intrinsics.umod8 (i8 x) (i8 y))
  let (x: u8) // (y: u8) = u8 (intrinsics.udiv8 (i8 x) (i8 y))
  let (x: u8) %% (y: u8) = u8 (intrinsics.umod8 (i8 x) (i8 y))

  let from_i32(x: i32) = u8 x

  let (x: u8) == (y: u8) = intrinsics.eq_i8 (i8 x) (i8 y)
  let (x: u8) < (y: u8) = intrinsics.ult8 (i8 x) (i8 y)
  let (x: u8) > (y: u8) = intrinsics.ult8 (i8 y) (i8 x)

  let sgn (x: u8) = u8 (intrinsics.usignum8 (i8 x))
  let abs (x: u8) = x

  let max (x: t) (y: t) = u8 (intrinsics.umax8 (i8 x) (i8 y))
  let min (x: t) (y: t) = u8 (intrinsics.umin8 (i8 x) (i8 y))
}

module u16: (integral with t = u16) = {
  type t = u16

  let (x: u16) + (y: u16) = u16 (intrinsics.add16 (i16 x) (i16 y))
  let (x: u16) - (y: u16) = u16 (intrinsics.sub16 (i16 x) (i16 y))
  let (x: u16) * (y: u16) = u16 (intrinsics.mul16 (i16 x) (i16 y))
  let (x: u16) / (y: u16) = u16 (intrinsics.udiv16 (i16 x) (i16 y))
  let (x: u16) % (y: u16) = u16 (intrinsics.umod16 (i16 x) (i16 y))
  let (x: u16) // (y: u16) = u16 (intrinsics.udiv16 (i16 x) (i16 y))
  let (x: u16) %% (y: u16) = u16 (intrinsics.umod16 (i16 x) (i16 y))

  let from_i32(x: i32) = u16 x

  let (x: u16) == (y: u16) = intrinsics.eq_i16 (i16 x) (i16 y)
  let (x: u16) < (y: u16) = intrinsics.ult16 (i16 x) (i16 y)
  let (x: u16) > (y: u16) = intrinsics.ult16 (i16 y) (i16 x)

  let sgn (x: u16) = u16 (intrinsics.usignum16 (i16 x))
  let abs (x: u16) = x

  let max (x: t) (y: t) = u16 (intrinsics.umax16 (i16 x) (i16 y))
  let min (x: t) (y: t) = u16 (intrinsics.umin16 (i16 x) (i16 y))
}

module u32: (integral with t = u32) = {
  type t = u32

  let (x: u32) + (y: u32) = u32 (intrinsics.add32 (i32 x) (i32 y))
  let (x: u32) - (y: u32) = u32 (intrinsics.sub32 (i32 x) (i32 y))
  let (x: u32) * (y: u32) = u32 (intrinsics.mul32 (i32 x) (i32 y))
  let (x: u32) / (y: u32) = u32 (intrinsics.udiv32 (i32 x) (i32 y))
  let (x: u32) % (y: u32) = u32 (intrinsics.umod32 (i32 x) (i32 y))
  let (x: u32) // (y: u32) = u32 (intrinsics.udiv32 (i32 x) (i32 y))
  let (x: u32) %% (y: u32) = u32 (intrinsics.umod32 (i32 x) (i32 y))

  let from_i32(x: i32) = u32 x

  let (x: u32) == (y: u32) = intrinsics.eq_i32 (i32 x) (i32 y)
  let (x: u32) < (y: u32) = intrinsics.ult32 (i32 x) (i32 y)
  let (x: u32) > (y: u32) = intrinsics.ult32 (i32 y) (i32 x)

  let sgn (x: u32) = u32 (intrinsics.usignum32 (i32 x))
  let abs (x: u32) = x

  let max (x: t) (y: t) = u32 (intrinsics.umax32 (i32 x) (i32 y))
  let min (x: t) (y: t) = u32 (intrinsics.umin32 (i32 x) (i32 y))
}

module u64: (integral with t = u64) = {
  type t = u64

  let (x: u64) + (y: u64) = u64 (intrinsics.add64 (i64 x) (i64 y))
  let (x: u64) - (y: u64) = u64 (intrinsics.sub64 (i64 x) (i64 y))
  let (x: u64) * (y: u64) = u64 (intrinsics.mul64 (i64 x) (i64 y))
  let (x: u64) / (y: u64) = u64 (intrinsics.udiv64 (i64 x) (i64 y))
  let (x: u64) % (y: u64) = u64 (intrinsics.umod64 (i64 x) (i64 y))
  let (x: u64) // (y: u64) = u64 (intrinsics.udiv64 (i64 x) (i64 y))
  let (x: u64) %% (y: u64) = u64 (intrinsics.umod64 (i64 x) (i64 y))

  let from_i32(x: i32) = u64 x

  let (x: u64) == (y: u64) = intrinsics.eq_i64 (i64 x) (i64 y)
  let (x: u64) < (y: u64) = intrinsics.ult64 (i64 x) (i64 y)
  let (x: u64) > (y: u64) = intrinsics.ult64 (i64 y) (i64 x)

  let sgn (x: u64) = u64 (intrinsics.usignum64 (i64 x))
  let abs (x: u64) = x

  let max (x: t) (y: t) = u64 (intrinsics.umax64 (i64 x) (i64 y))
  let min (x: t) (y: t) = u64 (intrinsics.umin64 (i64 x) (i64 y))
}

module f64: (real with t = f64) = {
  type t = f64

  let (x: f64) + (y: f64) = intrinsics.fadd64 x y
  let (x: f64) - (y: f64) = intrinsics.fsub64 x y
  let (x: f64) * (y: f64) = intrinsics.fmul64 x y
  let (x: f64) / (y: f64) = intrinsics.fdiv64 x y

  let from_i32 (x: i32) = f64 x
  let from_fraction (x: i32) (y: i32) = f64 x / f64 y
  let to_i32 (x: f64) = i32 x

  let (x: f64) == (y: f64) = intrinsics.eq_f64 x y
  let (x: f64) < (y: f64) = intrinsics.lt64 x y
  let (x: f64) > (y: f64) = intrinsics.lt64 y x

  let max (x: t) (y: t) = intrinsics.fmax64 x y
  let min (x: t) (y: t) = intrinsics.fmin64 x y

  let sgn (x: f64) = if      x < 0f64  then -1f64
                     else if x == 0f64 then  0f64
                     else                    1f64
  let abs (x: f64) = intrinsics.fabs64 x

  let sqrt (x: f64) = intrinsics.sqrt64 x

  let log (x: f64) = intrinsics.log64 x
  let exp (x: f64) = intrinsics.exp64 x
  let cos (x: f64) = intrinsics.cos64 x
  let sin (x: f64) = intrinsics.sin64 x
  let acos (x: f64) = intrinsics.acos64 x
  let asin (x: f64) = intrinsics.asin64 x
  let atan (x: f64) = intrinsics.atan64 x
  let atan2 (x: f64) (y: f64) = intrinsics.atan2_64 x y

  let isinf (x: f64) = intrinsics.isinf64 x
  let isnan (x: f64) = intrinsics.isnan64 x

  let inf = 1f64 / 0f64
  let nan = 0f64 / 0f64

  let pi = 3.1415926535897932384626433832795028841971693993751058209749445923078164062f64
  let e = 2.718281828459045235360287471352662497757247093699959574966967627724076630353f64
}

module f32: (real with t = f32) = {
  type t = f32

  let (x: f32) + (y: f32) = intrinsics.fadd32 x y
  let (x: f32) - (y: f32) = intrinsics.fsub32 x y
  let (x: f32) * (y: f32) = intrinsics.fmul32 x y
  let (x: f32) / (y: f32) = intrinsics.fdiv32 x y

  let from_i32 (x: i32) = f32 x
  let from_fraction (x: i32) (y: i32) = f32 x / f32 y
  let to_i32 (x: f32) = i32 x

  let (x: f32) == (y: f32) = intrinsics.eq_f32 x y
  let (x: f32) < (y: f32) = intrinsics.lt32 x y
  let (x: f32) > (y: f32) = intrinsics.lt32 y x

  let max (x: t) (y: t) = intrinsics.fmax32 x y
  let min (x: t) (y: t) = intrinsics.fmin32 x y

  let sgn (x: f32) = if      x < 0f32  then -1f32
                     else if x == 0f32 then  0f32
                     else                    1f32
  let abs (x: f32) = intrinsics.fabs32 x

  let sqrt (x: f32) = intrinsics.sqrt32 x

  let log (x: f32) = intrinsics.log32 x
  let exp (x: f32) = intrinsics.exp32 x
  let cos (x: f32) = intrinsics.cos32 x
  let sin (x: f32) = intrinsics.sin32 x
  let acos (x: f32) = intrinsics.acos32 x
  let asin (x: f32) = intrinsics.asin32 x
  let atan (x: f32) = intrinsics.atan32 x
  let atan2 (x: f32) (y: f32) = intrinsics.atan2_32 x y

  let isinf (x: f32) = intrinsics.isinf32 x
  let isnan (x: f32) = intrinsics.isnan32 x

  let inf = 1f32 / 0f32
  let nan = 0f32 / 0f32

  let pi = f32 f64.pi
  let e = f32 f64.pi
}
