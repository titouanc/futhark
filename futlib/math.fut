module type numeric = {
  type t

  val +: t -> t -> t
  val -: t -> t -> t
  val *: t -> t -> t
  val /: t -> t -> t

  val fromInt: i32 -> t

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
}

module type real = {
  include numeric

  val fromFraction: i32 -> i32 -> t
  val toInt: t -> i32

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

  fun (x: i8) + (y: i8) = x intrinsics.+ y
  fun (x: i8) - (y: i8) = x intrinsics.- y
  fun (x: i8) * (y: i8) = x intrinsics.* y
  fun (x: i8) / (y: i8) = x intrinsics./ y
  fun (x: i8) % (y: i8) = x intrinsics.% y

  fun fromInt(x: i32) = i8 x

  fun (x: i8) == (y: i8) = x intrinsics.== y
  fun (x: i8) < (y: i8) = x intrinsics.< y
  fun (x: i8) > (y: i8) = x intrinsics.> y

  fun sgn (x: i8) = intrinsics.sgn x
  fun abs (x: i8) = intrinsics.abs x

  fun max (x: t) (y: t) = if x < y then y else x
  fun min (x: t) (y: t) = if x < y then x else y
}

module i16: (integral with t = i16) = {
  type t = i16

  fun (x: i16) + (y: i16) = x intrinsics.+ y
  fun (x: i16) - (y: i16) = x intrinsics.- y
  fun (x: i16) * (y: i16) = x intrinsics.* y
  fun (x: i16) / (y: i16) = x intrinsics./ y
  fun (x: i16) % (y: i16) = x intrinsics.% y

  fun fromInt(x: i32) = i16 x

  fun (x: i16) == (y: i16) = x intrinsics.== y
  fun (x: i16) < (y: i16) = x intrinsics.< y
  fun (x: i16) > (y: i16) = x intrinsics.> y

  fun sgn (x: i16) = intrinsics.sgn x
  fun abs (x: i16) = intrinsics.abs x

  fun max (x: t) (y: t) = if x < y then y else x
  fun min (x: t) (y: t) = if x < y then x else y
}

module i32: (integral with t = i32) = {
  type t = i32

  fun (x: i32) + (y: i32) = x intrinsics.+ y
  fun (x: i32) - (y: i32) = x intrinsics.- y
  fun (x: i32) * (y: i32) = x intrinsics.* y
  fun (x: i32) / (y: i32) = x intrinsics./ y
  fun (x: i32) % (y: i32) = x intrinsics.% y

  fun fromInt(x: i32) = x

  fun (x: i32) == (y: i32) = x intrinsics.== y
  fun (x: i32) < (y: i32) = x intrinsics.< y
  fun (x: i32) > (y: i32) = x intrinsics.> y

  fun sgn (x: i32) = intrinsics.sgn x
  fun abs (x: i32) = intrinsics.abs x

  fun max (x: t) (y: t) = if x < y then y else x
  fun min (x: t) (y: t) = if x < y then x else y
}

module i64: (integral with t = i64) = {
  type t = i64

  fun (x: i64) + (y: i64) = x intrinsics.+ y
  fun (x: i64) - (y: i64) = x intrinsics.- y
  fun (x: i64) * (y: i64) = x intrinsics.* y
  fun (x: i64) / (y: i64) = x intrinsics./ y
  fun (x: i64) % (y: i64) = x intrinsics.% y

  fun fromInt(x: i32) = i64 x

  fun (x: i64) == (y: i64) = x intrinsics.== y
  fun (x: i64) < (y: i64) = x intrinsics.< y
  fun (x: i64) > (y: i64) = x intrinsics.> y

  fun sgn (x: i64) = intrinsics.sgn x
  fun abs (x: i64) = intrinsics.abs x

  fun max (x: t) (y: t) = if x < y then y else x
  fun min (x: t) (y: t) = if x < y then x else y
}

module u8: (integral with t = u8) = {
  type t = u8

  fun (x: u8) + (y: u8) = x intrinsics.+ y
  fun (x: u8) - (y: u8) = x intrinsics.- y
  fun (x: u8) * (y: u8) = x intrinsics.* y
  fun (x: u8) / (y: u8) = x intrinsics./ y
  fun (x: u8) % (y: u8) = x intrinsics.% y

  fun fromInt(x: i32) = u8 x

  fun (x: u8) == (y: u8) = x intrinsics.== y
  fun (x: u8) < (y: u8) = x intrinsics.< y
  fun (x: u8) > (y: u8) = x intrinsics.> y

  fun sgn (x: u8) = intrinsics.sgn x
  fun abs (x: u8) = intrinsics.abs x

  fun max (x: t) (y: t) = if x < y then y else x
  fun min (x: t) (y: t) = if x < y then x else y
}

module u16: (integral with t = u16) = {
  type t = u16

  fun (x: u16) + (y: u16) = x intrinsics.+ y
  fun (x: u16) - (y: u16) = x intrinsics.- y
  fun (x: u16) * (y: u16) = x intrinsics.* y
  fun (x: u16) / (y: u16) = x intrinsics./ y
  fun (x: u16) % (y: u16) = x intrinsics.% y

  fun fromInt(x: i32) = u16 x

  fun (x: u16) == (y: u16) = x intrinsics.== y
  fun (x: u16) < (y: u16) = x intrinsics.< y
  fun (x: u16) > (y: u16) = x intrinsics.> y

  fun sgn (x: u16) = intrinsics.sgn x
  fun abs (x: u16) = intrinsics.abs x

  fun max (x: t) (y: t) = if x < y then y else x
  fun min (x: t) (y: t) = if x < y then x else y
}

module u32: (integral with t = u32) = {
  type t = u32

  fun (x: u32) + (y: u32) = x intrinsics.+ y
  fun (x: u32) - (y: u32) = x intrinsics.- y
  fun (x: u32) * (y: u32) = x intrinsics.* y
  fun (x: u32) / (y: u32) = x intrinsics./ y
  fun (x: u32) % (y: u32) = x intrinsics.% y

  fun fromInt(x: i32) = u32 x

  fun (x: u32) == (y: u32) = x intrinsics.== y
  fun (x: u32) < (y: u32) = x intrinsics.< y
  fun (x: u32) > (y: u32) = x intrinsics.> y

  fun sgn (x: u32) = intrinsics.sgn x
  fun abs (x: u32) = intrinsics.abs x

  fun max (x: t) (y: t) = if x < y then y else x
  fun min (x: t) (y: t) = if x < y then x else y
}

module u64: (integral with t = u64) = {
  type t = u64

  fun (x: u64) + (y: u64) = x intrinsics.+ y
  fun (x: u64) - (y: u64) = x intrinsics.- y
  fun (x: u64) * (y: u64) = x intrinsics.* y
  fun (x: u64) / (y: u64) = x intrinsics./ y
  fun (x: u64) % (y: u64) = x intrinsics.% y

  fun fromInt(x: i32) = u64 x

  fun (x: u64) == (y: u64) = x intrinsics.== y
  fun (x: u64) < (y: u64) = x intrinsics.< y
  fun (x: u64) > (y: u64) = x intrinsics.> y

  fun sgn (x: u64) = intrinsics.sgn x
  fun abs (x: u64) = intrinsics.abs x

  fun max (x: t) (y: t) = if x < y then y else x
  fun min (x: t) (y: t) = if x < y then x else y
}

module f64: (real with t = f64) = {
  type t = f64

  fun (x: f64) + (y: f64) = x intrinsics.+ y
  fun (x: f64) - (y: f64) = x intrinsics.- y
  fun (x: f64) * (y: f64) = x intrinsics.* y
  fun (x: f64) / (y: f64) = x intrinsics./ y

  fun fromInt (x: i32) = f64 x
  fun fromFraction (x: i32) (y: i32) = f64 x intrinsics./ f64 y
  fun toInt (x: f64) = i32 x

  fun (x: f64) == (y: f64) = x intrinsics.== y
  fun (x: f64) <  (y: f64) = x intrinsics.< y
  fun (x: f64) >  (y: f64) = x intrinsics.> y

  fun max (x: t) (y: t) = if x < y then y else x
  fun min (x: t) (y: t) = if x < y then x else y

  fun sgn (x: f64) = if      x intrinsics.< 0f64  then -1f64
                     else if x intrinsics.== 0f64 then  0f64
                     else                               1f64
  fun abs (x: f64) = intrinsics.abs x

  fun sqrt (x: f64) = intrinsics.sqrt64 x

  fun log (x: f64) = intrinsics.log64 x
  fun exp (x: f64) = intrinsics.exp64 x
  fun cos (x: f64) = intrinsics.cos64 x
  fun sin (x: f64) = intrinsics.sin64 x
  fun acos (x: f64) = intrinsics.acos64 x
  fun asin (x: f64) = intrinsics.asin64 x
  fun atan (x: f64) = intrinsics.atan64 x
  fun atan2 (x: f64) (y: f64) = intrinsics.atan2_64 x y

  fun isinf (x: f64) = intrinsics.isinf64 x
  fun isnan (x: f64) = intrinsics.isnan64 x

  val inf = 1f64 / 0f64
  val nan = 0f64 / 0f64

  val pi = 3.1415926535897932384626433832795028841971693993751058209749445923078164062f64
  val e = 2.718281828459045235360287471352662497757247093699959574966967627724076630353f64
}

module f32: (real with t = f32) = {
  type t = f32

  fun (x: f32) + (y: f32) = x intrinsics.+ y
  fun (x: f32) - (y: f32) = x intrinsics.- y
  fun (x: f32) * (y: f32) = x intrinsics.* y
  fun (x: f32) / (y: f32) = x intrinsics./ y

  fun fromInt (x: i32) = f32 x
  fun fromFraction (x: i32) (y: i32) = f32 x intrinsics./ f32 y
  fun toInt (x: f32) = i32 x

  fun (x: f32) == (y: f32) = x intrinsics.== y
  fun (x: f32) <  (y: f32) = x intrinsics.< y
  fun (x: f32) >  (y: f32) = x intrinsics.> y

  fun max (x: t) (y: t) = if x < y then y else x
  fun min (x: t) (y: t) = if x < y then x else y

  fun sgn (x: f32) = if      x intrinsics.< 0f32  then -1f32
                     else if x intrinsics.== 0f32 then  0f32
                     else                               1f32
  fun abs (x: f32) = intrinsics.abs x

  fun sqrt (x: f32) = intrinsics.sqrt32 x

  fun log (x: f32) = intrinsics.log32 x
  fun exp (x: f32) = intrinsics.exp32 x
  fun cos (x: f32) = intrinsics.cos32 x
  fun sin (x: f32) = intrinsics.sin32 x
  fun acos (x: f32) = intrinsics.acos32 x
  fun asin (x: f32) = intrinsics.asin32 x
  fun atan (x: f32) = intrinsics.atan32 x
  fun atan2 (x: f32) (y: f32) = intrinsics.atan2_32 x y

  fun isinf (x: f32) = intrinsics.isinf32 x
  fun isnan (x: f32) = intrinsics.isnan32 x

  val inf = 1f32 / 0f32
  val nan = 0f32 / 0f32

  val pi = f32 f64.pi
  val e = f32 f64.pi

}
