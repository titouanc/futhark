-- More fancy use of module-level lambdas.
-- ==
-- input { 9 } output { 3 }

import "futlib/math"

module type operation = {type a type b val f: a -> b}

module compose = \(F: operation) ->
                 \(G: operation with a = F.b) -> {
  type a = F.a
  type b = G.b

  let f(x: a) = G.f (F.f x)
}

module i32_to_f64: operation with a = i32 with b = f64 = {
  type a = i32
  type b = f64
  let f(x: a) = f64 x
}

module f64_to_i32: operation with a = f64 with b = i32 = {
  type a = f64
  type b = i32
  let f(x: a) = i32 x
}

module f64_sqrt: operation with a = f64 with b = f64 = {
  type a = f64
  type b = f64
  let f(x: a) =  f64.sqrt x
}

module i32_sqrt = compose (compose i32_to_f64 f64_sqrt) f64_to_i32

let main(x: i32) = i32_sqrt.f x
