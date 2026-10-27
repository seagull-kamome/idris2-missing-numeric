||| Powers by repeated squaring.
|||
||| The loop takes a number of steps and multiplications of the order of the
||| logarithm of the exponent, and does not recurse deeper than the loop runs
||| (`Data.Monoid.Exponentiation.(^)` of contrib builds a view of the exponent
||| first, which is as deep as the exponent is large: on a backend with a stack
||| of fixed size an exponent of a few hundred thousand overflows it).
|||
||| Copyright 2021-2026 HATTORI, Hiroki
||| This file is released under the MIT license, see LICENSE for more detail.
|||
module Data.Pow

%default total

||| `base` to the power `e`, by `mul`, `one` being the neutral element. `mul` is
||| expected to be associative (it need not be commutative: the result is
||| `base * base * ... * base`, in that order) and `one` to be neutral for it. The
||| fuel is only there to show that the loop ends: it is `e`, which the loop
||| halves each time, so it never runs out before the exponent does.
export
powBy : (mul : a -> a -> a) -> (one : a) -> (base : a) -> (e : Nat) -> a
powBy mul one base e = go e one base (natToInteger e)
  where
    go : (fuel : Nat) -> (acc : a) -> (b : a) -> (k : Integer) -> a
    go Z acc _ _ = acc
    go (S fuel) acc b k =
      let acc' = if k `mod` 2 == 1 then mul acc b else acc
          k' = k `div` 2
      in if k' == 0 then acc' else go fuel acc' (mul b b) k'

||| `x` to the power `e`, `x * x * ... * x` with `e` factors (`1` for `0`).
export
powNum : Num a => a -> Nat -> a
powNum x e = powBy (*) (fromInteger 1) x e

export infixr 10 ^^

||| `x` to an integer power; a negative one is the reciprocal of the positive.
||| (A `Fixed` whose power rounds to zero has no reciprocal: `recip` divides by
||| zero, as it does for zero itself.)
export
(^^) : Fractional a => a -> Integer -> a
x ^^ e = if e >= 0 then powNum x (integerToNat e) else recip (powNum x (integerToNat (negate e)))
