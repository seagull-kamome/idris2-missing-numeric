||| The laws of `Integer`, a commutative ring with cancellation.
|||
||| The operations of `Integer` are primitive: their definitions are not in the
||| language, so these laws cannot be proven in it. They are stated here, once,
||| and taken as true by `believe_me` (the way `Data.Int.Order` of contrib treats
||| `Int`); each is a plain fact about integers, and `test/Main.idr` checks all of
||| them on a range of values. Everything else in this package that is proven
||| rests on these and on nothing unsafe.
|||
||| Copyright 2021-2026 HATTORI, Hiroki
||| This file is released under the MIT license, see LICENSE for more detail.
|||
module Data.Integer.Laws

import Data.Nat
import public Data.Ring.Laws

%default total

-- The one place a law is believed: two things that are equal.
unsafeEq : {0 a, b : t} -> a === b
unsafeEq = believe_me (the (Int === Int) Refl)

export
CommRingLaws Integer where
  addComm _ _ = unsafeEq
  addAssoc _ _ _ = unsafeEq
  addZero _ = unsafeEq
  addNeg _ = unsafeEq
  subIsAddNeg _ _ = unsafeEq
  mulComm _ _ = unsafeEq
  mulAssoc _ _ _ = unsafeEq
  mulOne _ = unsafeEq
  mulDistrib _ _ _ = unsafeEq

||| Cancelling a factor that is not zero: `integral domain`.
export
mulCancelR : (a, b, c : Integer) -> Not (c === 0) -> a * c === b * c -> a === b
mulCancelR _ _ _ _ _ = unsafeEq

||| `natToInteger` keeps products.
export
natToIntegerMul : (m, n : Nat) -> natToInteger (m * n) === natToInteger m * natToInteger n
natToIntegerMul _ _ = unsafeEq

||| `natToInteger` of a successor is not zero.
export
natToIntegerSucc : (n : Nat) -> Not (natToInteger (S n) === 0)
natToIntegerSucc _ _ = believe_me ()

||| Going to a `Nat` and back keeps the absolute value.
export
natToIntegerToNatAbs : (a : Integer) -> natToInteger (integerToNat (abs a)) === abs a
natToIntegerToNatAbs _ = unsafeEq

||| The absolute value of a number that is not negative.
export
absNonNegative : (a : Integer) -> (a < 0) === False -> abs a === a
absNonNegative _ _ = unsafeEq

||| The absolute value of a negative number.
export
absNegative : (a : Integer) -> (a < 0) === True -> abs a === negate a
absNegative _ _ = unsafeEq
