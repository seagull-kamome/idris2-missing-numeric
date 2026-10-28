||| What is true of the operations on fixed point numbers, proven.
|||
||| Addition, subtraction and negation are those of the integers in the
||| numerator, and follow their laws exactly: `Fixed n` is an abelian group under
||| addition. Multiplication and division round down, so a product is not always
||| exact and `*` is neither associative nor distributive over `+` (the digits
||| that are cut off differ with the order); what is true of it is commutativity,
||| that 1 is neutral and 0 annihilates, and that `fromInteger` keeps sums and
||| products, which is proven here. `test/Main.idr` shows a case where the
||| rounding makes `*` not associative.
|||
||| Copyright 2021-2026 HATTORI, Hiroki
||| This file is released under the MIT license, see LICENSE for more detail.
|||
module Data.Fixed.Laws

import Data.Fixed
import Data.Integer.Laws

%default total

||| Two fixed point numbers are equal when their numerators are.
export
fixedExt : {x, y : Fixed n} -> x.num === y.num -> x === y
fixedExt {x = MkFixed a} {y = MkFixed b} p = cong MkFixed p

||| 10 to a power is not zero. This is believed, like the laws of `Integer` (the
||| table and the squaring of `pow10` are not followed here; the test checks it
||| for the first two hundred powers); it is the one use of `believe_me` outside
||| `Data.Integer.Laws`.
export
pow10NonZero : (n : Nat) -> Not (pow10 n === 0)
pow10NonZero _ _ = believe_me ()

-- --------------------------------------------------------------------------
-- Addition: an abelian group

export
fixedAddCommutative : (x, y : Fixed n) -> addF x y === addF y x
fixedAddCommutative x y = fixedExt (addComm x.num y.num)

export
fixedAddAssociative : (x, y, z : Fixed n) -> addF (addF x y) z === addF x (addF y z)
fixedAddAssociative x y z = fixedExt (addAssoc x.num y.num z.num)

||| `0` is `fromInteger 0`.
export
fixedAddZero : {n : Nat} -> (x : Fixed n) -> addF x (fromIntegerF 0) === x
fixedAddZero {n} x = fixedExt (trans (cong (x.num +) (mulZeroL (pow10 n))) (Data.Ring.Laws.addZero x.num))

export
fixedAddNegate : {n : Nat} -> (x : Fixed n) -> addF x (negF x) === fromIntegerF 0
fixedAddNegate {n} x = fixedExt (trans (addNeg x.num) (sym (mulZeroL (pow10 n))))

export
fixedSubIsAddNegate : (x, y : Fixed n) -> subF x y === addF x (negF y)
fixedSubIsAddNegate x y = fixedExt (subIsAddNeg x.num y.num)

export
fixedNegateInvolutive : (x : Fixed n) -> negF (negF x) === x
fixedNegateInvolutive x = fixedExt (negNeg x.num)

-- --------------------------------------------------------------------------
-- Multiplication

export
fixedMulCommutative : {n : Nat} -> (x, y : Fixed n) -> mulF x y === mulF y x
fixedMulCommutative x y = fixedExt (cong (`div` pow10 n) (mulComm x.num y.num))

||| `1` is `fromInteger 1`.
export
fixedMulOneNeutral : {n : Nat} -> (x : Fixed n) -> mulF x (fromIntegerF 1) === x
fixedMulOneNeutral {n} x =
  fixedExt (trans (cong (\u => (x.num * u) `div` pow10 n) (mulOneL (pow10 n)))
                  (divMulCancel x.num (pow10 n) (pow10NonZero n)))

||| `0` is `fromInteger 0`.
export
fixedMulZeroAnnihilates : {n : Nat} -> (x : Fixed n) -> mulF x (fromIntegerF 0) === fromIntegerF 0
fixedMulZeroAnnihilates {n} x =
  fixedExt (trans (cong (\u => (x.num * u) `div` pow10 n) (mulZeroL (pow10 n)))
           (trans (cong (`div` pow10 n) (Data.Ring.Laws.mulZero x.num))
            (trans (zeroDiv (pow10 n) (pow10NonZero n)) (sym (mulZeroL (pow10 n))))))

-- --------------------------------------------------------------------------
-- From the integers

export
fixedFromIntegerAdd : {n : Nat} -> (a, b : Integer) -> fromIntegerF (a + b) === addF (fromIntegerF {n} a) (fromIntegerF {n} b)
fixedFromIntegerAdd {n} a b = fixedExt (mulDistribR a b (pow10 n))

export
fixedFromIntegerMul : {n : Nat} -> (a, b : Integer) -> fromIntegerF (a * b) === mulF (fromIntegerF {n} a) (fromIntegerF {n} b)
fixedFromIntegerMul {n} a b =
  fixedExt (sym (trans (cong (`div` pow10 n) rearranged)
                       (divMulCancel ((a * b) * pow10 n) (pow10 n) (pow10NonZero n))))
  where
    -- (a r) (b r) = ((a b) r) r
    rearranged : (a * pow10 n) * (b * pow10 n) === ((a * b) * pow10 n) * pow10 n
    rearranged = trans (mulInterchange a (pow10 n) b (pow10 n))
                  (trans (cong ((a * b) *) (mulComm (pow10 n) (pow10 n)))
                         (sym (mulAssoc (a * b) (pow10 n) (pow10 n))))
