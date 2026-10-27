||| The laws of a commutative ring for `Num t` and `Neg t`, as an interface, and
||| the rearrangements of sums and products that proofs about numbers built from
||| `t` (rationals, complex numbers) need again and again.
|||
||| A type with primitive operations (`Integer`, `Int`, `Double` ...) cannot show
||| its laws inside the language; `Data.Integer.Laws` states those of `Integer`.
||| A type whose operations are defined by Idris code can give its own proofs.
|||
||| Copyright 2021-2026 HATTORI, Hiroki
||| This file is released under the MIT license, see LICENSE for more detail.
|||
module Data.Ring.Laws

%default total

||| `Num t` and `Neg t` make a commutative ring (`fromInteger 0` and
||| `fromInteger 1` are the neutral elements).
public export
interface (Num t, Neg t) => CommRingLaws t where
  addComm : (a, b : t) -> a + b === b + a
  addAssoc : (a, b, c : t) -> (a + b) + c === a + (b + c)
  addZero : (a : t) -> a + fromInteger 0 === a
  addNeg : (a : t) -> a + negate a === fromInteger 0
  subIsAddNeg : (a, b : t) -> a - b === a + negate b
  mulComm : (a, b : t) -> a * b === b * a
  mulAssoc : (a, b, c : t) -> (a * b) * c === a * (b * c)
  mulOne : (a : t) -> a * fromInteger 1 === a
  mulDistrib : (a, b, c : t) -> a * (b + c) === a * b + a * c

-- --------------------------------------------------------------------------
-- Sums

public export 0 Zero : (t : Type) -> Num t => t
Zero t = fromInteger 0

public export 0 One : (t : Type) -> Num t => t
One t = fromInteger 1

export
addZeroL : CommRingLaws t => (a : t) -> fromInteger 0 + a === a
addZeroL a = trans (addComm (fromInteger 0) a) (addZero a)

export
addNegL : CommRingLaws t => (a : t) -> negate a + a === fromInteger 0
addNegL a = trans (addComm (negate a) a) (addNeg a)

||| `a + (b + c) = b + (a + c)`
export
addSwap : CommRingLaws t => (a, b, c : t) -> a + (b + c) === b + (a + c)
addSwap a b c =
  trans (sym (addAssoc a b c))
        (trans (cong (+ c) (addComm a b)) (addAssoc b a c))

||| `(a + b) + (c + d) = (a + c) + (b + d)`
export
addInterchange : CommRingLaws t => (a, b, c, d : t) -> (a + b) + (c + d) === (a + c) + (b + d)
addInterchange a b c d =
  trans (addAssoc a b (c + d))
   (trans (cong (a +) (addSwap b c d))
          (sym (addAssoc a c (b + d))))

export
addCancelL : CommRingLaws t => (a, b, c : t) -> a + b === a + c -> b === c
addCancelL a b c prf =
  trans (sym (addZeroL b))
   (trans (cong (+ b) (sym (addNegL a)))
    (trans (addAssoc (negate a) a b)
     (trans (cong (negate a +) prf)
      (trans (sym (addAssoc (negate a) a c))
       (trans (cong (+ c) (addNegL a)) (addZeroL c))))))

||| `negate (a + b) = negate a + negate b`
export
negAdd : CommRingLaws t => (a, b : t) -> negate (a + b) === negate a + negate b
negAdd a b =
  addCancelL (a + b) (negate (a + b)) (negate a + negate b) $
    trans (addNeg (a + b))
     (sym (trans (addInterchange a b (negate a) (negate b))
          (trans (cong2 (+) (addNeg a) (addNeg b))
           (addZero (fromInteger 0)))))

-- --------------------------------------------------------------------------
-- Products

export
mulOneL : CommRingLaws t => (a : t) -> fromInteger 1 * a === a
mulOneL a = trans (mulComm (fromInteger 1) a) (mulOne a)

export
mulDistribR : CommRingLaws t => (a, b, c : t) -> (a + b) * c === a * c + b * c
mulDistribR a b c =
  trans (mulComm (a + b) c)
   (trans (mulDistrib c a b)
    (trans (cong (+ (c * b)) (mulComm c a))
           (cong (a * c +) (mulComm c b))))

||| `a * (b * c) = b * (a * c)`
export
mulSwap : CommRingLaws t => (a, b, c : t) -> a * (b * c) === b * (a * c)
mulSwap a b c =
  trans (sym (mulAssoc a b c))
        (trans (cong (* c) (mulComm a b)) (mulAssoc b a c))

||| `(a * b) * c = (a * c) * b`
export
mulRotate : CommRingLaws t => (a, b, c : t) -> (a * b) * c === (a * c) * b
mulRotate a b c =
  trans (mulAssoc a b c) (trans (cong (a *) (mulComm b c)) (sym (mulAssoc a c b)))

||| `(a * b) * (c * d) = (a * c) * (b * d)`
export
mulInterchange : CommRingLaws t => (a, b, c, d : t) -> (a * b) * (c * d) === (a * c) * (b * d)
mulInterchange a b c d =
  trans (mulAssoc a b (c * d))
   (trans (cong (a *) (mulSwap b c d))
          (sym (mulAssoc a c (b * d))))

-- --------------------------------------------------------------------------
-- Zero and negation in products

||| `a * 0 = 0`
export
mulZero : CommRingLaws t => (a : t) -> a * fromInteger 0 === fromInteger 0
mulZero a =
  addCancelL (a * fromInteger 0) (a * fromInteger 0) (fromInteger 0) $
    trans (sym (mulDistrib a (fromInteger 0) (fromInteger 0)))
     (trans (cong (a *) (addZero (fromInteger 0)))
            (sym (addZero (a * fromInteger 0))))

export
mulZeroL : CommRingLaws t => (a : t) -> fromInteger 0 * a === fromInteger 0
mulZeroL a = trans (mulComm (fromInteger 0) a) (mulZero a)

||| `a * negate b = negate (a * b)`
export
mulNeg : CommRingLaws t => (a, b : t) -> a * negate b === negate (a * b)
mulNeg a b =
  addCancelL (a * b) (a * negate b) (negate (a * b)) $
    trans (sym (mulDistrib a b (negate b)))
     (trans (cong (a *) (addNeg b))
      (trans (mulZero a) (sym (addNeg (a * b)))))

||| `negate a * b = negate (a * b)`
export
negMul : CommRingLaws t => (a, b : t) -> negate a * b === negate (a * b)
negMul a b =
  trans (mulComm (negate a) b) (trans (mulNeg b a) (cong negate (mulComm b a)))

||| `negate (negate a) = a`
export
negNeg : CommRingLaws t => (a : t) -> negate (negate a) === a
negNeg a =
  addCancelL (negate a) (negate (negate a)) a $
    trans (addNeg (negate a)) (sym (addNegL a))

||| `a - b = a + negate b` spelled out for a product: `a * (b - c) = a * b - a * c`
export
mulSub : CommRingLaws t => (a, b, c : t) -> a * (b - c) === a * b - a * c
mulSub a b c =
  trans (cong (a *) (subIsAddNeg b c))
   (trans (mulDistrib a b (negate c))
    (trans (cong (a * b +) (mulNeg a c))
           (sym (subIsAddNeg (a * b) (a * c)))))
