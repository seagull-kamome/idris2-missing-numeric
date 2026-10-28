||| What is true of the operations on rationals, proven.
|||
||| A rational has many representations (`1 %: 2`, `2 %: 4` ...), so the laws are
||| about `Equiv`, the relation "is the same number", not about `===`:
|||
||| * `Equiv` is an equivalence (`equivRefl`, `equivSym`, `equivTrans`) and is what
|||   `==` decides (`eqRationalSound`, `eqRationalComplete`);
||| * `+`, `*`, `negate` and `-` keep it (`plusRespects` ...), so a number may be
|||   replaced by another representation of itself in any expression;
||| * the rationals follow the laws of a field up to it: addition and
|||   multiplication are associative and commutative, 0 and 1 are neutral, every
|||   number has an opposite, a non-zero one has a reciprocal (`recipExists`) that
|||   is an inverse (`recipInverse`), and multiplication distributes over addition.
|||   (That the reciprocal keeps `Equiv` is not proven.)
|||
||| The proofs rest on the laws of `Integer` (`Data.Integer.Laws`), which are
||| stated there once, and on nothing else.
|||
||| Copyright 2021-2026 HATTORI, Hiroki
||| This file is released under the MIT license, see LICENSE for more detail.
|||
module Data.Rational.Laws

import Data.Nat
import Data.Rational
import Data.Integer.Laws

%default total

-- --------------------------------------------------------------------------
-- Equiv is an equivalence

export
equivRefl : (x : Rational) -> Equiv x x
equivRefl x = Refl

export
equivSym : {x, y : Rational} -> Equiv x y -> Equiv y x
equivSym p = sym p

||| The denominator of a rational is not zero (as an Integer).
export
denomNonZero : (x : Rational) -> Not (denom x === 0)
denomNonZero (MkRational num (S k)) = natToIntegerSucc k

export
equivTrans : {x, y, z : Rational} -> Equiv x y -> Equiv y z -> Equiv x z
equivTrans {x} {y} {z} p q =
  mulCancelR (x.num * denom z) (z.num * denom x) (denom y) (denomNonZero y) $
    -- (a f) d = (a d) f = (c b) f = (c f) b = (e d) b = (e b) d
    trans (mulRotate x.num (denom z) (denom y))
     (trans (cong (* denom z) p)
      (trans (mulRotate y.num (denom x) (denom z))
       (trans (cong (* denom x) q)
              (mulRotate z.num (denom y) (denom x)))))

||| Two representations whose numerators and denominators are equal are the same
||| number.
export
equivCongruent : (x, y : Rational) -> x.num === y.num -> x.den === y.den -> Equiv x y
equivCongruent x y pn pd =
  rewrite pn in
  rewrite pd in
  Refl

-- --------------------------------------------------------------------------
-- What == decides

export
eqRationalSound : {x, y : Rational} -> eqRational x y === True -> Equiv x y
eqRationalSound {x} {y} prf with (equivDec x y)
  eqRationalSound prf | Yes p = p
  eqRationalSound prf | No _ = absurd (the (False === True) prf)

export
eqRationalComplete : {x, y : Rational} -> Equiv x y -> eqRational x y === True
eqRationalComplete {x} {y} p with (equivDec x y)
  eqRationalComplete p | Yes _ = Refl
  eqRationalComplete p | No contra = absurd (contra p)

-- --------------------------------------------------------------------------
-- The operations keep Equiv

-- the denominator of a product or sum, as an Integer
denomMul : (x, y : Rational) -> denom (multR x y) === denom x * denom y
denomMul x y = natToIntegerMul x.den y.den

denomPlus : (x, y : Rational) -> denom (plusR x y) === denom x * denom y
denomPlus x y = natToIntegerMul x.den y.den

export
negateRespects : {x, x' : Rational} -> Equiv x x' -> Equiv (negateR x) (negateR x')
negateRespects {x} {x'} p =
  trans (negMul x.num (denom x'))
   (trans (cong negate p) (sym (negMul x'.num (denom x))))

export
multRespects : {x, x', y, y' : Rational} -> Equiv x x' -> Equiv y y' -> Equiv (multR x y) (multR x' y')
multRespects {x} {x'} {y} {y'} p q =
  -- (a c) (b' d') = (a b') (c d') = (a' b) (c' d) = (a' c') (b d)
  trans (cong ((x.num * y.num) *) (denomMul x' y'))
   (trans (mulInterchange x.num y.num (denom x') (denom y'))
    (trans (cong2 (*) p q)
     (trans (sym (mulInterchange x'.num y'.num (denom x) (denom y)))
            (cong ((x'.num * y'.num) *) (sym (denomMul x y))))))

-- (a d + c b) (b' d') = (a' d' + c' b') (b d), given a b' = a' b and c d' = c' d
plusCore : (a, b, c, d, a', b', c', d' : Integer)
        -> a * b' === a' * b -> c * d' === c' * d
        -> (a * d + c * b) * (b' * d') === (a' * d' + c' * b') * (b * d)
plusCore a b c d a' b' c' d' p q =
  trans (mulDistribR (a * d) (c * b) (b' * d'))
   (trans (cong2 (+) e1 e2)
    (trans (cong2 (+) (cong (* (d * d')) p) (cong (* (b * b')) q))
           (sym (trans (mulDistribR (a' * d') (c' * b') (b * d)) (cong2 (+) e3 e4)))))
  where
    e1 : (a * d) * (b' * d') === (a * b') * (d * d')
    e1 = mulInterchange a d b' d'
    e2 : (c * b) * (b' * d') === (c * d') * (b * b')
    e2 = trans (cong ((c * b) *) (mulComm b' d')) (mulInterchange c b d' b')
    e3 : (a' * d') * (b * d) === (a' * b) * (d * d')
    e3 = trans (mulInterchange a' d' b d) (cong ((a' * b) *) (mulComm d' d))
    e4 : (c' * b') * (b * d) === (c' * d) * (b * b')
    e4 = trans (cong ((c' * b') *) (mulComm b d))
          (trans (mulInterchange c' b' d b) (cong ((c' * d) *) (mulComm b' b)))

export
plusRespects : {x, x', y, y' : Rational} -> Equiv x x' -> Equiv y y' -> Equiv (plusR x y) (plusR x' y')
plusRespects {x} {x'} {y} {y'} p q =
  trans (cong ((x.num * denom y + y.num * denom x) *) (denomPlus x' y'))
   (trans (plusCore x.num (denom x) y.num (denom y) x'.num (denom x') y'.num (denom y') p q)
          (cong ((x'.num * denom y' + y'.num * denom x') *) (sym (denomPlus x y))))

-- --------------------------------------------------------------------------
-- Addition

export
plusComm : (x, y : Rational) -> Equiv (plusR x y) (plusR y x)
plusComm x y =
  equivCongruent (plusR x y) (plusR y x) (addComm (x.num * denom y) (y.num * denom x)) (multCommutative x.den y.den)

-- (a d + c b) f + e (b d) = a (d f) + (c f + e d) b
plusAssocCore : (a, b, c, d, e, f : Integer)
             -> (a * d + c * b) * f + e * (b * d) === a * (d * f) + (c * f + e * d) * b
plusAssocCore a b c d e f =
  trans (cong (+ (e * (b * d))) (mulDistribR (a * d) (c * b) f))
   (trans (cong2 (+) (cong2 (+) (mulAssoc a d f) (mulRotate c b f)) (eBD))
    (trans (addAssoc (a * (d * f)) ((c * f) * b) ((e * d) * b))
           (cong (a * (d * f) +) (sym (mulDistribR (c * f) (e * d) b)))))
  where
    eBD : e * (b * d) === (e * d) * b
    eBD = trans (sym (mulAssoc e b d)) (mulRotate e b d)

export
plusAssoc : (x, y, z : Rational) -> Equiv (plusR (plusR x y) z) (plusR x (plusR y z))
plusAssoc x y z = equivCongruent (plusR (plusR x y) z) (plusR x (plusR y z)) numEq (sym (multAssociative x.den y.den z.den))
  where
    numEq : (plusR (plusR x y) z).num === (plusR x (plusR y z)).num
    numEq =
      trans (cong ((x.num * denom y + y.num * denom x) * denom z +)
                  (cong (z.num *) (natToIntegerMul x.den y.den)))
       (trans (plusAssocCore x.num (denom x) y.num (denom y) z.num (denom z))
              (cong (\k => x.num * k + (y.num * denom z + z.num * denom y) * denom x)
                    (sym (natToIntegerMul y.den z.den))))

export
plusZero : (x : Rational) -> Equiv (plusR x (MkRational 0 1)) x
plusZero x =
  equivCongruent (plusR x (MkRational 0 1)) x (trans (cong2 (+) (mulOne x.num) (mulZeroL (denom x))) (addZero x.num))
                 (multOneRightNeutral x.den)

export
plusNegate : (x : Rational) -> Equiv (plusR x (negateR x)) (MkRational 0 1)
plusNegate x =
  trans (cong (* 1) numZero)
   (trans (mulZeroL 1) (sym (mulZeroL (denom (plusR x (negateR x))))))
  where
    -- a b + (-a) b = (a + -a) b = 0 b = 0
    numZero : x.num * denom x + negate x.num * denom x === 0
    numZero = trans (sym (mulDistribR x.num (negate x.num) (denom x)))
               (trans (cong (* denom x) (addNeg x.num)) (mulZeroL (denom x)))

||| `x - y` is `x + negate y`.
export
minusIsPlusNegate : (x, y : Rational) -> Equiv (minusR x y) (plusR x (negateR y))
minusIsPlusNegate x y =
  equivCongruent (minusR x y) (plusR x (negateR y)) (trans (subIsAddNeg (x.num * denom y) (y.num * denom x))
                        (cong (x.num * denom y +) (sym (negMul y.num (denom x)))))
                 Refl

-- --------------------------------------------------------------------------
-- Multiplication

export
multComm : (x, y : Rational) -> Equiv (multR x y) (multR y x)
multComm x y = equivCongruent (multR x y) (multR y x) (mulComm x.num y.num) (multCommutative x.den y.den)

export
multAssoc : (x, y, z : Rational) -> Equiv (multR (multR x y) z) (multR x (multR y z))
multAssoc x y z = equivCongruent (multR (multR x y) z) (multR x (multR y z)) (mulAssoc x.num y.num z.num) (sym (multAssociative x.den y.den z.den))

export
multOne : (x : Rational) -> Equiv (multR x (MkRational 1 1)) x
multOne x = equivCongruent (multR x (MkRational 1 1)) x (mulOne x.num) (multOneRightNeutral x.den)

export
multZero : (x : Rational) -> Equiv (multR x (MkRational 0 1)) (MkRational 0 1)
multZero x =
  trans (cong (* 1) (mulZero x.num)) (trans (mulZeroL 1) (sym (mulZeroL (denom (multR x (MkRational 0 1))))))

-- (a s) ((b d) (b f)) = ((a c) (b f) + (a e) (b d)) (b (d f)), where s = c f + e d
distribCore : (a, b, c, d, e, f : Integer)
           -> (a * (c * f + e * d)) * ((b * d) * (b * f))
              === ((a * c) * (b * f) + (a * e) * (b * d)) * (b * (d * f))
distribCore a b c d e f =
  trans (cong ((a * s) *) dc)
   (trans (sym (mulAssoc (a * s) b (b * (d * f))))
    (trans (cong (* (b * (d * f))) (mulRotate a s b))
           (cong (* (b * (d * f))) (sym t))))
  where
    s : Integer
    s = c * f + e * d
    -- (b d) (b f) = b (b (d f))
    dc : (b * d) * (b * f) === b * (b * (d * f))
    dc = trans (mulAssoc b d (b * f)) (cong (b *) (mulSwap d b f))
    -- (a c) (b f) + (a e) (b d) = (a b) s
    t : (a * c) * (b * f) + (a * e) * (b * d) === (a * b) * (c * f + e * d)
    t = trans (cong2 (+) (mulInterchange a c b f) (mulInterchange a e b d))
         (sym (mulDistrib (a * b) (c * f) (e * d)))

||| Multiplication distributes over addition.
export
multDistributes : (x, y, z : Rational) -> Equiv (multR x (plusR y z)) (plusR (multR x y) (multR x z))
multDistributes x y z =
  trans (cong ((x.num * (y.num * denom z + z.num * denom y)) *) dR)
   (trans (distribCore x.num (denom x) y.num (denom y) z.num (denom z))
          (cong2 (*) (cong2 (+) (cong ((x.num * y.num) *) (sym dXZ)) (cong ((x.num * z.num) *) (sym dXY)))
                     (sym dL)))
  where
    dXY : denom (multR x y) === denom x * denom y
    dXY = natToIntegerMul x.den y.den
    dXZ : denom (multR x z) === denom x * denom z
    dXZ = natToIntegerMul x.den z.den
    dYZ : denom (plusR y z) === denom y * denom z
    dYZ = natToIntegerMul y.den z.den
    -- the denominators of the two sides
    dL : denom (multR x (plusR y z)) === denom x * (denom y * denom z)
    dL = trans (natToIntegerMul x.den (y.den * z.den)) (cong (denom x *) dYZ)
    dR : denom (plusR (multR x y) (multR x z)) === (denom x * denom y) * (denom x * denom z)
    dR = trans (natToIntegerMul (x.den * y.den) (x.den * z.den))
               (cong2 (*) dXY dXZ)

-- --------------------------------------------------------------------------
-- Reciprocal

-- (a * -b) * 1 = 1 * (b * s) when s = -a
recipCoreNeg : (a, b, s : Integer) -> s === negate a -> (a * negate b) * 1 === 1 * (b * s)
recipCoreNeg a b s ps =
  trans (mulOne (a * negate b))
   (trans (mulNeg a b)
    (sym (trans (mulOneL (b * s))
         (trans (cong (b *) ps)
          (trans (mulNeg b a) (cong negate (mulComm b a)))))))

-- (a * b) * 1 = 1 * (b * s) when s = a
recipCorePos : (a, b, s : Integer) -> s === a -> (a * b) * 1 === 1 * (b * s)
recipCorePos a b s ps =
  trans (mulOne (a * b))
   (trans (mulComm a b) (sym (trans (mulOneL (b * s)) (cong (b *) ps))))

-- the two signs of the numerator, given the test as a Bool
recipCore : (a, b, s : Integer) -> (t : Bool) -> (a < 0) === t -> s === abs a
         -> (a * signFlip t b) * 1 === 1 * (b * s)
recipCore a b s True lt ps = recipCoreNeg a b s (trans ps (absNegative a lt))
recipCore a b s False lt ps = recipCorePos a b s (trans ps (absNonNegative a lt))

recipNumCore : (a, b, s : Integer) -> s === abs a -> (a * recipNum a b) * 1 === 1 * (b * s)
recipNumCore a b s ps = recipCore a b s (a < 0) Refl ps

||| A number times its reciprocal is one.
export
recipInverse : (x, r : Rational) -> recipMaybe x === Just r -> Equiv (multR x r) (MkRational 1 1)
recipInverse x r prf with (integerToNat (abs x.num)) proof eq
  recipInverse x r prf | Z = absurd (the (Nothing {ty = Rational} === Just r) prf)
  recipInverse x r prf | (S k) =
    case justEq prf of
      Refl =>
        let sIsAbs : natToInteger (S k) === abs x.num
            sIsAbs = trans (cong natToInteger (sym eq)) (natToIntegerToNatAbs x.num)
         in trans (recipNumCore x.num (denom x) (natToInteger (S k)) sIsAbs)
                  (cong (1 *) (sym (natToIntegerMul x.den (S k))))
  where
    justEq : Just a === Just b -> a === b
    justEq Refl = Refl

||| A number that is not zero has a reciprocal (and `recipInverse` says that it is
||| one).
export
recipExists : (x : Rational) -> Not (x.num === 0) -> (r : Rational ** recipMaybe x === Just r)
recipExists x nz =
  case absNatSucc x.num nz of
    (k ** eq) => (MkRational (recipNum x.num (denom x)) (S k) ** cong (recipWith x) eq)

||| Subtraction keeps Equiv.
export
minusRespects : {x, x', y, y' : Rational} -> Equiv x x' -> Equiv y y' -> Equiv (minusR x y) (minusR x' y')
minusRespects {x} {x'} {y} {y'} p q =
  equivTrans {x = minusR x y} {y = plusR x (negateR y)} {z = minusR x' y'}
    (minusIsPlusNegate x y)
    (equivTrans {x = plusR x (negateR y)} {y = plusR x' (negateR y')} {z = minusR x' y'}
      (plusRespects {x} {x'} {y = negateR y} {y' = negateR y'} p (negateRespects {x = y} {x' = y'} q))
      (equivSym {x = minusR x' y'} {y = plusR x' (negateR y')} (minusIsPlusNegate x' y')))
