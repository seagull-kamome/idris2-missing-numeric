||| What is true of the operations on complex numbers, proven.
|||
||| Whenever `t` follows the laws of a commutative ring (`CommRingLaws t`) the
||| complex numbers over `t` do: addition and multiplication are associative and
||| commutative, `0` and `1` are neutral, every number has an opposite, and
||| multiplication distributes over addition. Besides: the conjugate is its own
||| inverse and keeps sums and products, a number times its conjugate is the
||| square of its magnitude (a real number), and that square keeps products.
|||
||| The equalities are `===`: two complex numbers are equal when their parts are.
||| (`Data.Rational.Laws` is the one for rationals, which need a weaker equality.)
|||
||| Copyright 2021-2026 HATTORI, Hiroki
||| This file is released under the MIT license, see LICENSE for more detail.
|||
module Data.Complex.Laws

import Data.Complex
import public Data.Ring.Laws

%default total

||| Two complex numbers are equal when their parts are.
export
complexExt : {x, y : Complex t} -> x.real === y.real -> x.imag === y.imag -> x === y
complexExt {x = MkComplex a b} {y = MkComplex c d} p q = cong2 MkComplex p q

-- --------------------------------------------------------------------------
-- Rearrangements of four terms

-- (a - b) - (c + d) = (a - c) - (d + b)
subSum : CommRingLaws t => (a, b, c, d : t) -> (a - b) - (c + d) === (a - c) - (d + b)
subSum a b c d =
  trans (subIsAddNeg (a - b) (c + d))
   (trans (cong2 (+) (subIsAddNeg a b) (negAdd c d))
    (trans (addAssoc a (negate b) (negate c + negate d))
     (trans (cong (a +) (addSwap (negate b) (negate c) (negate d)))
      (trans (cong (a +) (cong (negate c +) (addComm (negate b) (negate d))))
       (trans (sym (addAssoc a (negate c) (negate d + negate b)))
        (trans (cong2 (+) (sym (subIsAddNeg a c)) (sym (negAdd d b)))
               (sym (subIsAddNeg (a - c) (d + b)))))))))

-- (a - b) + (c + d) = (a + c) + (d - b)
subSumPlus : CommRingLaws t => (a, b, c, d : t) -> (a - b) + (c + d) === (a + c) + (d - b)
subSumPlus a b c d =
  trans (cong (+ (c + d)) (subIsAddNeg a b))
   (trans (addAssoc a (negate b) (c + d))
    (trans (cong (a +) (addSwap (negate b) c d))
     (trans (cong (a +) (cong (c +) (addComm (negate b) d)))
      (trans (sym (addAssoc a c (d + negate b)))
             (cong ((a + c) +) (sym (subIsAddNeg d b)))))))

-- (a + b) - (c + d) = (a - c) + (b - d)
subInterchange : CommRingLaws t => (a, b, c, d : t) -> (a + b) - (c + d) === (a - c) + (b - d)
subInterchange a b c d =
  trans (subIsAddNeg (a + b) (c + d))
   (trans (cong ((a + b) +) (negAdd c d))
    (trans (addInterchange a b (negate c) (negate d))
           (cong2 (+) (sym (subIsAddNeg a c)) (sym (subIsAddNeg b d)))))

-- (a - b) * c = a * c - b * c
mulSubR : CommRingLaws t => (a, b, c : t) -> (a - b) * c === a * c - b * c
mulSubR a b c =
  trans (mulComm (a - b) c)
   (trans (mulSub c a b)
    (cong2 (-) (mulComm c a) (mulComm c b)))

-- --------------------------------------------------------------------------
-- Addition

export
complexAddCommutative : CommRingLaws t => (x, y : Complex t) -> addC x y === addC y x
complexAddCommutative x y = complexExt (addComm x.real y.real) (addComm x.imag y.imag)

export
complexAddAssociative : CommRingLaws t => (x, y, z : Complex t) -> addC (addC x y) z === addC x (addC y z)
complexAddAssociative x y z = complexExt (addAssoc x.real y.real z.real) (addAssoc x.imag y.imag z.imag)

export
complexAddZero : CommRingLaws t => (x : Complex t) -> addC x (MkComplex (fromInteger 0) (fromInteger 0)) === x
complexAddZero (MkComplex a b) = complexExt (Data.Ring.Laws.addZero a) (Data.Ring.Laws.addZero b)

export
complexAddNegate : CommRingLaws t => (x : Complex t) -> addC x (negC x) === MkComplex (fromInteger 0) (fromInteger 0)
complexAddNegate x = complexExt (Data.Ring.Laws.addNeg x.real) (Data.Ring.Laws.addNeg x.imag)

export
complexSubIsAddNegate : CommRingLaws t => (x, y : Complex t) -> subC x y === addC x (negC y)
complexSubIsAddNegate x y = complexExt (subIsAddNeg x.real y.real) (subIsAddNeg x.imag y.imag)

-- --------------------------------------------------------------------------
-- Multiplication

export
complexMulCommutative : CommRingLaws t => (x, y : Complex t) -> mulC x y === mulC y x
complexMulCommutative x y =
  complexExt (cong2 (-) (mulComm x.real y.real) (mulComm x.imag y.imag))
             (trans (cong2 (+) (mulComm x.real y.imag) (mulComm x.imag y.real))
                    (addComm (y.imag * x.real) (y.real * x.imag)))

export
complexMulOneNeutral : CommRingLaws t => (x : Complex t) -> mulC x (MkComplex (fromInteger 1) (fromInteger 0)) === x
complexMulOneNeutral x =
  complexExt (trans (cong2 (-) (Data.Ring.Laws.mulOne x.real) (mulZero x.imag))
                    (trans (subIsAddNeg x.real (fromInteger 0))
                     (trans (cong (x.real +) (negZero t))
                            (Data.Ring.Laws.addZero x.real))))
             (trans (cong2 (+) (mulZero x.real) (Data.Ring.Laws.mulOne x.imag))
                    (addZeroL x.imag))

export
complexMulZeroAnnihilates : CommRingLaws t => (x : Complex t) -> mulC x (MkComplex (fromInteger 0) (fromInteger 0)) === MkComplex (fromInteger 0) (fromInteger 0)
complexMulZeroAnnihilates x =
  complexExt (trans (cong2 (-) (mulZero x.real) (mulZero x.imag))
                    (trans (subIsAddNeg (fromInteger 0) (fromInteger 0))
                           (trans (cong (fromInteger 0 +) (negZero t)) (Data.Ring.Laws.addZero (fromInteger 0)))))
             (trans (cong2 (+) (mulZero x.real) (mulZero x.imag)) (Data.Ring.Laws.addZero (fromInteger 0)))

export
complexMulAssociative : CommRingLaws t => (x, y, z : Complex t) -> mulC (mulC x y) z === mulC x (mulC y z)
complexMulAssociative (MkComplex xr xi) (MkComplex yr yi) (MkComplex zr zi) = complexExt realPart imagPart
  where
    -- the real part: both sides are  (m1 - m2) - (m3 + m4)  and  (m1 - m3) - (m4 + m2),
    -- with m1 = xr (yr zr), m2 = xi (yi zr), m3 = xr (yi zi), m4 = xi (yr zi)
    realPart : ((xr * yr - xi * yi) * zr - (xr * yi + xi * yr) * zi)
               === (xr * (yr * zr - yi * zi) - xi * (yr * zi + yi * zr))
    realPart =
      trans (cong2 (-)
              (trans (mulSubR (xr * yr) (xi * yi) zr) (cong2 (-) (mulAssoc xr yr zr) (mulAssoc xi yi zr)))
              (trans (mulDistribR (xr * yi) (xi * yr) zi) (cong2 (+) (mulAssoc xr yi zi) (mulAssoc xi yr zi))))
       (trans (subSum (xr * (yr * zr)) (xi * (yi * zr)) (xr * (yi * zi)) (xi * (yr * zi)))
              (sym (cong2 (-) (mulSub xr (yr * zr) (yi * zi)) (mulDistrib xi (yr * zi) (yi * zr)))))

    -- the imaginary part: (m5 - m6) + (m7 + m8)  and  (m5 + m7) + (m8 - m6),
    -- with m5 = xr (yr zi), m6 = xi (yi zi), m7 = xr (yi zr), m8 = xi (yr zr)
    imagPart : ((xr * yr - xi * yi) * zi + (xr * yi + xi * yr) * zr)
               === (xr * (yr * zi + yi * zr) + xi * (yr * zr - yi * zi))
    imagPart =
      trans (cong2 (+)
              (trans (mulSubR (xr * yr) (xi * yi) zi) (cong2 (-) (mulAssoc xr yr zi) (mulAssoc xi yi zi)))
              (trans (mulDistribR (xr * yi) (xi * yr) zr) (cong2 (+) (mulAssoc xr yi zr) (mulAssoc xi yr zr))))
       (trans (subSumPlus (xr * (yr * zi)) (xi * (yi * zi)) (xr * (yi * zr)) (xi * (yr * zr)))
              (sym (cong2 (+) (mulDistrib xr (yr * zi) (yi * zr)) (mulSub xi (yr * zr) (yi * zi)))))

export
complexMulDistributes : CommRingLaws t => (x, y, z : Complex t) -> mulC x (addC y z) === addC (mulC x y) (mulC x z)
complexMulDistributes (MkComplex xr xi) (MkComplex yr yi) (MkComplex zr zi) = complexExt realPart imagPart
  where
    -- xr (yr + zr) - xi (yi + zi) = (xr yr - xi yi) + (xr zr - xi zi)
    realPart : xr * (yr + zr) - xi * (yi + zi) === (xr * yr - xi * yi) + (xr * zr - xi * zi)
    realPart = trans (cong2 (-) (mulDistrib xr yr zr) (mulDistrib xi yi zi))
                 (subInterchange (xr * yr) (xr * zr) (xi * yi) (xi * zi))
    -- xr (yi + zi) + xi (yr + zr) = (xr yi + xi yr) + (xr zi + xi zr)
    imagPart : xr * (yi + zi) + xi * (yr + zr) === (xr * yi + xi * yr) + (xr * zi + xi * zr)
    imagPart = trans (cong2 (+) (mulDistrib xr yi zi) (mulDistrib xi yr zr))
                 (addInterchange (xr * yi) (xr * zi) (xi * yr) (xi * zr))

-- --------------------------------------------------------------------------
-- The conjugate and the magnitude

export
conjugateInvolutive : CommRingLaws t => (x : Complex t) -> conjugate (conjugate x) === x
conjugateInvolutive (MkComplex a b) = complexExt Refl (negNeg b)

export
conjugateAdd : CommRingLaws t => (x, y : Complex t) -> conjugate (addC x y) === addC (conjugate x) (conjugate y)
conjugateAdd x y = complexExt Refl (negAdd x.imag y.imag)

export
conjugateMul : CommRingLaws t => (x, y : Complex t) -> conjugate (mulC x y) === mulC (conjugate x) (conjugate y)
conjugateMul (MkComplex xr xi) (MkComplex yr yi) = complexExt realPart imagPart
  where
    -- xr yr - xi yi = xr yr - (-xi)(-yi)
    realPart : xr * yr - xi * yi === xr * yr - negate xi * negate yi
    realPart = cong (xr * yr -) (sym (trans (negMul xi (negate yi)) (trans (cong negate (mulNeg xi yi)) (negNeg (xi * yi)))))
    -- -(xr yi + xi yr) = xr (-yi) + (-xi) yr
    imagPart : negate (xr * yi + xi * yr) === xr * negate yi + negate xi * yr
    imagPart = trans (negAdd (xr * yi) (xi * yr)) (sym (cong2 (+) (mulNeg xr yi) (negMul xi yr)))

||| A number times its conjugate is the square of its magnitude.
export
mulConjugate : CommRingLaws t => (x : Complex t) -> mulC x (conjugate x) === MkComplex (normSq x) (fromInteger 0)
mulConjugate (MkComplex a b) = complexExt realPart imagPart
  where
    -- a a - b (-b) = a a + b b
    realPart : a * a - b * negate b === a * a + b * b
    realPart = trans (cong (a * a -) (mulNeg b b))
                (trans (subIsAddNeg (a * a) (negate (b * b)))
                       (cong (a * a +) (negNeg (b * b))))
    -- a (-b) + b a = 0
    imagPart : a * negate b + b * a === fromInteger 0
    imagPart = trans (cong2 (+) (mulNeg a b) (mulComm b a)) (addNegL (a * b))

-- (a b) (c d) = (a c) (b d) for the multiplication of complex numbers
mulInterchangeC : CommRingLaws t => (a, b, c, d : Complex t) -> mulC (mulC a b) (mulC c d) === mulC (mulC a c) (mulC b d)
mulInterchangeC a b c d =
  trans (complexMulAssociative a b (mulC c d))
   (trans (cong (mulC a) (sym (complexMulAssociative b c d)))
    (trans (cong (\u => mulC a (mulC u d)) (complexMulCommutative b c))
     (trans (cong (mulC a) (complexMulAssociative c b d))
            (sym (complexMulAssociative a c (mulC b d))))))

||| The square of the magnitude keeps products: `|x y|^2 = |x|^2 |y|^2`.
export
normSqMul : CommRingLaws t => (x, y : Complex t) -> normSq (mulC x y) === normSq x * normSq y
normSqMul x y =
  trans (sym (cong real (mulConjugate (mulC x y))))
   (trans (cong (\u => real (mulC (mulC x y) u)) (conjugateMul x y))
    (trans (cong real (mulInterchangeC x y (conjugate x) (conjugate y)))
     (trans (cong real (cong2 mulC (mulConjugate x) (mulConjugate y)))
            realProduct)))
  where
    -- (a, 0) (b, 0) has the real part  a b - 0 0 = a b
    realProduct : real (mulC (MkComplex (normSq x) (fromInteger 0)) (MkComplex (normSq y) (fromInteger 0)))
                  === normSq x * normSq y
    realProduct =
      trans (cong (normSq x * normSq y -) (mulZero (fromInteger 0)))
       (trans (subIsAddNeg (normSq x * normSq y) (fromInteger 0))
        (trans (cong (normSq x * normSq y +) (negZero t)) (Data.Ring.Laws.addZero (normSq x * normSq y))))
