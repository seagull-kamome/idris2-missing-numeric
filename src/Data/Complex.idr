||| Complex number.
|||
||| A complex number over any `t` that has the operations needed: addition,
||| subtraction, multiplication for a `Num t` that is a `Neg t`, division
||| (`Fractional (Complex t)`) for a `Fractional t`. The functions that need
||| roots, angles and exponentials (`magnitude`, `phase`, `polar`, `cexp` ...) are
||| for `Complex Double`: Idris has no interface for them. `Data.Complex.Laws`
||| proves that the operations follow the laws of a commutative ring whenever `t`
||| does.
|||
||| Copyright 2021-2026 HATTORI, Hiroki
||| This file is released under the MIT license, see LICENSE for more detail.
|||
module Data.Complex

import Data.Pow
import Generics.Derive
import Derive.Eq
%language ElabReflection

-- --------------------------------------------------------------------------

public export
record Complex t where
  constructor MkComplex
  real : t
  imag : t

||| `real + imag i`.
export
Show t => Show (Complex t) where
  showPrec d x = showParens (d >= PrefixMinus) "\{show x.real} + \{show x.imag}i"

export
Functor Complex where
  map f x = MkComplex (f x.real) (f x.imag)

%runElab derive "Complex" [Generic, Meta, Derive.Eq.Eq]

-- --------------------------------------------------------------------------
-- The operations; the instances below are made of these

public export
addC : Num t => Complex t -> Complex t -> Complex t
addC x y = MkComplex (x.real + y.real) (x.imag + y.imag)

public export
negC : Neg t => Complex t -> Complex t
negC x = MkComplex (negate x.real) (negate x.imag)

public export
subC : Neg t => Complex t -> Complex t -> Complex t
subC x y = MkComplex (x.real - y.real) (x.imag - y.imag)

public export
mulC : Neg t => Complex t -> Complex t -> Complex t
mulC x y = MkComplex (x.real * y.real - x.imag * y.imag)
                     (x.real * y.imag + x.imag * y.real)

public export
conjugate : Neg t => Complex t -> Complex t
conjugate x = MkComplex x.real (negate x.imag)

||| The square of the magnitude, `real * real + imag * imag`.
public export
normSq : Num t => Complex t -> t
normSq x = x.real * x.real + x.imag * x.imag

export
(Neg t, Num t) => Num (Complex t) where
  (+) = addC
  (*) = mulC
  fromInteger x = MkComplex (fromInteger x) (fromInteger 0)

export
Neg t => Neg (Complex t) where
  negate = negC
  (-) = subC

||| The reciprocal; as for a `Fractional t` it is not defined for zero.
public export
recipC : (Neg t, Fractional t) => Complex t -> Complex t
recipC x = let n = normSq x in MkComplex (x.real / n) (negate x.imag / n)

export
(Neg t, Fractional t) => Fractional (Complex t) where
  x / y = mulC x (recipC y)
  recip = recipC

export
[additiveComplexSemigroup] (Neg t, Num t) => Semigroup (Complex t) where
  (<+>) = addC

export
[additiveComplexMonoid] (Neg t, Num t) => Monoid (Complex t) using additiveComplexSemigroup where
  neutral = MkComplex (fromInteger 0) (fromInteger 0)

-- --------------------------------------------------------------------------

||| The complex number whose imaginary part is zero.
export
fromReal : Num t => t -> Complex t
fromReal r = MkComplex r (fromInteger 0)

||| The imaginary unit.
export
i : Num t => Complex t
i = MkComplex (fromInteger 0) (fromInteger 1)

export
isReal : (Num t, Eq t) => Complex t -> Bool
isReal x = x.imag == fromInteger 0

export
isImaginary : (Num t, Eq t) => Complex t -> Bool
isImaginary x = x.real == fromInteger 0

||| Kept for the name it had.
export
isImage : (Num t, Eq t) => Complex t -> Bool
isImage = isImaginary

-- --------------------------------------------------------------------------
-- Powers

||| `x` to a power by squaring.
export
pow : (Neg t, Num t) => Complex t -> Nat -> Complex t
pow = powBy mulC (fromReal (fromInteger 1))

-- --------------------------------------------------------------------------
-- Magnitude, angle and what depends on them (Double)

-- The angle of the point (x, y), in (-pi, pi].
atan2 : Double -> Double -> Double
atan2 y x =
  if x > 0 then atan (y / x)
  else if x < 0 then (if y >= 0 then atan (y / x) + pi else atan (y / x) - pi)
  else if y > 0 then pi / 2
  else if y < 0 then negate pi / 2
  else 0

||| The distance from zero.
export
magnitude : Complex Double -> Double
magnitude x = sqrt (normSq x)

||| The angle with the real axis, in (-pi, pi]; zero for zero.
export
phase : Complex Double -> Double
phase x = atan2 x.imag x.real

||| The magnitude and the angle.
export
polar : Complex Double -> (Double, Double)
polar x = (magnitude x, phase x)

||| The number with a magnitude and an angle.
export
mkPolar : (r, theta : Double) -> Complex Double
mkPolar r theta = MkComplex (r * cos theta) (r * sin theta)

||| `cos theta + i sin theta`.
export
cis : Double -> Complex Double
cis = mkPolar 1

||| `e` to the power `x`.
export
cexp : Complex Double -> Complex Double
cexp x = mkPolar (exp x.real) x.imag

||| The principal natural logarithm, with the angle in (-pi, pi]. Not defined for
||| zero (`-infinity` for the real part).
export
clog : Complex Double -> Complex Double
clog x = MkComplex (log (magnitude x)) (phase x)

||| The principal square root, the one with a real part that is not negative.
export
csqrt : Complex Double -> Complex Double
csqrt x = mkPolar (sqrt (magnitude x)) (phase x / 2)

||| `x` to the power `y` (`exp (y * log x)`; zero to a power is `NaN`).
export
cpow : Complex Double -> Complex Double -> Complex Double
cpow x y = cexp (mulC y (clog x))

-- --------------------------------------------------------------------------
-- vim: tw=80 sw=2 expandtab :
