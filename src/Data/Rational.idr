||| Rational number
|||
||| A rational is a numerator and a denominator that is not zero, and it is not
||| kept reduced: `1 %: 2` and `2 %: 4` are two representations of one number.
||| `Eq` and `Ord` compare the numbers (by cross multiplication), not the
||| representations; `Equiv` says it as a type, and `Data.Rational.Laws` proves
||| that the operations keep it and that they follow the laws of a field. `reduce`
||| gives the representation with the smallest denominator.
|||
||| Copyright 2021-2026 HATTORI, Hiroki
||| This file is released under the MIT license, see LICENSE for more detail.
|||
module Data.Rational

import Decidable.Equality
import Data.Nat
import Data.Nat.Factor
import Data.Maybe
import Data.Pow

%default total

-- --------------------------------------------------------------------------

public export
record Rational where
  constructor MkRational
  num : Integer
  den : Nat
  {auto 0 denIsNonZero : IsSucc den}


public export NonZero : Rational -> Type
NonZero x = Not (x.num=0)

||| The denominator as an Integer.
public export
denom : Rational -> Integer
denom x = natToInteger x.den

||| The same number: `a/b` and `c/d` are when `a * d = c * b`.
public export
Equiv : Rational -> Rational -> Type
Equiv x y = x.num * denom y === y.num * denom x

-- --------------------------------------------------------------------------

public export
multSuccSucc:{n,m:Nat} -> IsSucc n -> IsSucc m -> IsSucc (n * m)
multSuccSucc {n=S n'} {m=S m'} _ _ = ItIsSucc


-- --------------------------------------------------------------------------

||| The representation with the smallest denominator (the numerator and the
||| denominator have no common factor).
export reduce : Rational -> Rational
reduce (MkRational num den@(S _)) =
  let (f ** MkGCD (CommonFactorExists _ _ pr0) _) = Data.Nat.Factor.gcd (fromInteger $ abs num) den in
  let (den' ** CofactorExists q pr1) = cofactor pr0 in
  case den' of
    Z impossible
    S _ => MkRational (num `div` (cast f)) den'


export infixr 9 %:, %?
export infixl 7 /?

export (%:) : (num:Integer) -> (den:Nat) -> {auto 0 _:NonZero den} -> Rational
(%:) num den = MkRational num den

namespace Integer
  export (%?) : (num:Integer) -> (den:Integer) -> Maybe Rational
  (%?) num den = if den < 0 then go (negate num) (cast $ negate den) else go num (cast den)
    where
      go : Integer -> Nat -> Maybe Rational
      go num' den' = case den' of
        Z => Nothing
        S _ => Just $ MkRational num' den'


-- --------------------------------------------------------------------------
export
Show Rational where
  showPrec d x = showParens (d >= User 9 || x.num < 0) "\{show x.num} %: \{show x.den}"

export Cast Integer Rational        where cast x = MkRational x 1
export Cast Nat Rational            where cast x = MkRational (natToInteger x) 1
export Cast Int Rational            where cast x = MkRational (cast x) 1

-- the number of decimal digits of an Integer, sign not counted
digitCount : Integer -> Nat
digitCount n = length (unpack (show (abs n)))

||| As a Double, the quotient of the two. When either has more than 300 digits
||| (a Double cannot hold it) both are first cut by the same power of ten, so the
||| quotient is not a `NaN`; the result is then rounded more than once.
export
toDouble : Rational -> Double
toDouble x =
  let k = (max (digitCount x.num) (digitCount (denom x))) `minus` 300
      p = powBy (*) 1 10 k
   in if k == 0 then cast x.num / cast (denom x)
      else cast (x.num `div` p) / cast (denom x `div` p)

export Cast Rational Double         where cast = toDouble

-- --------------------------------------------------------------------------
-- Equality and order: of the numbers

||| Whether the two are the same number, decided.
public export
equivDec : (x, y : Rational) -> Dec (Equiv x y)
equivDec x y = decEq (x.num * denom y) (y.num * denom x)

||| Same number.
public export
eqRational : Rational -> Rational -> Bool
eqRational x y = case equivDec x y of
  Yes _ => True
  No _ => False

export
Eq Rational where
  (==) = eqRational

public export compareAsReal : Rational -> Rational -> Ordering
compareAsReal (MkRational lnum lden) (MkRational rnum rden) =
  compare (lnum * natToInteger rden) (rnum * natToInteger lden)

export
Ord Rational where
  compare = compareAsReal

-- --------------------------------------------------------------------------
-- The operations; the instances below are made of these

public export
plusR : Rational -> Rational -> Rational
plusR l r = MkRational (l.num * denom r + r.num * denom l)
                       (l.den * r.den)
                       {denIsNonZero=multSuccSucc l.denIsNonZero r.denIsNonZero}

public export
minusR : Rational -> Rational -> Rational
minusR l r = MkRational (l.num * denom r - r.num * denom l)
                        (l.den * r.den)
                        {denIsNonZero=multSuccSucc l.denIsNonZero r.denIsNonZero}

public export
multR : Rational -> Rational -> Rational
multR l r = MkRational (l.num * r.num) (l.den * r.den)
                       {denIsNonZero=multSuccSucc l.denIsNonZero r.denIsNonZero}

public export
negateR : Rational -> Rational
negateR x = MkRational (negate x.num) x.den {denIsNonZero = x.denIsNonZero}

public export
absR : Rational -> Rational
absR x = MkRational (abs x.num) x.den {denIsNonZero = x.denIsNonZero}

export
Num Rational where
  (+) = plusR
  (*) = multR
  fromInteger x = MkRational x 1

export
Neg Rational where
  negate = negateR
  (-) = minusR

public export
Abs Rational where
  abs = absR

||| -1, 0 or 1 as the number is negative, zero or positive.
export
signum : Rational -> Integer
signum x = if x.num < 0 then -1 else if x.num > 0 then 1 else 0

-- --------------------------------------------------------------------------
namespace SimpleOpr
  namespace Nat
    public export %inline mult : Rational -> Nat -> Rational
    mult (MkRational num den)  n = MkRational (num * cast n) den

    public export %inline div : Rational -> (n:Nat) -> {auto 0 nIsNonZero:NonZero n} -> Rational
    div (MkRational num den {denIsNonZero}) n =
      let 0 prf : NonZero (den * n) = multSuccSucc denIsNonZero nIsNonZero
       in MkRational num (den * n)


  namespace Integer
    public export %inline mult : Rational -> Integer -> Rational
    mult (MkRational num den) n = MkRational (num * n) den

    public export partial %inline div : Rational -> Integer -> Maybe Rational
    div x n with (the Nat $ fromInteger n)
      _ | Z = Nothing
      _ | n'@(S _) = Just $ div x n'


-- --------------------------------------------------------------------------

export
[additiveRationalSemigroup] Semigroup Rational where
  (<+>) = (+)

export
[additiveRationalMonoid]  Monoid Rational using additiveRationalSemigroup where
  neutral = MkRational 0 1

-- --------------------------------------------------------------------------
-- Division

||| `negate b` for `True`, `b` for `False`.
public export
signFlip : Bool -> Integer -> Integer
signFlip True b = negate b
signFlip False b = b

||| The numerator of the reciprocal of `a / b`: `b`, with the sign of `a`.
public export
recipNum : (a, b : Integer) -> Integer
recipNum a b = signFlip (a < 0) b

||| The reciprocal, given the denominator it will have (`integerToNat` of the
||| absolute value of the numerator): `Nothing` when that is zero.
public export
recipWith : (x : Rational) -> (n : Nat) -> Maybe Rational
recipWith x Z = Nothing
recipWith x n@(S _) = Just $ MkRational (recipNum x.num (denom x)) n

||| The reciprocal of a number; `Nothing` for zero. The sign goes to the
||| numerator.
public export
recipMaybe : Rational -> Maybe Rational
recipMaybe x = recipWith x (integerToNat (abs x.num))

||| `recipMaybe` for a number that is known not to be zero (the proof is not
||| used; it is there for the caller to have shown it).
export recip : (x:Rational) -> {auto 0 ok:Not (x.num=0)} -> Maybe Rational
recip x = recipMaybe x

||| Division; `Nothing` when the divisor is zero.
export
(/?) : Rational -> Rational -> Maybe Rational
x /? y = map (x *) (recipMaybe y)

-- --------------------------------------------------------------------------
-- Powers

||| `x` to a power by squaring (the numerator and the denominator grow with the
||| power: `reduce` the result if it is to be kept).
export
pow : Rational -> Nat -> Rational
pow = powNum

||| `x` to an integer power, the reciprocal for a negative one: `Nothing` for zero
||| to a negative power.
export
powInteger : Rational -> Integer -> Maybe Rational
powInteger x e = if e >= 0 then Just (pow x (integerToNat e)) else map (\r => pow r (integerToNat (negate e))) (recipMaybe x)

-- --------------------------------------------------------------------------
-- Whole numbers and fractions

||| The numerator of the reduced representation.
export numerator : Rational -> Integer
numerator x = (reduce x).num

||| The denominator of the reduced representation.
export denominator : Rational -> Nat
denominator x = (reduce x).den

||| Whether the number is a whole number.
export isInteger : Rational -> Bool
isInteger x = x.num `mod` denom x == 0

||| The greatest integer not above the number.
export floor : Rational -> Integer
floor x = x.num `div` (natToInteger x.den)

||| The least integer not below the number.
export ceil : Rational -> Integer
ceil x = (x.num + (natToInteger x.den) - 1) `div` (natToInteger x.den)

||| The integer part, towards zero.
export truncate : Rational -> Integer
truncate x = if x.num < 0 then negate (negate x.num `div` denom x) else x.num `div` denom x

||| The nearest integer; a number half way between two goes to the even one.
export round : Rational -> Integer
round x =
  let i = floor x
      twice = 2 * (x.num - i * denom x)    -- twice the fraction, over the denominator
   in case compare twice (denom x) of
        LT => i
        GT => i + 1
        EQ => if i `mod` 2 == 0 then i else i + 1

||| The integer part (towards zero) and the fraction, which has the sign of the
||| number and is less than one: `x = fromInteger i + f`.
export properFraction : Rational -> (Integer, Rational)
properFraction x = let i = truncate x in (i, x - cast i)

||| The fraction of `properFraction`.
export fract : Rational -> Rational
fract = snd . properFraction

-- --------------------------------------------------------------------------
-- vim: tw=80 sw=2 expandtab :
