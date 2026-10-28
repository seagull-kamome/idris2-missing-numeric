||| Fixed point fractional number. - Ported from Haskell base.
|||
||| Copyright 2021-2023, HATTORI, Hiroki
||| This file is released under the MIT license, see LICENSE for more detail.
|||
module Data.Fixed

import Data.Nat
import Data.Maybe
import Data.String
import Data.Rational
import Generics.Derive
import Derive.Ord
import Derive.Eq

import Data.Pow

%default total
%language ElabReflection

-- --------------------------------------------------------------------------

public export
record Fixed (n:Nat) where
  constructor MkFixed
  num : Integer
%runElab derive "Fixed" [Generic, Derive.Eq.Eq, Derive.Ord.Ord, DecEq]


-- 10 to the power n as an Integer, which is what the arithmetic needs: a table
-- for the number of digits a Fixed usually has, and squaring for the rest.
-- (The operations ask for it every time they run.)
public export
pow10 : Nat -> Integer
pow10 n = case n of
  0 => 1
  1 => 10
  2 => 100
  3 => 1000
  4 => 10000
  5 => 100000
  6 => 1000000
  7 => 10000000
  8 => 100000000
  9 => 1000000000
  10 => 10000000000
  11 => 100000000000
  12 => 1000000000000
  13 => 10000000000000
  14 => 100000000000000
  15 => 1000000000000000
  16 => 10000000000000000
  17 => 100000000000000000
  18 => 1000000000000000000
  19 => 10000000000000000000
  20 => 100000000000000000000
  21 => 1000000000000000000000
  22 => 10000000000000000000000
  23 => 100000000000000000000000
  24 => 1000000000000000000000000
  25 => 10000000000000000000000000
  26 => 100000000000000000000000000
  27 => 1000000000000000000000000000
  28 => 10000000000000000000000000000
  29 => 100000000000000000000000000000
  30 => 1000000000000000000000000000000
  31 => 10000000000000000000000000000000
  32 => 100000000000000000000000000000000
  33 => 1000000000000000000000000000000000
  34 => 10000000000000000000000000000000000
  35 => 100000000000000000000000000000000000
  36 => 1000000000000000000000000000000000000
  _ => powBy (*) 1 10 n


-- 10 to the power n as a Nat, for the denominator of a Rational. It is the plain
-- definition so that it can be shown not to be zero; use `pow10` to calculate.
natExp10 : Nat -> Nat
natExp10 Z = 1
natExp10 (S k) = 10 * natExp10 k

plusIsSucc : {a, b : Nat} -> IsSucc a -> IsSucc (a + b)
plusIsSucc {a = S _} ItIsSucc = ItIsSucc

natExp10IsSucc : (n : Nat) -> IsSucc (natExp10 n)
natExp10IsSucc Z = ItIsSucc
natExp10IsSucc (S k) = plusIsSucc {a = natExp10 k} {b = mult 9 (natExp10 k)} (natExp10IsSucc k)

0 NatExp10NotZero : {n:Nat} -> NonZero (natExp10 n)
NatExp10NotZero = natExp10IsSucc n

||| The value of 1 in the numerator: 10 to the number of digits (Haskell's
||| `resolution`).
export
resolution : {n:Nat} -> (0 _:Fixed n) -> Integer
resolution _ = pow10 n

-- --------------------------------------------------------------------------
-- The operations; the instances below are made of these

public export
addF : Fixed n -> Fixed n -> Fixed n
addF x y = MkFixed (x.num + y.num)

public export
subF : Fixed n -> Fixed n -> Fixed n
subF x y = MkFixed (x.num - y.num)

public export
negF : Fixed n -> Fixed n
negF x = MkFixed (negate x.num)

||| A product, rounded down.
public export
mulF : {n:Nat} -> Fixed n -> Fixed n -> Fixed n
mulF x y = MkFixed ((x.num * y.num) `div` pow10 n)

public export
fromIntegerF : {n:Nat} -> Integer -> Fixed n
fromIntegerF i = MkFixed (i * pow10 n)

export
{n:Nat} -> Num (Fixed n) where
  (+) = addF
  (*) = mulF
  fromInteger = fromIntegerF

export
{n:Nat} -> Neg (Fixed n) where
  negate = negF
  (-) = subF

export
{n:Nat} -> Abs (Fixed n) where abs (MkFixed x) = MkFixed $ abs x

||| Division rounds down (for a divisor above zero; `div` of `Integer` with a
||| negative divisor is the backend's own), and dividing by zero stops the program
||| (`divide` and `recipMaybe` do not).
export
{n:Nat} -> Fractional (Fixed n) where
  x / y = MkFixed $ (x.num * pow10 n) `div` y.num
  recip x = let
    res = pow10 n in MkFixed $ (res * res) `div` x.num

export
[additiveFixedSemigroup] {n:Nat} -> Semigroup (Fixed n) where
  (<+>) = addF

export
[additiveFixedMonoid] {n:Nat} -> Monoid (Fixed n) using additiveFixedSemigroup where
  neutral = MkFixed 0


export
{n:Nat} -> Show (Fixed n) where
  show x = if n == 0 then show x.num
                     else if x.num < 0 then "-" ++ go (negate x.num)
                     else go x.num where
    go : Integer -> String
    go x = let r = pow10 n
               i = x `div` r
               d' = show $ x `mod` r
            in show i ++ "." ++ replicate (fromInteger $ cast $ cast n - strLength d') '0' ++ d'



-- --------------------------------------------------------------------------
-- Type cast


export
{n:Nat} -> Cast Int (Fixed n) where
  cast i = MkFixed $ (cast i) * pow10 n
export
{n:Nat} -> Cast Integer (Fixed n) where
  cast i = MkFixed $ i * pow10 n
||| Rounded down (towards minus infinity) like `*` and `/`; the `Maybe` is kept
||| for compatibility, a denominator is never zero.
export
{n:Nat} -> Cast Rational (Maybe (Fixed n)) where
  cast x = Just $ MkFixed $ (x.num * pow10 n) `div` (natToInteger x.den)
export
{n:Nat} -> Cast (Fixed n) Rational where
  cast x = MkRational x.num (natExp10 n) {denIsNonZero=NatExp10NotZero {n}}


-- --------------------------------------------------------------------------

export div' : {n:Nat} -> Fixed n -> Fixed n -> Integer
div' x q = x.num `div` q.num

export mod' : {n:Nat} -> Fixed n -> Fixed n -> Fixed n
mod' x q = MkFixed $ x.num `mod` q.num

export scale : {n:Nat} -> Integer -> Fixed n -> Fixed n
scale y x = MkFixed $ x.num * y

||| `x` to the power `e` by squaring (a loop that is not as deep as `e` is large,
||| unlike the `^` of contrib). Every product is rounded down, so the digits at
||| the end can differ from those of `^`, which multiplies in another order; the
||| fewer products, the nearer the result is to the true power. For a negative
||| power see `Data.Pow.(^^)`.
export pow : {n:Nat} -> Fixed n -> Nat -> Fixed n
pow = powNum

-- --------------------------------------------------------------------------
-- Division that cannot stop the program

||| `x / y`, `Nothing` when `y` is zero.
export
divide : {n:Nat} -> Fixed n -> Fixed n -> Maybe (Fixed n)
divide x y = if y.num == 0 then Nothing else Just (x / y)

||| The reciprocal, `Nothing` for zero.
export
recipMaybe : {n:Nat} -> Fixed n -> Maybe (Fixed n)
recipMaybe x = if x.num == 0 then Nothing else Just (recip x)

||| Quotient and remainder, as `div'` and `mod'` (the quotient rounded down).
export
divMod' : {n:Nat} -> Fixed n -> Fixed n -> (Integer, Fixed n)
divMod' x q = (div' x q, mod' x q)

-- --------------------------------------------------------------------------
-- Whole numbers and fractions

||| The greatest integer not above the number.
export
floor : {n:Nat} -> Fixed n -> Integer
floor x = x.num `div` pow10 n

||| The least integer not below the number.
export
ceil : {n:Nat} -> Fixed n -> Integer
ceil x = negate (negate x.num `div` pow10 n)

||| The integer part, towards zero.
export
truncate : {n:Nat} -> Fixed n -> Integer
truncate x = if x.num < 0 then negate (negate x.num `div` pow10 n) else x.num `div` pow10 n

||| The nearest integer; a number half way between two goes to the even one.
export
round : {n:Nat} -> Fixed n -> Integer
round x =
  let i = floor x
      twice = 2 * (x.num - i * pow10 n)    -- twice the fraction, in units of 10^-n
   in case compare twice (pow10 n) of
        LT => i
        GT => i + 1
        EQ => if i `mod` 2 == 0 then i else i + 1

||| The integer part (towards zero) and the fraction, which has the sign of the
||| number and is less than one.
export
properFraction : {n:Nat} -> Fixed n -> (Integer, Fixed n)
properFraction x = let i = truncate x in (i, x - fromInteger i)

||| The fraction of `properFraction`.
export
fract : {n:Nat} -> Fixed n -> Fixed n
fract = snd . properFraction

-- --------------------------------------------------------------------------
-- Other numbers

||| The same number with another count of digits: exact for more digits, rounded
||| down for fewer.
export
resize : {m, n : Nat} -> Fixed m -> Fixed n
resize x = MkFixed ((x.num * pow10 n) `div` pow10 m)

export
{n:Nat} -> Cast Nat (Fixed n) where
  cast i = MkFixed $ natToInteger i * pow10 n

||| The nearest number (a half goes away from zero); `Nothing` for a NaN, an
||| infinity and a number too large for a `Fixed` of this many digits (a count of
||| digits above 300 cannot be told from a Double either).
export
fromDouble : {n:Nat} -> Double -> Maybe (Fixed n)
fromDouble x =
  if n > 300 || x /= x || x - x /= 0 then Nothing
  else let scaled = x * cast (pow10 n)
        in if scaled - scaled /= 0 then Nothing
           else Just (MkFixed (cast (if scaled < 0 then scaled - 0.5 else scaled + 0.5)))

||| `fromDouble`, with zero for what it refuses.
export
{n:Nat} -> Cast Double (Fixed n) where
  cast x = fromMaybe (MkFixed 0) (fromDouble x)

export
{n:Nat} -> Cast (Fixed n) Double where
  cast x = cast x.num / cast (pow10 n)

||| Read `[-+]digits[.digits]` (`.5` and `5.` too, but not `.`); `Nothing` for
||| anything else and for more digits after the point than the type has.
export
parseFixed : {n:Nat} -> String -> Maybe (Fixed n)
parseFixed s =
  case unpack s of
    ('-' :: cs) => map negate (unsigned cs)
    ('+' :: cs) => unsigned cs
    cs => unsigned cs
  where
    digitsOf : List Char -> Maybe Integer
    digitsOf [] = Nothing
    digitsOf cs = if all isDigit cs then Just (foldl (\a, c => a * 10 + cast (ord c - ord '0')) 0 cs) else Nothing

    unsigned : List Char -> Maybe (Fixed n)
    unsigned cs =
      case break (== '.') cs of
        (whole, []) => map (\w => MkFixed (w * pow10 n)) (digitsOf whole)
        (whole, _ :: frac) =>
          if length frac > n || (null whole && null frac) then Nothing
          else do
            w <- if null whole then Just 0 else digitsOf whole
            f <- if null frac then Just 0 else digitsOf frac
            Just (MkFixed (w * pow10 n + f * pow10 (n `minus` length frac)))

-- --------------------------------------------------------------------------
-- vim: tw=80 sw=2 expandtab :
