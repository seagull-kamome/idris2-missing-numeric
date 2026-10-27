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
export
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

resolution : {n:Nat} -> (0 _:Fixed n) -> Nat
resolution _ = natExp10 n




export
{n:Nat} -> Num (Fixed n) where
  x + y = MkFixed $ x.num + y.num
  x * y = MkFixed $ (x.num * y.num) `div` pow10 n
  fromInteger i = MkFixed $ i * pow10 n

export
{n:Nat} -> Neg (Fixed n) where
  negate x = MkFixed $ negate x.num
  x - y = MkFixed $ x.num - y.num

export
{n:Nat} -> Abs (Fixed n) where abs (MkFixed x) = MkFixed $ abs x

export
{n:Nat} -> Fractional (Fixed n) where
  x / y = MkFixed $ (x.num * pow10 n) `div` y.num
  recip x = let
    res = pow10 n in MkFixed $ (res * res) `div` x.num


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
-- vim: tw=80 sw=2 expandtab :
