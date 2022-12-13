||| Fixed point fractional number. - Ported from Haskell base.
|||
||| Copyright 2021, HATTORI, Hiroki
||| This file is released under the MIT license, see LICENSE for more detail.
|||
module Data.Fixed

import Data.Nat
import Data.Maybe
import Data.String
import Data.Rational
import Generics.Newtype

import Data.Monoid.Exponentiation

%default total
%language ElabReflection

-- --------------------------------------------------------------------------

public export
record Fixed (n:Nat) where
  constructor MkFixed
  num : Integer
%runElab derive "Fixed" [Generic, Eq, Ord, DecEq]


export exp10 : Nat -> Integer
exp10 n with (n)
  _ | 0  = 1
  _ | 1  = 10
  _ | 2  = 100
  _ | 3  = 1000
  _ | 4  = 10000
  _ | 5  = 100000
  _ | 6  = 1000000
  _ | 7  = 10000000
  _ | 8  = 100000000
  _ | 9  = 1000000000
  _ | 10 = 10000000000
  _ | 11 = 100000000000
  _ | 12 = 1000000000000
  _ | 13 = 10000000000000
  _ | 14 = 100000000000000
  _ | 15 = 1000000000000000
  _ | 16 = 10000000000000000
  _ | 17 = 100000000000000000
  _ | 18 = 1000000000000000000
  _ | 19 = 10000000000000000000
  _ | _ = cast $ 10 ^ n

export resolution : {n:Nat} -> Fixed n -> Integer
resolution _ = exp10 n




export
{n:Nat} -> Num (Fixed n) where
  x + y = MkFixed $ x.num + y.num
  x * y = MkFixed $ (x.num * y.num) `div` (exp10 n)
  fromInteger i = MkFixed $ i * (exp10 n)

export
{n:Nat} -> Neg (Fixed n) where
  negate x = MkFixed $ negate x.num
  x - y = MkFixed $ x.num - y.num

export
{n:Nat} -> Abs (Fixed n) where abs (MkFixed x) = MkFixed $ abs x

export
{n:Nat} -> Fractional (Fixed n) where
  x / y = MkFixed $ (x.num * (exp10 n)) `div` y.num
  recip x = let
    res = exp10 n in MkFixed $ (res * res) `div` x.num


export
{n:Nat} -> Show (Fixed n) where
  show x = if n == 0 then show x.num
                     else if x.num < 0 then "-" ++ go (negate x.num)
                     else go x.num where
    go : Integer -> String
    go x = let r = exp10 n
               i = x `div` r
               d' = show $ x `mod` r
            in show i ++ "." ++ replicate (fromInteger $ cast $ cast n - strLength d') '0' ++ d'



-- --------------------------------------------------------------------------
-- Type cast


export
{n:Nat} -> Cast Int (Fixed n) where
  cast i = MkFixed $ (cast i) * (exp10 n)
export
{n:Nat} -> Cast Integer (Fixed n) where
  cast i = MkFixed $ i * (exp10 n)
export
{n:Nat} -> Cast Rational (Maybe (Fixed n)) where
  cast x = let d = x.den
            in toMaybe (d == 0) $ MkFixed $ x.num * (exp10 n) `div` (natToInteger d)
export
{n:Nat} -> Cast (Fixed n) Rational where
  cast x = x.num %: (exp10 n)


-- --------------------------------------------------------------------------

export div' : {n:Nat} -> Fixed n -> Fixed n -> Integer
div' x q = x.num `div` q.num

export mod' : {n:Nat} -> Fixed n -> Fixed n -> Fixed n
mod' x q = MkFixed $ x.num `mod` q.num

export scale : {n:Nat} -> Integer -> Fixed n -> Fixed n
scale y x = MkFixed $ x.num * y

-- --------------------------------------------------------------------------
-- vim: tw=80 sw=2 expandtab :
