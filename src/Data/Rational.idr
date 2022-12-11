||| Rational number
||| 
||| Copyright 2021, HATTORI, Hiroki
||| This file is released under the MIT license, see LICENSE for more detail.
||| 
module Data.Rational

import Data.Maybe
import Data.Integral.Gcd

import Generics.Derive

%default total
%language ElabReflection

-- --------------------------------------------------------------------------

public export
record Rational where
  constructor MkRational
  num : Integer
  den : Nat
%runElab derive "Rational" [Generic, Eq, DecEq]

export infinity : Rational
infinity = MkRational 0 0

export isInfinity : Rational -> Bool
isInfinity x = x.den == 0


-- --------------------------------------------------------------------------

export reduce : (num:Integer) -> (den:Nat) -> Rational
reduce x y =
  let d = gcd x $ natToInteger y
   in MkRational (x `div` d) (fromInteger $ (natToInteger y) `div` d)

infixr 9 %:

public export
(%:) : (num:Integer) -> (den:Integer) -> Rational
(%:) num den =
  if den >= 0
     then reduce num $ fromInteger den
     else reduce (negate num) (fromInteger $ negate den)



-- --------------------------------------------------------------------------

export
Show Rational where
  show x with (isInfinity x)
    _ | True = "#Infinity"
    _ | False = "\{show x.num} %: \{show x.den}"

public export
Ord Rational where
  compare x y = let x' = x.num * natToInteger y.den
                    y' = y.num * natToInteger x.den
                  in compare x' y'

public export Cast Integer Rational where cast x = MkRational x 1
Cast ty Integer => Cast ty Rational where cast x = MkRational (cast x) 1


public export
Num Rational where
  x + y = reduce (x.num * natToInteger y.den + y.num * natToInteger x.den) (x.den * y.den)
  x * y = reduce (x.num * y.num) (x.den * y.den)
  fromInteger x = MkRational x 1

public export
Neg Rational where
  negate x = MkRational (negate x.num) x.den
  x - y = reduce (x.num * natToInteger y.den - x.num * natToInteger x.den) (x.den * y.den)

public export
Abs Rational where
  abs x = MkRational (abs x.num) x.den
  -- signum x = MkRational (signum x.num) 1


public export
Fractional Rational where
  x / y = (x.num * natToInteger y.den) %: (y.num * natToInteger x.den)
  recip x = (natToInteger x.den) %: (fromInteger x.num)




-- --------------------------------------------------------------------------

export floor : Rational -> Maybe Integer
floor x = toMaybe (x.den /= 0) $ x.num `div` (natToInteger x.den)

export ceil : Rational -> Maybe Integer
ceil x = floor $ MkRational (x.num + (natToInteger x.den) - 1) x.den

-- --------------------------------------------------------------------------
-- vim: tw=80 sw=2 expandtab :
