||| Rational number
||| 
||| Copyright 2021, HATTORI, Hiroki
||| This file is released under the MIT license, see LICENSE for more detail.
||| 
module Data.Rational

import Decidable.Equality
import Data.Nat
import Data.Nat.Factor
import Data.Maybe

%default total

-- --------------------------------------------------------------------------

public export
record Rational where
  constructor MkRational
  num : Integer
  den : Nat
  0 denIsSucc : Not (den=0)



-- --------------------------------------------------------------------------

0 bothSuccMultSucc : {a,b:Nat} -> Not (a=0) -> Not (b=0) -> Not (a*b=0)
bothSuccMultSucc {a=a}{b=b} prl prr with (decEq (a*b) 0)
  _ | Yes prf = case zeroMultEitherZero a b prf of
                  Left pr1  => void $ prl pr1
                  Right pr1 => void $ prr pr1
  _ | No prf = prf

-- --------------------------------------------------------------------------

export reduce : (num:Integer) -> (den:Nat) -> {auto 0 ok:Not (den=0)} -> Rational
reduce _ 0 = void $ ok Refl
reduce num den@(S _) =
  let (f ** MkGCD (CommonFactorExists _ _ pr0) _) = Data.Nat.Factor.gcd (fromInteger $ abs num) den in
  let (den' ** CofactorExists q pr1) = cofactor pr0 in
  case decEq den' 0 of
    Yes prf => void $ ok $ rewrite pr1 in rewrite prf in Refl
    No prf => MkRational (num `div` (cast f)) den' prf

infixr 9 %:

public export
(%:) : (num:Integer) -> (den:Integer) -> {0 ok:Not (den=0)} -> Rational
(%:) num den =
  let den' = cast $ abs den in
  let num' = num * (if den < 0 then -1 else 1) in
  reduce num' den' {ok= ?rhl_mkratio}



-- --------------------------------------------------------------------------

export
Show Rational where
  showPrec d x = showParens (d >= PrefixMinus && x.num < 0) "\{show x.num} %: \{show x.den}"

public export
Eq Rational where
  x == y = let x' = x.num * natToInteger y.den
               y' = y.num * natToInteger x.den
            in x' == y'

public export
Ord Rational where
  compare x y = let x' = x.num * natToInteger y.den
                    y' = y.num * natToInteger x.den
                  in compare x' y'

public export Cast Integer Rational where cast x = MkRational x 1 absurd
Cast ty Integer => Cast ty Rational where cast x = MkRational (cast x) 1 absurd

public export
Num Rational where
  x + y = reduce (x.num * natToInteger y.den + y.num * natToInteger x.den) (x.den * y.den) {ok=bothSuccMultSucc x.denIsSucc y.denIsSucc}
  x * y = reduce (x.num * y.num) (x.den * y.den) {ok=bothSuccMultSucc x.denIsSucc y.denIsSucc}
  fromInteger x = MkRational x 1 absurd

public export
Neg Rational where
  negate x = { num := negate x.num } x
  x - y = reduce (x.num * natToInteger y.den - x.num * natToInteger x.den) (x.den * y.den) {ok=bothSuccMultSucc x.denIsSucc y.denIsSucc}

public export
Abs Rational where
  abs x = { num := abs x.num } x
  -- signum x = MkRational (signum x.num) 1

-- --------------------------------------------------------------------------

export recip : (x:Rational) -> {auto 0 ok:Not (x.num=0)} -> Rational
recip (MkRational 0 _) impossible
recip x = (%:) (cast x.den) x.num {ok=ok}

export floor : Rational -> Maybe Integer
floor x = toMaybe (x.den /= 0) $ x.num `div` (natToInteger x.den)

export ceil : Rational -> Maybe Integer
ceil x = floor $ { num := x.num + (natToInteger x.den) - 1 } x

-- --------------------------------------------------------------------------
-- vim: tw=80 sw=2 expandtab :
