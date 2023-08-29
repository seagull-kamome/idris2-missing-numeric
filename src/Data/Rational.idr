||| Rational number
||| 
||| Copyright 2021-2023 HATTORI, Hiroki
||| This file is released under the MIT license, see LICENSE for more detail.
||| 
module Data.Rational

import Control.Algebra
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
  {auto 0 denIsNonZero : NonZero den}


public export NonZero : Rational -> Type
NonZero x = Not (x.num=0)

-- --------------------------------------------------------------------------
namespace Lemma

  public export
  0 bothSuccMultSucc : {a,b:Nat} -> NonZero a -> NonZero b -> NonZero (a*b)
  bothSuccMultSucc {a=a}{b=b} prl prr with (a*b)
    _ | Z = case zeroMultEitherZero a b of
              Left _ impossible
              Right _ impossible
    _ | S _ = SIsNonZero


-- --------------------------------------------------------------------------

export reduce : Rational -> Rational
reduce (MkRational num den@(S _)) =
  let (f ** MkGCD (CommonFactorExists _ _ pr0) _) = Data.Nat.Factor.gcd (fromInteger $ abs num) den in
  let (den' ** CofactorExists q pr1) = cofactor pr0 in
  case den' of
    Z impossible
    S _ => MkRational (num `div` (cast f)) den'



infixr 9 %:, %?

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
-- Cast ty Integer => Cast ty Rational where cast x = MkRational (cast x) 1

-- --------------------------------------------------------------------------
public export
Eq Rational where
  (MkRational lnum lden) == (MkRational rnum rden) = lnum == rnum && lden == rden

public export compareAsReal : Rational -> Rational -> Ordering
compareAsReal (MkRational lnum lden) (MkRational rnum rden) =
  compare (lnum * natToInteger rden) (rnum * natToInteger lden)


export
Num Rational where
  l + r = MkRational (l.num * natToInteger r.den + r.num * natToInteger l.den)
                     (l.den * r.den)
                     {denIsNonZero=bothSuccMultSucc l.denIsNonZero r.denIsNonZero}
  l * r = MkRational (l.num * r.num) (l.den * r.den)
                     {denIsNonZero=bothSuccMultSucc l.denIsNonZero r.denIsNonZero}
  fromInteger x = MkRational x 1

export
Neg Rational where
  negate (MkRational num den) = MkRational (negate num) den
  l - r = MkRational (l.num * natToInteger r.den - r.num * natToInteger l.den) (l.den * r.den)
                     {denIsNonZero=bothSuccMultSucc l.denIsNonZero r.denIsNonZero}

public export
Abs Rational where
  abs (MkRational num den) = MkRational (abs num) den
  -- signum x = MkRational (signum x.num) 1

-- --------------------------------------------------------------------------
namespace SimpleOpr
  namespace Nat
    public export %inline mult : Rational -> Nat -> Rational
    mult (MkRational num den)  n = MkRational (num * cast n) den

    public export %inline div : Rational -> (n:Nat) -> {auto 0 nIsNonZero:NonZero n} -> Rational
    div (MkRational num den {denIsNonZero}) n =
      let 0 prf : NonZero (den * n) = bothSuccMultSucc denIsNonZero nIsNonZero
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
[additiveRationalSemigroupV] SemigroupV Rational using additiveRationalSemigroup where
  semigroupOpIsAssociative l c r = ?rhs_semigroupOpIsAssociative

export
[additiveRationalMonoid]  Monoid Rational using additiveRationalSemigroup where
  neutral = MkRational 0 1

export
[additiveRationalMonoidV] MonoidV Rational using additiveRationalMonoid additiveRationalSemigroupV where
  monoidNeutralIsNeutralL l = ?rhs_nonoidNeutralIsNeutralL
  monoidNeutralIsNeutralR r = ?rhs_nonoidNeutralIsNeutralR

export
[additiveRationalGroup] Group Rational using additiveRationalMonoidV where
  inverse = negate
  groupInverseIsInverseR r = ?rhs_groupInverseIsInerseR

export
[additiveRationalAbelianGroup] AbelianGroup Rational using additiveRationalGroup where
  groupOpIsCommutative l r =
    rewrite multCommutative l.den r.den
     in ?rhs_groupOpIsCommutative


-- --------------------------------------------------------------------------

export recip : (x:Rational) -> {auto 0 ok:Not (x.num=0)} -> Maybe Rational
recip x with (the Nat $ fromInteger x.num)
  _ | 0 = Nothing
  _ | n@(S _) = Just $ MkRational (natToInteger x.den) n

export floor : Rational -> Integer
floor x = x.num `div` (natToInteger x.den)

export ceil : Rational -> Integer
ceil x = (x.num + (natToInteger x.den) - 1) `div` (natToInteger x.den)

-- --------------------------------------------------------------------------
-- vim: tw=80 sw=2 expandtab :
