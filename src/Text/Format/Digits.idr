||| Format decimal number into string.
||| 
||| Copyright 2021-2023, HATTORI, Hiroki
||| This file is released under the MIT license, see LICENSE for more detail.
||| 
module Text.Format.Digits

import Data.Nat
import Data.Fin
import Data.Primitives.Views
import Data.String

%default total

-- --------------------------------------------------------------------------

public export Digits : Nat -> Type
Digits _ = String

public export toDigit : {0 base:Nat} -> Digits base -> (n:Nat) -> {auto 0 prfNumLEBase:So (n < base)} -> Char
toDigit digits  n = assert_total $ strIndex digits $ cast n

public export fromDigit : {base:Nat} -> Digits base -> (ch:Char) -> Maybe Nat
fromDigit {base=base} digits ch = go 0 $ asList digits
  where
   go : Nat -> AsList xs -> Maybe Nat
   go n Nil = Nothing
   go n (x::xs) =
     if n >= base then Nothing
        else if ch == x then Just n else go (n + 1) xs

public export %inline upperAlnumDigits : {auto 0 base:Nat} -> {auto 0 _: So (base <= 36)} -> Digits base
upperAlnumDigits = "0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZ"

public export %inline lowerAlnumDigits : {auto 0 base:Nat} -> {auto 0 _: So (base <= 36)} -> Digits base
lowerAlnumDigits = "0123456789abcdefghijklmnopqrstuvwxyz"

public export upperHexdigits : Digits 16
upperHexdigits = upperAlnumDigits {base=16}

public export lowerHexdigits : Digits 16
lowerHexdigits = lowerAlnumDigits {base=16}



-- --------------------------------------------------------------------------

||| Render Integer number into String with base.
|||
||| >>> intToDigits lowerHexdigits 999
||| 3e7
|||
||| >>> intToDigits (upperAlnumDigits {base=8}) 11
||| 13
|||
public export
intToDigits : {base:Nat} -> Digits base -> Int -> String
intToDigits {base=base} digits n =
  case compare n 0 of
    EQ => "0"
    LT => pack ('-' :: (go bi (abs n) []))
    GT => pack $ go bi n []
  where
    -- Bound once as a plain local variable rather than inlining `cast
    -- base` at each use: `with`/`case` on `n \`divides\` d` can only
    -- refine `d` to the literal `0` in the `DivByZero` branch when `d`
    -- is itself a pattern variable -- unifying an opaque application
    -- like `cast base` against `0` is something the elaborator can't
    -- solve, since `base` is abstract (it genuinely could be `Z`, this
    -- isn't a workaround for a solvable-but-awkward goal).
    bi : Int
    bi = cast base

    go : Int -> Int -> List Char -> List Char
    go d 0 xs = xs
    go d n xs with (n `divides` d)
      go d (_ * dv + r) xs | DivBy dv r prf =
        let prf' : So ((cast r) < base) = ?go_prf_rhs
         in go d (assert_smaller n dv) (toDigit {prfNumLEBase=prf'} digits (cast r) :: xs)
      -- `base = 0`: `Digits 0` has no digit characters to index into
      -- anyway, so nothing more can be rendered -- stop here rather
      -- than claim a digit that doesn't exist.
      go 0 n xs | DivByZero = xs


-- --------------------------------------------------------------------------

||| Convert String to Int
|||
||| >>> digitsToInt upperHexdgits "1A"
||| 26
|||
public export
digitsToInt : {base:Nat} -> Digits base -> String -> Maybe Int
digitsToInt {base=base} digits str =
  case asList str of
    Nil => Nothing
    ('-'::xs) => map negate $ go 0 xs
    xs => go 0 xs
  where
    base_i : Int
    base_i = cast base
    go : Int -> AsList _ -> Maybe Int
    go ans Nil = Just ans
    go ans (x::xs) with (fromDigit {base=base} digits x)
      _ | Just x' = go (ans * base_i + cast x') xs
      _ | Nothing = Nothing


-- --------------------------------------------------------------------------
-- vim: tw=80 sw=2 expandtab :
