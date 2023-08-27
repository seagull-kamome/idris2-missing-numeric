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
    LT => pack ('-' :: (go (abs n) []))
    GT => pack $ go n []
  where
    go : Int -> List Char -> List Char
    go 0 xs = xs
    go n xs with (n `divides` (cast base))
      go (_ * d + r) xs | DivBy d r prf =
        let prf' : So ((cast r) < base) = ?go_prf_rhs
         in go (assert_smaller n d) (toDigit {prfNumLEBase=prf'} digits (cast r) :: xs)


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
