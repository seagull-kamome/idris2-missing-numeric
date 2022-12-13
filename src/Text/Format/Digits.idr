||| Format decimal number into string.
||| 
||| Copyright 2021, HATTORI, Hiroki
||| This file is released under the MIT license, see LICENSE for more detail.
||| 
module Text.Format.Digits

import Data.Nat
import Data.Fin
import Data.Primitives.Views
import Data.String

%default total

-- --------------------------------------------------------------------------

public export Digits : (base:Nat) -> Type
Digits base = (n:Nat) -> {0 p:So (n < base)} -> Char

upperHexdigit : Digits 36
upperHexdigit n = assert_total $ strIndex "0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZ" $ cast n

lowerHexdigit : Digits 36
lowerHexdigit n = assert_total $ strIndex "0123456789abcdefghijklmnopqrstuvwxyz" $ cast n


intToDigits : (base:Nat)
            -> {base':Nat} -> {auto ok:base <= base' = True} -> Digits base'
            -> Int -> String
intToDigits base digits n = if n < 0 then pack $ go n [] else "0"
  where
    base_i : Int
    base_i = cast base

    go : Int -> List Char -> List Char
    go 0 xs = xs
    go m xs with (m `divides` base_i)
      go (_ * d + r) xs | DivBy d r prf =
        let prf' = believe_me prf
            in go (assert_smaller n d) (digits {ok=prf'} (cast r) :: xs)



-- --------------------------------------------------------------------------

public export DigitNum : (base:Nat) -> Type
DigitNum base = Char -> Maybe Int

hexNum : DigitNum 16
hexNum '0' = Just 0
hexNum '1' = Just 1
hexNum '2' = Just 2
hexNum '3' = Just 3
hexNum '4' = Just 4
hexNum '5' = Just 5
hexNum '6' = Just 6
hexNum '7' = Just 7
hexNum '8' = Just 8
hexNum '9' = Just 9
hexNum 'a' = Just 10
hexNum 'A' = Just 10
hexNum 'b' = Just 11
hexNum 'B' = Just 11
hexNum 'c' = Just 12
hexNum 'C' = Just 12
hexNum 'd' = Just 13
hexNum 'D' = Just 13
hexNum 'e' = Just 14
hexNum 'E' = Just 14
hexNum 'f' = Just 15
hexNum 'F' = Just 15
hexNum _ = Nothing


digitsToInt : (base:Nat)
           -> {base':Nat} -> {auto ok:base <= base' = True} -> Digits base'
           -> String -> Maybe Int
digitsToInt base digits str = go 0 $ unpack str where
  base_i : Int
  base_i = cast base

  go : Int -> List Char -> Maybe Int
  go ans [] = Just ans
  go ans (x::xs) with (hexNum x)
    go ans (x::xs) | Just x' = go (ans * base_i + x') xs
    go ans (x::xs) | Nothing = Nothing


-- --------------------------------------------------------------------------
-- vim: tw=80 sw=2 expandtab :
