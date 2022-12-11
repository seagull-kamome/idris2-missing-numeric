||| Format decimal number into string.
||| 
||| Copyright 2021, HATTORI, Hiroki
||| This file is released under the MIT license, see LICENSE for more detail.
||| 
module Text.Format.Digits

import Data.Nat
import Data.Fin
import Data.Primitives.Views

%default total

-- --------------------------------------------------------------------------

public export Digits : (base:Nat) -> Type
Digits base = (n:Nat) -> {auto ok:n < (cast base) = True} -> Char


upperHexdigit : Digits 16
upperHexdigit 0 = '0'
upperHexdigit 1 = '1'
upperHexdigit 2 = '2'
upperHexdigit 3 = '3'
upperHexdigit 4 = '4'
upperHexdigit 5 = '5'
upperHexdigit 6 = '6'
upperHexdigit 7 = '7'
upperHexdigit 8 = '8'
upperHexdigit 9 = '9'
upperHexdigit 10 = 'A'
upperHexdigit 11 = 'B'
upperHexdigit 12 = 'C'
upperHexdigit 13 = 'D'
upperHexdigit 14 = 'E'
upperHexdigit 15 = 'F'
upperHexdigit _ = '_' -- why i need this?


lowerHexdigit : Digits 16
lowerHexdigit 0 = '0'
lowerHexdigit 1 = '1'
lowerHexdigit 2 = '2'
lowerHexdigit 3 = '3'
lowerHexdigit 4 = '4'
lowerHexdigit 5 = '5'
lowerHexdigit 6 = '6'
lowerHexdigit 7 = '7'
lowerHexdigit 8 = '8'
lowerHexdigit 9 = '9'
lowerHexdigit 10 = 'a'
lowerHexdigit 11 = 'b'
lowerHexdigit 12 = 'c'
lowerHexdigit 13 = 'd'
lowerHexdigit 14 = 'e'
lowerHexdigit 15 = 'f'
lowerHexdigit _ = '_'  -- also this



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
