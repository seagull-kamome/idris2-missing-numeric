||| GCD and LCM. This is partial algorhytm with assert_total notation.
|||
||| Copyright 2021, HATTORI, Hiroki
||| This file is released under the MIT license, see LICENSE for more detail.
|||
module Data.Integral.Gcd

%default total

-- --------------------------------------------------------------------------

export gcd : (Eq a, Num a, Abs a, Integral a) => a -> a -> a
gcd x y = go (abs x) (abs y)
  where go : a -> a -> a
        go x' y' = if y' == 0 then x' else assert_total $ go y' (x' `mod` y')


export lcm : (Eq a, Num a, Abs a, Integral a) => a -> a -> a
lcm x y = if x == 0 then 0
          else if y == 0 then 0
          else abs $ (x `div` (gcd x y)) * y

-- --------------------------------------------------------------------------
-- vim: tw=80 sw=2 expandtab :
