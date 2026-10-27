module Main

import Data.Nat  -- for NonZero
import Data.List
import Data.Fixed
import Data.Pow
import Data.Complex
import Data.Rational
import Text.Format.Decimal
import System.Info

assertEq : Show a => Eq a => a -> a -> IO ()
assertEq x y with (x == y)
  _ | True  = putStr "✓"
  _ | False = putStrLn ("\n  ✗ expected=" ++ show x ++ " actual=" ++ show y)

chk : (Show a, Show b) => String -> List (a, b) -> (b -> a) -> (b -> a -> a -> Bool) -> IO ()
chk dsc xs f g = do
  putStr (dsc ++ ": ")
  for_ xs $
    \xs@(e, x) => do
      let ans = f x
      if g x e ans
         then putStr "✓"
         else putStrLn ("\n  ✗ test=" ++ show xs ++ " ans=" ++ show ans)
  putStrLn ""


partial main : IO ()
main = do
  putStrLn $ "Codegen : \{System.Info.codegen}"
  testTextFormat >> testComplex >> testFixed >> testRational
  where
    testTextFormat : IO ()
    testTextFormat = do
      do
        let fmt00 = { width := Just 4, prec := Just 0, pad := Nothing,
                      spc := ' ', point := '.',
                      minus := Just (Left "-"), plus := Nothing } defaultDecimalFormat
        chk "Text format (Int + Width)"
            [ ("   0", 0), ("   1", 1), ("  10", 10), (" -10", -10)
            , ("-999", -999), (" 999", 999), ("1234", 1234), ("-1234", -1234)
            , ("99999", 99999) ]
            (format fmt00) (const (==))
      do
        let fmt00 = { width := Nothing, prec := Just 0, pad := Nothing,
                      spc := ' ', point := '.',
                      minus := Just (Left "-"), plus := Nothing } defaultDecimalFormat
        chk "Text format (Int + no width)"
            [ ("0", 0), ("1", 1), ("10", 10), ("-10", -10), ("-999", -999)
            , ("999", 999), ("1234", 1234), ("-1234", -1234), ("99999", 99999) ]
            (format fmt00) (const (==))
      do
        let fmt00 = { width := Just 4, prec := Just 0, pad := Nothing,
                      spc := ' ', point := '.',
                      minus := Just (Left "-"), plus := Just (Left "+") } defaultDecimalFormat
        chk "Text format (Int + Width and PlusSign"
            [ ("  +0", 0), ("  +1", 1), ("+123", 123), ("+1234", 1234) ]
            (format fmt00) (const (==))

      do
        let fmt00 = { width := Just 4, prec := Just 0, pad := Nothing,
                      spc := ' ', point := '.',
                      minus := Just (Right "-"), plus := Nothing } defaultDecimalFormat
        chk "Text format (Int + TailingSign)"
            [ ("   0", 0), ("   1-", -1), (" 123-", -123), ("1234-", -1234) ]
            (format fmt00) (const (==))

      do
        let fmt00 = { width := Just 4, prec := Just 0, pad := Just '0',
                      spc := ' ', point := '.',
                      minus := Just (Left "-"), plus := Nothing } defaultDecimalFormat
        chk "Text format (Int + Padding)"
            [ ("0000", 0), ("-0001", -1), ("-0123", -123), ("-1234", -1234) ]
            (format fmt00) (const (==))

      do
        let fmt00 = { width := Nothing, prec := Just 0, pad := Just '0',
                      spc := ' ', point := '.',
                      minus := Just (Left "-"), plus := Nothing } defaultDecimalFormat
        chk "Text format (Int + no width + padding)"
            [ ("0", 0), ("-1", -1), ("-123", -123), ("-1234", -1234) ]
            (format fmt00) (const (==))

      do
        let fmt00 = { width := Just 4, prec := Nothing, pad := Nothing,
                      spc := ' ', point := '.',
                      minus := Just (Left "-"), plus := Nothing } defaultDecimalFormat
        chk "Text format (Fixed + Width)"
            [("   0.000000000000", the (Fixed 12) 0),
             ("   1.000000000000", 1), (" -10.000000000000", -10) ]
            (format fmt00) (const (==))

    testComplex : IO ()
    testComplex = do
      chk "Complex Eq"
          [ (True, (MkComplex 0 1, MkComplex 0 1))
          , (False, (MkComplex 1 1, MkComplex 0 1)) ]
          (uncurry (==)) (const (==))

    testFixed : IO ()
    testFixed = do
      chk "Fixed"
         [ ("0.000000000000", the (Fixed 12) 0)
         , ("99.000000000000", 99)
         , ("99.000000000000", 100 - 1)
         , ("0.000000000099", MkFixed 100 - MkFixed 1 )
         , ("1.000000000100", MkFixed 100 + 1 )
         , ("8.000000000372", (2 + MkFixed 93) * 4 )
         , ("-0.500000000023", negate ((2 + MkFixed 93) / 4) )
         , ("0.333333333333", recip 3 )
         ] show (const (==))
      -- the table of powers of ten agrees with squaring, and goes on past the table
      chk "Powers of ten"
         [ (True, n) | n <- [0 .. 60] ]
         (\n => pow10 n == powBy (*) 1 10 n && pow10 n == natToInteger (the Nat 10 `power` n)) (const (==))
      -- powBy itself: exponents 0, 1, 2, powers of two, odd and even, and strings (the count of factors)
      chk "powBy"
         [ (1, powBy (*) 1 (the Integer 7) 0), (7, powBy (*) 1 (the Integer 7) 1), (49, powBy (*) 1 (the Integer 7) 2)
         , (2401, powBy (*) 1 (the Integer 7) 4), (343, powBy (*) 1 (the Integer 7) 3), (16807, powBy (*) 1 (the Integer 7) 5)
         , (1024, powBy (*) 1 (the Integer 2) 10), (1073741824, powBy (*) 1 (the Integer 2) 30) ]
         id (const (==))
      let cat = \a, b => a ++ the String b
      chk "powBy on strings"
         [ ("", powBy cat "" "ab" 0), ("ab", powBy cat "" "ab" 1), ("abab", powBy cat "" "ab" 2)
         , ("ababab", powBy cat "" "ab" 3), ("ababababab", powBy cat "" "ab" 5), (fastConcat (replicate 13 "xy"), powBy cat "" "xy" 13) ]
         id (const (==))
      chk "Fixed with many digits"
         [ ("1.000000000000000000000000000000000000000000", the (Fixed 42) 1)
         , ("0.333333333333333333333333333333333333333333", recip 3)
         , ("2.500000000000000000000000000000000000000000", the (Fixed 42) 5 / 2)
         , ("0.000000000000000000000000000000000000000001", MkFixed 1)
         ] show (const (==))
      -- powers: small, zero, negative, large (a loop, no deep recursion)
      chk "Fixed pow and ^^"
         [ ("1.000000000000", pow (the (Fixed 12) 7) 0)
         , ("7.000000000000", pow (the (Fixed 12) 7) 1)
         , ("343.000000000000", pow (the (Fixed 12) 7) 3)
         , ("1024.000000000000", pow (the (Fixed 12) 2) 10)
         , ("0.000976562500", the (Fixed 12) 2 ^^ (-10))
         , ("0.250000000000", the (Fixed 12) 2 ^^ (-2))
         , ("1.000000000000", the (Fixed 12) 5 ^^ 0)
         , ("1.000100004928", pow (the (Fixed 12) (MkFixed 1000000001000)) 100000)
         , ("1.001000499452", pow (the (Fixed 12) (MkFixed 1000000001000)) 1000000)
         , ("1.000000000000", pow (the (Fixed 12) 1) 4000000)
         ] show (const (==))
      chk "Fixed and Rational"
         [ ("Just 0.250000000000", show (the (Maybe (Fixed 12)) (cast (1 %: 4))))
         , ("Just 0.333333333333", show (the (Maybe (Fixed 12)) (cast (2 %: 6))))
         , ("Just -0.500000000000", show (the (Maybe (Fixed 12)) (cast ((-1) %: 2))))
         , ("25 %: 100", show (the Rational (cast (the (Fixed 2) (MkFixed 25)))))
         ] id (const (==))

    testRational : IO ()
    testRational = do
      chk "Rational"
         [ ( "Just (2 %: 10)", 2 %? 10 )
         , ( "Just (1 %: 3)" , map reduce (3 %? 9) )
         , ( "Just (-1 %: 3)", map reduce (3 %? -9) )
         , ( "Just (-1 %: 3)", map reduce (-3 %? 9) )
         , ( "Just (1 %: 3)" , map reduce (-3 %? -9) )
         , ( "Just (8 %: 15)", Just ((1 %: 3) + (1 %: 5)))
         , ( "Just (2 %: 15)", Just ((1 %: 3) * (2 %: 5)))
         --, ( "5 %: 6", (1 %: 3) / (2 %: 5))
         -- , ( "3 %: 1", recip (1 %: 3))
         ] show (const (==))
      assertEq LT (compareAsReal (2 %: 3) (4 %: 5))
      assertEq EQ (compareAsReal (2 %: 3) (4 %: 6))
      assertEq GT (compareAsReal (2 %: 3) (5 %: 20))
      assertEq 18 $ floor (55 %: 3)
      assertEq 19 $ ceil (55 %: 3)



