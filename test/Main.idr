module Main

import Data.Nat  -- for NonZero
import Data.List
import Data.Maybe
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

implies' : Bool -> Bool -> Bool
implies' p q = not p || q

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



      -- Eq and Ord compare the numbers, not the representations
      chk "Rational Eq/Ord"
         [ (True, (1 %: 2) == (2 %: 4)), (False, (1 %: 2) == (1 %: 3)), (True, (-1 %: 2) == (-2 %: 4))
         , (True, (1 %: 3) < (1 %: 2)), (True, (-1 %: 2) < (-1 %: 3)), (False, (2 %: 4) < (1 %: 2)), (True, (2 %: 4) <= (1 %: 2))
         , (True, max (1 %: 3) (1 %: 2) == (1 %: 2)), (True, compare (2 %: 3) (4 %: 6) == EQ) ]
         id (const (==))
      -- the reciprocal keeps the sign; division; powers
      chk "Rational recip, division, powers"
         [ ("Just (3 %: 1)", show (recipMaybe (1 %: 3)))
         , ("Just (-4 %: 3)", show (recipMaybe (-3 %: 4)))
         , ("Nothing", show (recipMaybe (0 %: 5)))
         , ("Just (5 %: 6)", show ((1 %: 3) /? (2 %: 5)))
         , ("Nothing", show ((1 %: 3) /? (0 %: 1)))
         , ("1 %: 8", show (pow (1 %: 2) 3))
         , ("1 %: 1", show (pow (7 %: 3) 0))
         , ("Just (1 %: 8)", show (powInteger (1 %: 2) 3))
         , ("Just (8 %: 1)", show (powInteger (1 %: 2) (-3)))
         , ("Just (9 %: 4)", show (powInteger (-2 %: 3) (-2)))
         , ("Nothing", show (powInteger (0 %: 1) (-1)))
         , ("Just (1 %: 1)", show (powInteger (0 %: 1) 0)) ]
         id (const (==))
      -- floor, ceil, truncate, round (half to even), the integer part and the fraction
      chk "Rational whole part"
         [ ((2, 3, 2, 2), (floor (5 %: 2), ceil (5 %: 2), truncate (5 %: 2), round (5 %: 2)))
         , ((-3, -2, -2, -2), (floor (-5 %: 2), ceil (-5 %: 2), truncate (-5 %: 2), round (-5 %: 2)))
         , ((3, 4, 3, 4), (floor (7 %: 2), ceil (7 %: 2), truncate (7 %: 2), round (7 %: 2)))
         , ((0, 1, 0, 0), (floor (1 %: 3), ceil (1 %: 3), truncate (1 %: 3), round (1 %: 3)))
         , ((0, 1, 0, 1), (floor (2 %: 3), ceil (2 %: 3), truncate (2 %: 3), round (2 %: 3)))
         , ((-1, 0, 0, 0), (floor (-1 %: 3), ceil (-1 %: 3), truncate (-1 %: 3), round (-1 %: 3)))
         , ((4, 4, 4, 4), (floor (8 %: 2), ceil (8 %: 2), truncate (8 %: 2), round (8 %: 2))) ]
         id (const (==))
      chk "Rational properFraction"
         [ ("(2, 1 %: 2)", show (properFraction (5 %: 2)))
         , ("(-2, (-1 %: 2))", show (properFraction (-5 %: 2)))
         , ("1 %: 2", show (fract (5 %: 2)))
         , ("0 %: 2", show (fract (4 %: 2))) ]
         id (const (==))
      chk "Rational reduced parts"
         [ ((1, 3), (numerator (2 %: 6), denominator (2 %: 6))), ((-1, 2), (numerator (-3 %: 6), denominator (-3 %: 6))) ]
         id (const (==))
      chk "Rational isInteger and signum"
         [ ((True, False, -1, 0, 1), (isInteger (6 %: 3), isInteger (5 %: 3), signum (-2 %: 3), signum (0 %: 3), signum (2 %: 3))) ]
         id (const (==))
      chk "Rational casts"
         [ ("3 %: 1", show (the Rational (cast (the Nat 3)))), ("(-4 %: 1)", show (the Rational (cast (the Int (-4)))))
         ]
         id (const (==))
      chk "Rational to Double"
         [ (True, the Double (cast (3 %: 4)) == 0.75), (True, the Double (cast (-1 %: 2)) == -0.5), (True, the Double (cast (6 %: 8)) == 0.75) ]
         id (const (==))
      -- the laws of Integer that Data.Integer.Laws believes, tried on a range of values
      let range = the (List Integer) [-6 .. 6]
      let nz = filter (/= 0) range
      let laws =
            [ ("a + b = b + a", \a, b, c => a + b == b + a), ("(a + b) + c = a + (b + c)", \a, b, c => (a + b) + c == a + (b + c))
            , ("a + 0 = a", \a, b, c => a + 0 == a), ("a + negate a = 0", \a, b, c => a + negate a == 0)
            , ("a - b = a + negate b", \a, b, c => a - b == a + negate b), ("a * b = b * a", \a, b, c => a * b == b * a)
            , ("(a * b) * c = a * (b * c)", \a, b, c => (a * b) * c == a * (b * c)), ("a * 1 = a", \a, b, c => a * 1 == a)
            , ("a * (b + c) = a * b + a * c", \a, b, c => a * (b + c) == a * b + a * c)
            , ("natToInteger of a product", \a, b, c => natToInteger (integerToNat (abs a) * integerToNat (abs b)) == abs a * abs b)
            , ("natToInteger (integerToNat (abs a)) = abs a", \a, b, c => natToInteger (integerToNat (abs a)) == abs a)
            , ("abs a = a if not a < 0", \a, b, c => not (a < 0) `implies'` (abs a == a))
            , ("abs a = negate a if a < 0", \a, b, c => (a < 0) `implies'` (abs a == negate a))
            , ("a * c = b * c, c /= 0, then a = b", \a, b, c => (c /= 0 && a * c == b * c) `implies'` (a == b)) ]
      for_ laws $ \(name, law) => do
        let ok = all (\a => all (\b => all (\c => law a b c) range) range) range
        putStrLn ("Integer law " ++ name ++ ": " ++ (if ok then "✓" else "✗ failed"))
