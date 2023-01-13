module Main

import Data.Fixed
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

    testRational : IO ()
    testRational = do
      chk "Rational"
         [ ( "1 %: 5", 2 %: 10 )
         , ( "1 %: 3", 3 %: 9 )
         , ( "-1 %: 3", 3 %: -9 )
         , ( "-1 %: 3", -3 %: 9 )
         , ( "1 %: 3", -3 %: -9 )
         , ( "8 %: 15", (1 %: 3) + (1 %: 5))
         , ( "2 %: 15", (1 %: 3) * (2 %: 5))
         -- , ( "5 %: 6", (1 %: 3) / (2 %: 5))
         -- , ( "3 %: 1", recip (1 %: 3))
         ] show (const (==))
      assertEq LT (compare (2 %: 3) (4 %: 5))
      assertEq EQ (compare (2 %: 3) (4 %: 6))
      assertEq GT (compare (2 %: 3) (5 %: 20))
      assertEq (Just 18) $ floor (55 %: 3)
      assertEq (Just 19) $ ceil (55 %: 3)



