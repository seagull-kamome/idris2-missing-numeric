module Main

import Data.Nat  -- for NonZero
import Data.List
import Data.Maybe
import Data.Fixed
import Data.Fixed.Laws
import Data.Pow
import Data.Complex
import Data.Rational
import Text.Format.Decimal
import Text.Format.Digits
import System
import System.Info
import Data.IORef

-- a failure is shown and counted: the exit status of the program tells it
Failures : Type
Failures = IORef Nat

assertEq : Show a => Eq a => Failures -> a -> a -> IO ()
assertEq fails x y with (x == y)
  _ | True  = putStr "✓"
  _ | False = putStrLn ("\n  ✗ expected=" ++ show x ++ " actual=" ++ show y) >> modifyIORef fails S

implies' : Bool -> Lazy Bool -> Bool
implies' p q = not p || q

chk : (Show a, Show b) => Failures -> String -> List (a, b) -> (b -> a) -> (b -> a -> a -> Bool) -> IO ()
chk fails dsc xs f g = do
  putStr (dsc ++ ": ")
  for_ xs $
    \xs@(e, x) => do
      let ans = f x
      if g x e ans
         then putStr "✓"
         else putStrLn ("\n  ✗ test=" ++ show xs ++ " ans=" ++ show ans) >> modifyIORef fails S
  putStrLn ""


partial main : IO ()
main = do
  putStrLn $ "Codegen : \{System.Info.codegen}"
  fails <- newIORef 0
  testTextFormat fails >> testDigits fails >> testComplex fails >> testFixed fails >> testRational fails
  n <- readIORef fails
  if n == 0 then putStrLn "all passed" else putStrLn (show n ++ " failed") >> exitFailure
  where
    testTextFormat : Failures -> IO ()
    testTextFormat fails = do
      do
        let fmt00 = { width := Just 4, prec := Just 0, pad := Nothing,
                      spc := ' ', point := '.',
                      minus := Just (Left "-"), plus := Nothing } defaultDecimalFormat
        chk fails "Text format (Int + Width)"
            [ ("   0", 0), ("   1", 1), ("  10", 10), (" -10", -10)
            , ("-999", -999), (" 999", 999), ("1234", 1234), ("-1234", -1234)
            , ("99999", 99999) ]
            (format fmt00) (const (==))
      do
        let fmt00 = { width := Nothing, prec := Just 0, pad := Nothing,
                      spc := ' ', point := '.',
                      minus := Just (Left "-"), plus := Nothing } defaultDecimalFormat
        chk fails "Text format (Int + no width)"
            [ ("0", 0), ("1", 1), ("10", 10), ("-10", -10), ("-999", -999)
            , ("999", 999), ("1234", 1234), ("-1234", -1234), ("99999", 99999) ]
            (format fmt00) (const (==))
      do
        chk fails "Text format (Fixed + precision)"
            [ ("1.500", format' (\f => { prec := Just 3 } f) (the (Fixed 2) (MkFixed 150)))
            , ("1.5", format' (\f => { prec := Just 1 } f) (the (Fixed 12) (MkFixed 1500000000000)))
            , ("1.50000", format' (\f => { prec := Just 5 } f) (the (Fixed 3) (MkFixed 1500)))
            , ("-0.250", format' (\f => { prec := Just 3 } f) (the (Fixed 2) (MkFixed (-25)))) ]
            id (const (==))
      do
        let fmt00 = { width := Just 4, prec := Just 0, pad := Nothing,
                      spc := ' ', point := '.',
                      minus := Just (Left "-"), plus := Just (Left "+") } defaultDecimalFormat
        chk fails "Text format (Int + Width and PlusSign"
            [ ("  +0", 0), ("  +1", 1), ("+123", 123), ("+1234", 1234) ]
            (format fmt00) (const (==))

      do
        let fmt00 = { width := Just 4, prec := Just 0, pad := Nothing,
                      spc := ' ', point := '.',
                      minus := Just (Right "-"), plus := Nothing } defaultDecimalFormat
        chk fails "Text format (Int + TailingSign)"
            [ ("   0", 0), ("   1-", -1), (" 123-", -123), ("1234-", -1234) ]
            (format fmt00) (const (==))

      do
        let fmt00 = { width := Just 4, prec := Just 0, pad := Just '0',
                      spc := ' ', point := '.',
                      minus := Just (Left "-"), plus := Nothing } defaultDecimalFormat
        chk fails "Text format (Int + Padding)"
            [ ("0000", 0), ("-0001", -1), ("-0123", -123), ("-1234", -1234) ]
            (format fmt00) (const (==))

      do
        let fmt00 = { width := Nothing, prec := Just 0, pad := Just '0',
                      spc := ' ', point := '.',
                      minus := Just (Left "-"), plus := Nothing } defaultDecimalFormat
        chk fails "Text format (Int + no width + padding)"
            [ ("0", 0), ("-1", -1), ("-123", -123), ("-1234", -1234) ]
            (format fmt00) (const (==))

      do
        let fmt00 = { width := Just 4, prec := Nothing, pad := Nothing,
                      spc := ' ', point := '.',
                      minus := Just (Left "-"), plus := Nothing } defaultDecimalFormat
        chk fails "Text format (Fixed + Width)"
            [("   0.000000000000", the (Fixed 12) 0),
             ("   1.000000000000", 1), (" -10.000000000000", -10) ]
            (format fmt00) (const (==))

    testDigits : Failures -> IO ()
    testDigits fails = do
      -- the base is given twice: `Digits base` is a String, which does not tell it
      let hex = intToDigits {base=16} lowerHexdigits
          unhex = digitsToInt {base=16} lowerHexdigits
      chk fails "Digits, intToDigits"
          [ ("3e7", hex 999), ("3E7", intToDigits {base=16} upperHexdigits 999)
          , ("13", intToDigits {base=8} (upperAlnumDigits {base=8}) 11), ("0", hex 0)
          , ("-ff", hex (-255)), ("101", intToDigits {base=2} (lowerAlnumDigits {base=2}) 5)
          , ("z", intToDigits {base=36} (lowerAlnumDigits {base=36}) 35), ("10", intToDigits {base=36} (lowerAlnumDigits {base=36}) 36)
          , ("1", intToDigits {base=2} (lowerAlnumDigits {base=2}) 1)
          , ("9223372036854775807", intToDigits {base=10} (lowerAlnumDigits {base=10}) 9223372036854775807) ]
          id (const (==))
      chk fails "Digits, digitsToInt"
          [ (Just 999, unhex "3e7"), (Just (-255), unhex "-ff")
          , (Just 26, digitsToInt {base=16} upperHexdigits "1A"), (Nothing, unhex "g")
          , (Nothing, unhex ""), (Just 0, unhex "0") ]
          id (const (==))
      let b7 = lowerAlnumDigits {base=7}
          b36 = lowerAlnumDigits {base=36}
      chk fails "Digits, the two agree"
          [ (True, all (\n => unhex (hex n) == Just n) [-300 .. 300])
          , (True, all (\n => digitsToInt {base=7} b7 (intToDigits {base=7} b7 n) == Just n) [-300 .. 300])
          , (True, all (\n => digitsToInt {base=36} b36 (intToDigits {base=36} b36 n) == Just n) [-5000, -1234, 99999, 1234567890]) ]
          id (const (==))

    testComplex : Failures -> IO ()
    testComplex fails = do
      chk fails "Complex Eq"
          [ (True, (MkComplex 0 1, MkComplex 0 1))
          , (False, (MkComplex 1 1, MkComplex 0 1)) ]
          (uncurry (==)) (const (==))
      -- over Integer: ring operations, the conjugate, the square of the magnitude
      chk fails "Complex Integer"
          [ ("3 + 7i", show (the (Complex Integer) (MkComplex 1 2 + MkComplex 2 5)))
          , ("-5 + 10i", show (the (Complex Integer) (MkComplex 1 2 * MkComplex 3 4)))
          , ("-1 + -1i", show (the (Complex Integer) (MkComplex 1 2 - MkComplex 2 3)))
          , ("-2 + -3i", show (the (Complex Integer) (negate (MkComplex 2 3))))
          , ("2 + -3i", show (conjugate (the (Complex Integer) (MkComplex 2 3))))
          , ("13", show (normSq (the (Complex Integer) (MkComplex 2 3))))
          , ("-1 + 0i", show (imaginaryUnit * the (Complex Integer) imaginaryUnit))
          , ("7 + 0i", show (the (Complex Integer) 7))
          , ("4 + 0i", show (the (Complex Integer) (fromReal 4)))
          , ("-5 + 12i", show (pow (the (Complex Integer) (MkComplex 2 3)) 2))
          , ("-46 + 9i", show (pow (the (Complex Integer) (MkComplex 2 3)) 3))
          , ("1 + 0i", show (pow (the (Complex Integer) (MkComplex 2 3)) 0))
          , ("65 + 0i", show (mulC (MkComplex 2 3 + MkComplex 0 0) (conjugate (MkComplex 2 3)) * MkComplex 5 0))
          ] id (const (==))
      chk fails "Complex isReal, isImaginary"
          [ (True, isReal (the (Complex Integer) (MkComplex 4 0))), (False, isReal (the (Complex Integer) (MkComplex 4 1)))
          , (True, isImaginary (the (Complex Integer) (MkComplex 0 1))), (True, isImage (the (Complex Integer) (MkComplex 0 9))) ]
          id (const (==))
      -- the laws, tried on values: the proofs hold for every ring; here one of them against the arithmetic
      let zs = [ MkComplex a b | a <- the (List Integer) [-2 .. 2], b <- [-2 .. 2] ]
      chk fails "Complex laws on values"
          [ (True, all (\(x, y) => x + y == y + x) [ (x, y) | x <- zs, y <- zs ])
          , (True, all (\(x, y) => x * y == y * x) [ (x, y) | x <- zs, y <- zs ])
          , (True, all (\(x, y, z) => (x * y) * z == x * (y * z)) [ (x, y, z) | x <- take 9 zs, y <- take 9 (drop 8 zs), z <- take 9 (drop 16 zs) ])
          , (True, all (\(x, y, z) => x * (y + z) == x * y + x * z) [ (x, y, z) | x <- take 9 zs, y <- take 9 (drop 8 zs), z <- take 9 (drop 16 zs) ])
          , (True, all (\(x, y) => normSq (x * y) == normSq x * normSq y) [ (x, y) | x <- zs, y <- zs ])
          , (True, all (\(x, y) => conjugate (x * y) == conjugate x * conjugate y) [ (x, y) | x <- zs, y <- zs ])
          , (True, all (\x => x * conjugate x == MkComplex (normSq x) 0) zs) ]
          id (const (==))
      -- division over a type with division: Fixed
      chk fails "Complex over Fixed"
          [ ("0.4400 + 0.0800i", show (the (Complex (Fixed 4)) (MkComplex 1 2) / MkComplex 3 4))
          , ("0.2000 + -0.4000i", show (recip (the (Complex (Fixed 4)) (MkComplex 1 2))))
          , ("1.0000 + 0.0000i", show (the (Complex (Fixed 4)) (MkComplex 1 2) / MkComplex 1 2))
          , ("0.2000 + -0.4000i", show (the (Complex (Fixed 4)) (MkComplex 1 2) ^^ (-1))) ]
          id (const (==))
      -- Double: magnitude, angle, polar form and what depends on them
      let near : Double -> Double -> Bool
          near a b = abs (a - b) < 1.0e-9
          nearC : Complex Double -> Complex Double -> Bool
          nearC a b = near a.real b.real && near a.imag b.imag
      chk fails "Complex magnitude of large and small parts"
         [ (True, abs (magnitude (MkComplex 3.0e200 4.0e200) / 5.0e200 - 1) < 1.0e-12)
         , (True, abs (magnitude (MkComplex 3.0e-200 4.0e-200) / 5.0e-200 - 1) < 1.0e-12)
         , (True, magnitude (MkComplex 0 0) == 0), (True, magnitude (MkComplex (-3) 0) == 3) ]
         id (const (==))
      chk fails "Complex Double"
          [ (True, near (magnitude (MkComplex 3 4)) 5), (True, near (phase (MkComplex 1 1)) (pi / 4))
          , (True, near (phase (MkComplex (-1) 0)) pi), (True, near (phase (MkComplex 0 (-1))) (negate pi / 2))
          , (True, near (phase (MkComplex 0 0)) 0), (True, near (phase (MkComplex (-1) (-1))) (negate (3 * pi / 4)))
          , (True, nearC (mkPolar 2 (pi / 2)) (MkComplex 0 2)), (True, nearC (cis pi) (MkComplex (-1) 0))
          , (True, let (r, t) = polar (MkComplex (-3) 4) in nearC (mkPolar r t) (MkComplex (-3) 4))
          , (True, nearC (cexp (MkComplex 0 pi)) (MkComplex (-1) 0))
          , (True, nearC (cexp (MkComplex 1 0)) (MkComplex euler 0))
          , (True, nearC (clog (MkComplex (-1) 0)) (MkComplex 0 pi))
          , (True, nearC (cexp (clog (MkComplex 3 4))) (MkComplex 3 4))
          , (True, nearC (csqrt (MkComplex (-4) 0)) (MkComplex 0 2))
          , (True, nearC (csqrt (MkComplex 3 4)) (MkComplex 2 1))
          , (True, nearC (mulC (csqrt (MkComplex 5 12)) (csqrt (MkComplex 5 12))) (MkComplex 5 12))
          , (True, nearC (cpow (MkComplex 0 1) (MkComplex 2 0)) (MkComplex (-1) 0))
          , (True, nearC (MkComplex 1 2 / MkComplex 3 4) (MkComplex 0.44 0.08))
          , (True, nearC (pow (MkComplex 1 1) 8) (MkComplex 16 0))
          , (True, nearC (MkComplex 1 1 ^^ (-2)) (MkComplex 0 (-0.5))) ]
          id (const (==))

    testFixed : Failures -> IO ()
    testFixed fails = do
      chk fails "Fixed"
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
      chk fails "Powers of ten"
         [ (True, n) | n <- [0 .. 60] ]
         (\n => pow10 n == powBy (*) 1 10 n && pow10 n == natToInteger (the Nat 10 `power` n)) (const (==))
      -- powBy itself: exponents 0, 1, 2, powers of two, odd and even, and strings (the count of factors)
      chk fails "powBy"
         [ (1, powBy (*) 1 (the Integer 7) 0), (7, powBy (*) 1 (the Integer 7) 1), (49, powBy (*) 1 (the Integer 7) 2)
         , (2401, powBy (*) 1 (the Integer 7) 4), (343, powBy (*) 1 (the Integer 7) 3), (16807, powBy (*) 1 (the Integer 7) 5)
         , (1024, powBy (*) 1 (the Integer 2) 10), (1073741824, powBy (*) 1 (the Integer 2) 30) ]
         id (const (==))
      let cat = \a, b => a ++ the String b
      chk fails "powBy on strings"
         [ ("", powBy cat "" "ab" 0), ("ab", powBy cat "" "ab" 1), ("abab", powBy cat "" "ab" 2)
         , ("ababab", powBy cat "" "ab" 3), ("ababababab", powBy cat "" "ab" 5), (fastConcat (replicate 13 "xy"), powBy cat "" "xy" 13) ]
         id (const (==))
      chk fails "Fixed with many digits"
         [ ("1.000000000000000000000000000000000000000000", the (Fixed 42) 1)
         , ("0.333333333333333333333333333333333333333333", recip 3)
         , ("2.500000000000000000000000000000000000000000", the (Fixed 42) 5 / 2)
         , ("0.000000000000000000000000000000000000000001", MkFixed 1)
         ] show (const (==))
      -- powers: small, zero, negative, large (a loop, no deep recursion). The values
      -- for 100000 and 1000000 are what the rounding of this order of products gives
      -- (the true powers are 1.0001000050001 and 1.0010005001667): they pin the
      -- behaviour down, they are not derived.
      chk fails "Fixed pow and ^^"
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
      chk fails "Fixed and Rational"
         [ ("Just 0.250000000000", show (the (Maybe (Fixed 12)) (cast (1 %: 4))))
         , ("Just 0.333333333333", show (the (Maybe (Fixed 12)) (cast (2 %: 6))))
         , ("Just -0.500000000000", show (the (Maybe (Fixed 12)) (cast ((-1) %: 2))))
         , ("25 %: 100", show (the Rational (cast (the (Fixed 2) (MkFixed 25)))))
         ] id (const (==))

      let f1 = \k => the (Fixed 1) (MkFixed k)
      let f2 = \k => the (Fixed 2) (MkFixed k)
      -- whole numbers and fractions
      chk fails "Fixed whole part"
         [ ((2, 3, 2, 2), (floor (f1 25), ceil (f1 25), truncate (f1 25), round (f1 25)))
         , ((-3, -2, -2, -2), (floor (f1 (-25)), ceil (f1 (-25)), truncate (f1 (-25)), round (f1 (-25))))
         , ((3, 4, 3, 4), (floor (f1 35), ceil (f1 35), truncate (f1 35), round (f1 35)))
         , ((0, 1, 0, 0), (floor (f1 3), ceil (f1 3), truncate (f1 3), round (f1 3)))
         , ((-1, 0, 0, 0), (floor (f1 (-3)), ceil (f1 (-3)), truncate (f1 (-3)), round (f1 (-3))))
         , ((4, 4, 4, 4), (floor (f1 40), ceil (f1 40), truncate (f1 40), round (f1 40))) ]
         id (const (==))
      chk fails "Fixed properFraction"
         [ ("(2, 0.5)", show (properFraction (f1 25))), ("(-2, -0.5)", show (properFraction (f1 (-25)))), ("0.0", show (fract (f1 40))) ]
         id (const (==))
      -- another count of digits, from a natural number and a Double, to a Double
      chk fails "Fixed resize and casts"
         [ ("1.23", show (the (Fixed 2) (resize (the (Fixed 4) (MkFixed 12345)))))
         , ("-1.24", show (the (Fixed 2) (resize (the (Fixed 4) (MkFixed (-12345))))))
         , ("1.23000", show (the (Fixed 5) (resize (f2 123))))
         , ("7.00", show (the (Fixed 2) (cast (the Nat 7))))
         , ("0.13", show (the (Fixed 2) (cast (the Double 0.125)))), ("-0.13", show (the (Fixed 2) (cast (the Double (-0.125)))))
         , ("2.50", show (the (Fixed 2) (cast (the Double 2.5)))) ]
         id (const (==))
      let nan = 0.0 / 0.0
      let inf = 1.0 / 0.0
      chk fails "Fixed fromDouble"
         [ ("Just 1.50", show (fromDouble {n=2} 1.5)), ("Nothing", show (fromDouble {n=2} nan)), ("Nothing", show (fromDouble {n=2} inf))
         , ("Nothing", show (fromDouble {n=2} (negate inf))), ("Nothing", show (fromDouble {n=400} 1.0))
         , ("0.00", show (the (Fixed 2) (cast nan))), ("0.00", show (the (Fixed 2) (cast inf))) ]
         id (const (==))
      chk fails "Fixed to Double"
         [ (True, the Double (cast (f2 125)) == 1.25), (True, the Double (cast (f2 (-5))) == -0.05) ]
         id (const (==))
      -- division that cannot stop the program
      chk fails "Fixed divide, recipMaybe, divMod'"
         [ ("Just 0.25", show (divide (the (Fixed 2) 1) 4)), ("Nothing", show (divide (the (Fixed 2) 1) 0))
         , ("Nothing", show (recipMaybe (the (Fixed 2) 0))), ("Just 0.25", show (recipMaybe (the (Fixed 2) 4)))
         , ("(3, 1.5)", show (divMod' (f1 75) (f1 20))), ("(-4, 0.5)", show (divMod' (f1 (-75)) (f1 20))) ]
         id (const (==))
      chk fails "Fixed parseFixed"
         [ ("Just 12.34", show (parseFixed {n=2} "12.34")), ("Just -0.50", show (parseFixed {n=2} "-0.5"))
         , ("Just 7.00", show (parseFixed {n=2} "7")), ("Just 0.50", show (parseFixed {n=2} ".5")), ("Just 3.10", show (parseFixed {n=2} "+3.1"))
         , ("Just 0.05", show (parseFixed {n=2} "0.05"))
         , ("Nothing", show (parseFixed {n=2} "1.234")), ("Nothing", show (parseFixed {n=2} "abc")), ("Nothing", show (parseFixed {n=2} ""))
         , ("Nothing", show (parseFixed {n=2} "-")), ("Nothing", show (parseFixed {n=2} "1.2.3"))
         , ("Nothing", show (parseFixed {n=2} ".")), ("Nothing", show (parseFixed {n=2} "+.")), ("Nothing", show (parseFixed {n=2} "-."))
         , ("Just 5.00", show (parseFixed {n=2} "5.")), ("Just 0", show (parseFixed {n=0} "0")) ]
         id (const (==))
      -- laws: addition is exact, multiplication is rounded down
      let fs = map f2 [-20 .. 20]
      chk fails "Fixed laws on values"
         [ (True, all (\(x, y) => x + y == y + x) [ (x, y) | x <- fs, y <- fs ])
         , (True, all (\(x, y, z) => (x + y) + z == x + (y + z)) [ (x, y, z) | x <- take 9 fs, y <- take 9 (drop 9 fs), z <- take 9 (drop 18 fs) ])
         , (True, all (\x => x + 0 == x && x + negate x == 0 && x - x == 0) fs)
         , (True, all (\(x, y) => x * y == y * x) [ (x, y) | x <- fs, y <- fs ])
         , (True, all (\x => x * 1 == x && x * 0 == 0) fs)
         , (True, all (\ab => the (Fixed 2) (fromInteger (fst ab + snd ab)) == fromInteger (fst ab) + fromInteger (snd ab)) [ (a, b) | a <- the (List Integer) [-9 .. 9], b <- the (List Integer) [-9 .. 9] ])
         , (True, all (\ab => the (Fixed 2) (fromInteger (fst ab * snd ab)) == fromInteger (fst ab) * fromInteger (snd ab)) [ (a, b) | a <- the (List Integer) [-9 .. 9], b <- the (List Integer) [-9 .. 9] ])
         , (True, all (\n => pow10 n /= 0) [0 .. 200])
         -- the rounding: * is not associative, and does not distribute over +
         , (False, (f1 9 * f1 9) * f1 2 == f1 9 * (f1 9 * f1 2))
         , (False, f1 5 * (f1 1 + f1 1) == f1 5 * f1 1 + f1 5 * f1 1) ]
         id (const (==))

    testRational : Failures -> IO ()
    testRational fails = do
      chk fails "Rational"
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
      assertEq fails LT (compareAsReal (2 %: 3) (4 %: 5))
      assertEq fails EQ (compareAsReal (2 %: 3) (4 %: 6))
      assertEq fails GT (compareAsReal (2 %: 3) (5 %: 20))
      assertEq fails 18 $ floor (55 %: 3)
      assertEq fails 19 $ ceil (55 %: 3)



      -- Eq and Ord compare the numbers, not the representations
      chk fails "Rational Eq/Ord"
         [ (True, (1 %: 2) == (2 %: 4)), (False, (1 %: 2) == (1 %: 3)), (True, (-1 %: 2) == (-2 %: 4))
         , (True, (1 %: 3) < (1 %: 2)), (True, (-1 %: 2) < (-1 %: 3)), (False, (2 %: 4) < (1 %: 2)), (True, (2 %: 4) <= (1 %: 2))
         , (True, max (1 %: 3) (1 %: 2) == (1 %: 2)), (True, compare (2 %: 3) (4 %: 6) == EQ) ]
         id (const (==))
      -- the reciprocal keeps the sign; division; powers
      chk fails "Rational recip, division, powers"
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
      chk fails "Rational whole part"
         [ ((2, 3, 2, 2), (floor (5 %: 2), ceil (5 %: 2), truncate (5 %: 2), round (5 %: 2)))
         , ((-3, -2, -2, -2), (floor (-5 %: 2), ceil (-5 %: 2), truncate (-5 %: 2), round (-5 %: 2)))
         , ((3, 4, 3, 4), (floor (7 %: 2), ceil (7 %: 2), truncate (7 %: 2), round (7 %: 2)))
         , ((0, 1, 0, 0), (floor (1 %: 3), ceil (1 %: 3), truncate (1 %: 3), round (1 %: 3)))
         , ((0, 1, 0, 1), (floor (2 %: 3), ceil (2 %: 3), truncate (2 %: 3), round (2 %: 3)))
         , ((-1, 0, 0, 0), (floor (-1 %: 3), ceil (-1 %: 3), truncate (-1 %: 3), round (-1 %: 3)))
         , ((4, 4, 4, 4), (floor (8 %: 2), ceil (8 %: 2), truncate (8 %: 2), round (8 %: 2))) ]
         id (const (==))
      chk fails "Rational properFraction"
         [ ("(2, 1 %: 2)", show (properFraction (5 %: 2)))
         , ("(-2, (-1 %: 2))", show (properFraction (-5 %: 2)))
         , ("1 %: 2", show (fract (5 %: 2)))
         , ("0 %: 2", show (fract (4 %: 2))) ]
         id (const (==))
      chk fails "Rational reduced parts"
         [ ((1, 3), (numerator (2 %: 6), denominator (2 %: 6))), ((-1, 2), (numerator (-3 %: 6), denominator (-3 %: 6))) ]
         id (const (==))
      chk fails "Rational isInteger and signum"
         [ ((True, False, -1, 0, 1), (isInteger (6 %: 3), isInteger (5 %: 3), signum (-2 %: 3), signum (0 %: 3), signum (2 %: 3))) ]
         id (const (==))
      chk fails "Rational casts"
         [ ("3 %: 1", show (the Rational (cast (the Nat 3)))), ("(-4 %: 1)", show (the Rational (cast (the Int (-4)))))
         ]
         id (const (==))
      -- a quotient of numbers that a Double cannot hold is not a NaN
      chk fails "Rational to Double, large parts"
         [ (True, let d = toDouble (pow (2 %: 3) 2000) in d == d && d >= 0 && d < 1.0e-300)
         , (True, abs (toDouble (multR (pow (10 %: 1) 400) (pow (1 %: 10) 399)) - 10) < 1.0e-9)
         , (True, abs (toDouble (multR (pow (-10 %: 1) 401) (pow (1 %: 10) 399)) + 100) < 1.0e-9)
         , (True, let d = toDouble (1 %: 3) in abs (d - 0.3333333333333333) < 1.0e-15) ]
         id (const (==))
      chk fails "Rational to Double"
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
            , ("a * c = b * c, c /= 0, then a = b", \a, b, c => (c /= 0 && a * c == b * c) `implies'` (a == b))
            , ("(a * c) div c = a, c /= 0", \a, b, c => (c /= 0) `implies'` ((a * c) `div` c == a))
            , ("0 div c = 0, c /= 0", \a, b, c => (c /= 0) `implies'` (the Integer 0 `div` c == 0)) ]
      for_ laws $ \(name, law) => do
        let ok = all (\a => all (\b => all (\c => law a b c) range) range) range
        putStrLn ("Integer law " ++ name ++ ": " ++ (if ok then "✓" else "✗ failed"))
        unless ok (modifyIORef fails S)
