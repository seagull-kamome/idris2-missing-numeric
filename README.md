[![CI](https://github.com/seagull-kamome/idris2-missing-numeric/actions/workflows/ci.yml/badge.svg?branch=master)](https://github.com/seagull-kamome/idris2-missing-numeric/actions/workflows/ci.yml)
[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](LICENSE)

# idris2-missing-numeric

A library for Idris 2 providing essential numeric data types that are currently missing from the standard library (`base` and `contrib`).

In addition to providing practical implementations of fixed-point numbers, rational numbers, complex numbers, fast exponentiation, and decimal formatting, this package includes **formal proofs in Idris 2's type system** verifying that these types satisfy fundamental algebraic laws (such as commutative ring and field axioms).

---

## Features & Modules

| Module | Types & Features | Description |
|---|---|---|
| [`Data.Fixed`](src/Data/Fixed.idr) | `Fixed n` | Decimal fixed-point numbers with $n$ decimal digits. Arithmetic, rounding (`floor`, `ceil`, `truncate`, `round`), safe division, parsing |
| [`Data.Rational`](src/Data/Rational.idr) | `Rational` | Exact rational numbers (fractions). Value-based `Eq` and `Ord`, simplification (`reduce`), arithmetic, conversion to `Double` |
| [`Data.Complex`](src/Data/Complex.idr) | `Complex a` | Complex numbers over any commutative ring. Conjugate, norm squared. Transcendental functions and polar conversions for `Complex Double` |
| [`Data.Pow`](src/Data/Pow.idr) | `powBy`, `(^^)` | Exponentiation by squaring with $O(\log n)$ recursion depth to prevent stack overflows |
| [`Text.Format.Decimal`](src/Text/Format/Decimal.idr) | `format'`, `zeroPad` | Decimal number formatting, zero-padding, width, alignment, and sign configurations |
| [`Text.Format.Digits`](src/Text/Format/Digits.idr) | Digits manipulation | Decomposing and converting numbers to and from digit sequences |

---

## Installation & Dependencies

### Requirements
- **Idris 2** >= 0.5.1
- **Dependencies**:
  - `base`
  - `contrib`
  - `elab-util` >= 0.6.0
  - `sop` >= 0.6.0

### Using Pack
Add the following to your `pack.toml`:

```toml
[custom.all.missing-numeric]
type = "github"
url  = "https://github.com/seagull-kamome/idris2-missing-numeric.git"
commit = "master"
ipkg = "missing-numeric.ipkg"
```

### Manual Build
```bash
# Build package
idris2 --build missing-numeric.ipkg

# Install package
idris2 --install missing-numeric.ipkg

# Run tests
make check
```

---

## Usage & Examples

### 1. Fixed-Point Numbers (`Data.Fixed`)

Ideal for calculations where floating-point rounding errors must be avoided, such as currency (2 decimal digits) or high-precision timestamps (e.g., picoseconds with 12 digits).

```idris
import Data.Fixed

-- Type representing 2 decimal places (e.g. cents)
Centi : Type
Centi = Fixed 2

exampleFixed : IO ()
exampleFixed = do
  -- Parse from string
  let Just price = parseFixed "19.99"
    | Nothing => putStrLn "Parse failed"
  
  -- Basic arithmetic
  let tax = price * 0.10
  putStrLn $ "Tax: " ++ show tax  -- 1.99 (truncated)
  
  -- Rounding operations
  putStrLn $ "Round: " ++ show (round (price + tax))
  putStrLn $ "Floor: " ++ show (floor (price + tax))
  putStrLn $ "Ceil:  " ++ show (ceiling (price + tax))

  -- Safe division (returns Nothing on division by zero)
  case divide price 0 of
    Nothing => putStrLn "Division by zero prevented!"
    Just res => putStrLn $ "Result: " ++ show res
```

### 2. Rational Numbers (`Data.Rational`)

Fractions with an integer numerator (`num`) and a strictly positive denominator (`den : So (den > 0)`). Even if two fractions have unreduced internal representations, `Eq` and `Ord` compare them as **mathematical values**.

```idris
import Data.Rational

exampleRational : IO ()
exampleRational = do
  -- Smart constructor (%:) with auto-search proof So (d > 0)
  let half    = 1 %: 2
  let twoQuar = 2 %: 4
  
  -- Different representation, but mathematically equal
  printLn (half == twoQuar) -- True
  
  -- Reduction (reduce)
  printLn (reduce twoQuar)  -- 1 %: 2
  
  -- Arithmetic and powers
  let r = (1 %: 3) + (1 %: 6)  -- 1/2
  printLn r
  printLn (r ^^ 3)             -- 1/8
```

### 3. Complex Numbers (`Data.Complex`)

Complex numbers defined with real and imaginary parts using the `(:+)` constructor.

```idris
import Data.Complex

exampleComplex : IO ()
exampleComplex = do
  let z1 = 3.0 :+ 4.0
  let z2 = 1.0 :+ 2.0
  
  -- Standard operations
  printLn (z1 + z2)        -- 4.0 + 6.0i
  printLn (conjugate z1)   -- 3.0 - 4.0i
  printLn (normSq z1)      -- 25.0
  
  -- Operations on Complex Double
  printLn (magnitude z1)   -- 5.0
  printLn (csqrt (-1.0 :+ 0.0)) -- 0.0 + 1.0i
  printLn (polar (magnitude z1) (phase z1))
```

### 4. Fast Exponentiation (`Data.Pow`)

Computes powers using binary exponentiation (repeated squaring), keeping recursion depth to $O(\log n)$ to avoid stack overflows with large exponents.

```idris
import Data.Pow

-- Quickly and safely compute powers of numbers
val : Integer
val = powNum 2 100000  -- Computes without stack overflow
```

### 5. Decimal Formatting (`Text.Format.Decimal`)

```idris
import Text.Format.Decimal

exampleFormat : IO ()
exampleFormat = do
  -- Zero-padded 4 digits
  putStrLn $ format' (zeroPad 4) 42   -- "0042"
  
  -- Custom width and padding
  let fmt = { width := Just 6, pad := Just ' ' } defaultDecimalFormat
  putStrLn $ format fmt (-123)        -- "  -123"
```

---

## Formal Verification & Proofs

All core numeric operations are formally verified against standard algebraic laws within Idris 2.

| Proof Module | Contents & Verified Properties |
|---|---|
| [`Data.Ring.Laws`](src/Data/Ring/Laws.idr) | Commutative ring laws (associativity, commutativity, distributivity, identities, zero annihilator) defined via `CommRingLaws t` with algebraic rewrites |
| [`Data.Integer.Laws`](src/Data/Integer/Laws.idr) | Ring laws for `Integer`. Stated via minimal `believe_me` because primitive integer arithmetic is built into the runtime (exhaustively checked over test ranges) |
| [`Data.Rational.Laws`](src/Data/Rational/Laws.idr) | Proof that `Equiv` is an equivalence relation, `==` correctly decides `Equiv`, `+`/`*`/`negate` preserve equivalence, and field axioms hold |
| [`Data.Complex.Laws`](src/Data/Complex/Laws.idr) | Proof that `Complex t` forms a commutative ring given any commutative ring `t`. Conjugation laws, $x \cdot \overline{x} = \text{normSq}(x)$, and multiplicativity of squared norm ($|xy|^2 = |x|^2 |y|^2$) |
| [`Data.Fixed.Laws`](src/Data/Fixed/Laws.idr) | Addition forms an Abelian group; multiplication commutativity, identity, and zero annihilator; `fromInteger` is a ring homomorphism |

> [!NOTE]
> **Regarding Soundness**:
> Across the entire package, `believe_me` is used in **only two places**: `Data.Integer.Laws` (due to Idris 2's built-in primitive integer operations) and `pow10NonZero` ($10^n \neq 0$) in `Data.Fixed.Laws`. All other proofs depend solely on these axioms and use no unsafe casts.

---

## Caveats & Backend Specifics

- **Truncation in `Fixed`**:
  `*` and `/` on `Fixed` truncate decimals. Because of truncation, associativity and distributivity do not strictly hold (counterexamples are included in tests). Rounding with negative divisors depends on the backend `div`.
- **Division by Zero**:
  `Fixed` `/` and `recip` crash when dividing by zero. For non-crashing alternatives, use `divide` and `recipMaybe`.
- **Comparison of `Rational`**:
  `Eq` for `Rational` compares numerical value. If you need structural equality of the representation (`MkRational`), compare `num` and `den` explicitly.
- **Nat Pattern Matching in RefC**:
  The RefC backend currently has an upstream limitation where pattern matching on `Nat` greater than $2^{63}$ can fail. Passing huge numbers to `(%?)` or `recipMaybe` might result in `Nothing` on RefC (it works properly on Chez Scheme and rc2).
- **`Cast Rational Double`**:
  If the numerator or denominator exceeds 300 digits, both are scaled down by powers of 10 prior to taking the quotient to avoid floating-point overflow.

---

## License

This project is licensed under the [MIT License](LICENSE).

**Author**: HATTORI, Hiroki ([seagull.kamome@gmail.com](mailto:seagull.kamome@gmail.com))
