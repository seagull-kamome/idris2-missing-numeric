[![CI](https://github.com/seagull-kamome/idris2-missing-numeric/actions/workflows/ci.yml/badge.svg?branch=master)](https://github.com/seagull-kamome/idris2-missing-numeric/actions/workflows/ci.yml)
[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](LICENSE)

# idris2-missing-numeric

Idris2 の標準ライブラリ（`base` や `contrib`）に含まれていない、実用的かつ重要な数値データ型を提供するライブラリです。

固定小数点数・有理数・複素数・高速累乗・数値フォーマットを提供するだけでなく、各データ型が満たす代数学的性質（可換環の法則や体の公理など）を **Idris2 の型システム上で形式証明** しています。

---

## 主な機能と提供モジュール

| モジュール | 型・機能 | 概要 |
|---|---|---|
| [`Data.Fixed`](src/Data/Fixed.idr) | `Fixed n` | 10進 $n$ 桁の固定小数点数。四則演算、各種丸め（切り捨て・切り上げ・四捨五入）、安全な除算、文字列解析 |
| [`Data.Rational`](src/Data/Rational.idr) | `Rational` | 厳密な有理数（分数）。値に基づく等値・順序比較、約分、四則演算、`Double` 変換 |
| [`Data.Complex`](src/Data/Complex.idr) | `Complex a` | 任意の可換環上の複素数。四則演算、共役、ノルム自乗。`Complex Double` 向けの超越関数・極座標変換 |
| [`Data.Pow`](src/Data/Pow.idr) | `powBy`, `(^^)` | 繰り返し2乗法（バイナリ累乗）による $O(\log n)$ 深度の高速な累乗計算 |
| [`Text.Format.Decimal`](src/Text/Format/Decimal.idr) | `format'`, `zeroPad` | 10進数の桁揃え、ゼロ埋め、符号付き表記などの文字列整形 |
| [`Text.Format.Digits`](src/Text/Format/Digits.idr) | 数字変換 | 数値から各桁の数字列への分解・操作 |

---

## インストールと依存関係

### 要件
- **Idris2** >= 0.5.1
- **依存パッケージ**:
  - `base`
  - `contrib`
  - `elab-util` >= 0.6.0
  - `sop` >= 0.6.0

### pack を使用する場合
`pack.toml` に以下を追加します：

```toml
[custom.all.missing-numeric]
type = "github"
url  = "https://github.com/seagull-kamome/idris2-missing-numeric.git"
commit = "master"
ipkg = "missing-numeric.ipkg"
```

### 手動ビルドする場合
```bash
# パッケージのビルド
idris2 --build missing-numeric.ipkg

# インストール
idris2 --install missing-numeric.ipkg

# テストの実行
make check
```

---

## 使い方とコード例

### 1. 固定小数点数 (`Data.Fixed`)

通貨計算（小数点以下2桁）や高精度タイムスタンプ（ピコ秒: 12桁）など、浮動小数点数の丸め誤差を避けたい計算に最適です。

```idris
import Data.Fixed

-- 小数点以下2桁の型
Centi : Type
Centi = Fixed 2

exampleFixed : IO ()
exampleFixed = do
  -- 文字列からのパース
  let Just price = parseFixed "19.99"
    | Nothing => putStrLn "Parse failed"
  
  -- 四則演算
  let tax = price * 0.10
  putStrLn $ "Tax: " ++ show tax  -- 1.99（切り捨て）
  
  -- 丸め操作
  putStrLn $ "Round: " ++ show (round (price + tax))
  putStrLn $ "Floor: " ++ show (floor (price + tax))
  putStrLn $ "Ceil:  " ++ show (ceiling (price + tax))

  -- 安全な除算（0割りでNothingを返す）
  case divide price 0 of
    Nothing => putStrLn "Division by zero prevented!"
    Just res => putStrLn $ "Result: " ++ show res
```

### 2. 有理数 (`Data.Rational`)

分子 (`num`) と分母 (`den : So (den > 0)`) を保持する厳密な分数です。内部表現は約分されていない状態でも、`Eq` や `Ord` は**数学的な数値として**比較されます。

```idris
import Data.Rational

exampleRational : IO ()
exampleRational = do
  -- スマートコンストラクタ (%:) による生成（分母が正であることの証明 So (d > 0) が自動探索されます）
  let half    = 1 %: 2
  let twoQuar = 2 %: 4
  
  -- 内部表現は異なりますが、数として等しいと判定されます
  printLn (half == twoQuar) -- True
  
  -- 約分 (reduce)
  printLn (reduce twoQuar)  -- 1 %: 2
  
  -- 四則演算と累乗
  let r = (1 %: 3) + (1 %: 6)  -- 1/2
  printLn r
  printLn (r ^^ 3)             -- 1/8
```

### 3. 複素数 (`Data.Complex`)

実部と虚部からなる複素数を扱います。`(:+)` コンストラクタで生成します。

```idris
import Data.Complex

exampleComplex : IO ()
exampleComplex = do
  let z1 = 3.0 :+ 4.0
  let z2 = 1.0 :+ 2.0
  
  -- 演算
  printLn (z1 + z2)        -- 4.0 + 6.0i
  printLn (conjugate z1)   -- 3.0 - 4.0i
  printLn (normSq z1)      -- 25.0
  
  -- Complex Double 向けの高度な関数
  printLn (magnitude z1)   -- 5.0
  printLn (csqrt (-1.0 :+ 0.0)) -- 0.0 + 1.0i
  printLn (polar (magnitude z1) (phase z1))
```

### 4. 高速な累乗 (`Data.Pow`)

標準の再帰的乗算とは異なり、繰り返し2乗法を用いて $O(\log n)$ の再帰深度で累乗を計算します。大きな指数を扱ってもコールスタックが溢れません。

```idris
import Data.Pow

-- 整数・有理数・環の要素を安全かつ高速にべき乗
val : Integer
val = powNum 2 100000  -- スタックオーバーフローせず即座に計算
```

### 5. 数値フォーマット (`Text.Format.Decimal`)

```idris
import Text.Format.Decimal

exampleFormat : IO ()
exampleFormat = do
  -- 4桁ゼロ埋め
  putStrLn $ format' (zeroPad 4) 42   -- "0042"
  
  -- 幅・配置のカスタマイズ
  let fmt = { width := Just 6, pad := Just ' ' } defaultDecimalFormat
  putStrLn $ format fmt (-123)        -- "  -123"
```

---

## 形式証明 (Formal Verification)

本ライブラリでは、実装された演算が満たすべき代数学的法則を定理として定式化し、証明を与えています。

| 証明モジュール | 内容と対象 |
|---|---|
| [`Data.Ring.Laws`](src/Data/Ring/Laws.idr) | 可換環の法則（結合律・交換律・分配律・単位元・零元）を `CommRingLaws t` として定義。証明で頻出する式変形補題を提供 |
| [`Data.Integer.Laws`](src/Data/Integer/Laws.idr) | `Integer` に対する環の法則。組み込みプリミティブ演算であるため `believe_me` で公理化（値の範囲テストで厳密に検査済み） |
| [`Data.Rational.Laws`](src/Data/Rational/Laws.idr) | `Equiv`（有理数の同値関係）が反射律・対称律・推移律を満たすこと、`==` が同値を判定すること、`+`/`*`/`negate` が同値を保つこと、体の公理 |
| [`Data.Complex.Laws`](src/Data/Complex/Laws.idr) | 任意の可換環 `t` 上の複素数が可換環をなすこと。共役の性質、`x * conjugate x = normSq x`、ノルム自乗の乗法性 ($|xy|^2 = |x|^2 |y|^2$) |
| [`Data.Fixed.Laws`](src/Data/Fixed/Laws.idr) | 加法がアーベル群をなすこと、乗法の可換性・単位元・零元、`fromInteger` が環準同型であること |

> [!NOTE]
> **健全性 (Soundness) について**:
> ライブラリ全体で `believe_me` を使用しているのは、Idris2 の組み込みランタイムに依存する `Data.Integer.Laws` と、`Data.Fixed.Laws` の `pow10NonZero`（$10^n \neq 0$）の **2箇所のみ** です。他のすべての証明はこれらのみに依存しており、安全でないキャストや穴は存在しません。

---

## 注意事項・バックエンド依存性

- **固定小数点数の切り捨て**:
  `Fixed` の `*` および `/` は切り捨て（truncate）を行います。そのため、結合律や分配律は厳密には成り立ちません（テストコードに反例があります）。また、負の数で割った場合の丸め規則は各バックエンドの `div` に依存します。
- **0 での除算**:
  `Fixed` の `/` および `recip` は 0 で割るとクラッシュします。安全な計算を行う場合は、`divide` および `recipMaybe` を使用してください。
- **有理数の比較**:
  `Rational` の `Eq` は数値としての比較（クロス乗算）です。分子・分母の内部表現を直接比較したい場合は `num` と `den` を個別に取り出して比較してください。
- **RefC バックエンドにおける Nat の制限**:
  RefC バックエンドでは、$2^{63}$ を超える巨大な `Nat` へのパターンマッチ（`Z` / `S _`）が正常に動かない上流の制限があります。そのため、極端に大きな値に対する `(%?)` や `recipMaybe` が RefC では `Nothing` になる場合があります（Chez Scheme や rc2 バックエンドでは正常に動作します）。
- **`Cast Rational Double`**:
  分子または分母が300桁を超える場合、指数オーバーフローを避けるため双方を同じ10の累乗で除算してから商を計算します（丸め誤差が累積する場合があります）。

---

## ライセンス

本プロジェクトは [MIT License](LICENSE) の下で公開されています。

**作者**: HATTORI, Hiroki ([seagull.kamome@gmail.com](mailto:seagull.kamome@gmail.com))
