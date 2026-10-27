master: ![workflow/CI](https://github.com/seagull-kamome/idris2-missing-numeric/actions/workflows/ci.yml/badge.svg?branch=master)

# idris2-missing-numeric

標準ライブラリにかけている算術型を実験的に提供します。





## モジュール

| モジュール | 内容 |
|---|---|
| `Data.Fixed` | 固定小数点数 `Fixed n`(10 進 n 桁)。切り捨て・丸め、`Double` や桁数の変換、`parseFixed`、0 割りしない除算、`pow` |
| `Data.Rational` | 有理数。表現は約分しない(`1 %: 2` と `2 %: 4` は別の表現)が、`Eq`/`Ord` は数として比べる。除算、累乗、`floor`/`ceil`/`truncate`/`round` |
| `Data.Complex` | 複素数。除算、`normSq`、累乗。`Complex Double` には `magnitude`/`phase`/`polar`/`cexp`/`clog`/`csqrt`/`cpow` |
| `Data.Pow` | 繰り返し 2 乗法の累乗(`powBy`、`powNum`、`^^`)。指数に比例する深さの再帰を使わない |
| `Text.Format.Decimal` | 10 進数の整形 |

## 証明

演算が従う法則は型の中で証明してあります。

- `Data.Ring.Laws` — 可換環の法則を `CommRingLaws t` として表し、証明でよく使う式変形をまとめたもの。
- `Data.Integer.Laws` — `Integer` の環の法則など。`Integer` の演算は組み込みで、言語の中で証明できないため、ここだけ `believe_me` で述べてあります(contrib の `Data.Int.Order` と同じ扱い)。どの法則もただの整数の事実で、`test/Main.idr` が値の範囲で確かめます。**`believe_me` を使うのは、ここと `Data.Fixed.Laws` の `pow10NonZero`(10 の累乗は 0 でない)の 2 か所だけです。このパッケージの他の証明は、これらだけに依存し、他に安全でないものを使いません。**
- `Data.Rational.Laws` — `Equiv`(同じ数)が同値関係であること、`==` がそれを判定すること、`+` `*` `negate` がそれを保つこと、体の法則(結合・交換・単位元・逆元・分配)。
- `Data.Complex.Laws` — `CommRingLaws t` を満たす任意の `t` 上で、複素数が可換環であること。共役の性質、`x * conjugate x` と `normSq x`、`normSq` が積を保つこと。
- `Data.Fixed.Laws` — 加法がアーベル群であること、`*` の可換性・単位元・零元、`fromInteger` が和と積を保つこと。`*` と `/` は切り捨てるので結合律・分配律は成り立ちません(テストに反例があります)。

## 注意

- `Fixed` の `*` と `/` は切り捨てます。除数が負のときの `Integer` の `div` の丸め方は、バックエンドのものです(除数が正なら、どのバックエンドでも切り捨て)。
- `Fixed` の `/` と `recip` は、0 で割ると止まります。止まらない版は `divide` と `recipMaybe` です。
- `Rational` の `Eq` は、以前は表現の比較でしたが、数の比較になりました。表現(`MkRational` の中身)の比較が要るときは、`num` と `den` を直接比べます。
- `Complex` の `Show` は `real + imag i` の順です(以前は逆でした)。`Data.Complex.Laws` の証明は、以前の(穴のあった)implicit 仮定の形とは別の述べ方です。
- RefC では、2^63 を超える `Nat` へのパターンマッチ(`Z` / `S _`)が正しく動かないことがあり(上流の制限)、`(%?)` や `recipMaybe` に巨大な数を渡すと `Nothing` になりました。Chez と rc2 では正しく動きます。
- `Cast Rational Double` は、分子か分母が 300 桁を超えると、両方を同じ 10 の累乗で割ってから商を取ります(丸めが重なります)。`Complex Double` の `phase` は、虚部が負のゼロのときも正のゼロとして扱います。
