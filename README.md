# hall-ray

このレポジトリでは、Lagrange スペクトラムにおける Hall's ray の存在を
Lean 4 と Mathlib で形式化する。目標は、両側無限連分数による
Lagrange スペクトラムの定義を用いて

```math
[6, \infty) \subset L
```

を証明することである。数学的な証明と形式化方針は
[`doc/main.tex`](doc/main.tex) にまとめている。

本レポジトリは、京都大学で行われた集中講義「数学系エンドユーザーのための Lean入門」のコード課題として作成された。

## 形式化の範囲

Lean で証明している最終結果は、正の部分商からなる両側列に対して
`limsup` で定義した `Lagrange.spectrum` についての

```lean
HallRay.hall_ray :
  Set.Ici (6 : ℝ) ⊆ HallRay.Lagrange.spectrum
```

である。これは `doc/main.tex` の定義 1 と定理 $[6,∞) ⊆ L$ に対応する。
Diophantus 近似定数を使う通常の Lagrange スペクトラムとの同値性は文献を
引用しているが、その同値性自体はこのレポジトリでは形式化していない。

また、 $c_F = \inf \{t \in \mathbb{R} | [t,\infty) \subset L\}$ について $[c_F, \infty) \subset L$ となることをいうには、$L$ が閉集合であることも示す必要があるが、その点はまだ形式化していない。

## 問題選定について
上記の $c_F$ は Freiman(1975) によってその値が決定されたため、Freiman の定数と呼ばれている。ところが、その証明は旧ソ連の地方大学の出版物として発行されたため入手性が極めて悪い上に、100ページ以上の長大な計算を伴うため、事実上半世紀以上誰にも検証されていない不健全な情況が続いている。

そこで、我々は現在[verify-freiman-constant](https://github.com/K-Yamada-2002/verify-freiman-constant) で Freiman の定数の検証を進めているが、将来的にはその証明をLeanによって形式化し、その結果を確かなものとすることを目標としている。

その第一歩として本レポジトリで行った Hallによる古典的結果である $[6,\infty) \subset L$ の形式化は意義を持ち、また、今回形式化した連分数に関するいくつかの補題は Lagrange スペクトラムのみならず、広く Diophantus 近似一般における結果の形式化に役立つと考えられる。

## 形式化の方法
形式化にあたって、次のような手順を行った。2. 以降の作業において、CodexとGrok Buildを活用して行った。

1. Hall's rayの存在の証明を書き下す
2. その行間を、可読性を損なわない程度に埋める
3. ドキュメントの構成に対応するLeanファイルを仮で作成する
4. 定義と主結果の形式化を行い、正しい内容が形式化されているか確認する
5. 補題や定理の証明の形式化を行う
6. ドキュメントにLeanファイルとの対応を追記する

## Lean ファイルの構造

```text
HallRay.lean                         ルート import
HallRay/
├── Basic.lean                      プロジェクト共通の Mathlib import
├── ContinuedFraction/
│   ├── Basic.lean                  有限・無限連分数、収束、cylinder 評価
│   └── Mobius.lean                 一次分数変換表示と長さの公式
├── Interval/
│   └── Minkowski.lean              閉区間、有限和、Minkowski 和の一般補題
├── Cantor/
│   ├── Construction.lean           C(4) の再帰的区間除去構成
│   └── Hall.lean                   C(4) + C(4) の区間表示
├── Lagrange/
│   ├── Basic.lean                  λ_i、limsup、Lagrange スペクトラム
│   └── BlockSequence.lean          指定した Lagrange 値を実現する両側列
└── Theorems/
    └── HallRay.lean                最終定理 [6, ∞) ⊆ L
```

直接 import に基づく依存関係は次の向きである
（`Basic.lean` への共通依存は省略）。

```text
ContinuedFraction.Basic ──┬──> ContinuedFraction.Mobius ──> Cantor.Construction
                          │                                      │
                          └──> Lagrange.Basic                    v
                                   │                         Cantor.Hall
                                   v                             │
                           Lagrange.BlockSequence                │
                                   └──────────────┬──────────────┘
                                                  v
                                         Theorems.HallRay

Interval.Minkowski ───────────────────────────> Cantor.Hall
```

## 文書と形式化の対応

`doc/main.tex` と Lean の対応は次のとおりである。

| 数学的対象 | Lean での名前 | ファイル |
|---|---|---|
| 正の部分商と有限語 | `PartialQuotient`, `Word` | [`ContinuedFraction/Basic.lean`](HallRay/ContinuedFraction/Basic.lean) |
| 無限連分数 `[c₀;c₁,c₂,…]` | `ContinuedFraction.value` | [`ContinuedFraction/Basic.lean`](HallRay/ContinuedFraction/Basic.lean) |
| 共通接頭辞を付ける写像 `Φ_w` | `ContinuedFraction.prefixMap` | [`ContinuedFraction/Mobius.lean`](HallRay/ContinuedFraction/Mobius.lean) |
| Minkowski 和 | `Interval.minkowskiSum` | [`Interval/Minkowski.lean`](HallRay/Interval/Minkowski.lean) |
| Cantor 集合 `C(N)` と区間・gap | `Cantor.C`, `T1`–`T3`, `G1`–`G3` | [`Cantor/Construction.lean`](HallRay/Cantor/Construction.lean) |
| `λ_i` と Lagrange スペクトラム `L` | `Lagrange.lambda`, `Lagrange.spectrum` | [`Lagrange/Basic.lean`](HallRay/Lagrange/Basic.lean) |
| `C(4)+C(4)=[√2-1,4√2-4]` | `Cantor.hall_C4` | [`Cantor/Hall.lean`](HallRay/Cantor/Hall.lean) |
| `[6,∞) ⊆ L` | `HallRay.hall_ray` | [`Theorems/HallRay.lean`](HallRay/Theorems/HallRay.lean) |

補題を含む詳しい対応表と、本文の証明から Lean 実装で変更した構成
（gap の有限 forest による処理、anchor を使う疎な両側列）は
[`doc/main.tex`](doc/main.tex) の「Lean 形式化との対応」に記載している。
現在、上表の主結果を含む形式化には `sorry` を残していない。

## ビルドと健全性の確認

Lean 4.32.1 および Mathlib v4.32.1 を使用する。

```sh
lake update
lake build
```


2026年7月24日に作者の環境で、依存関係を含むクリーンビルドを次のコマンドで確認した。
```sh
lake clean
lake update
lake build
```
実行結果：
```sh
Build completed successfully (8665 jobs).
```

また、HallRay/ 以下の形式化には sorry、admit、および本プロジェクトで追加した axiom 宣言が含まれていないことを確認した。
```sh
grep -RInE '\b(sorry|admit|axiom)\b' HallRay
```

文書の PDF は upLaTeX を 2 回実行した後、dvipdfmx で生成できる。

```sh
mkdir -p tmp/doc
uplatex -output-directory=tmp/doc doc/main.tex
uplatex -output-directory=tmp/doc doc/main.tex
dvipdfmx -o doc/main.pdf tmp/doc/main.dvi
```
