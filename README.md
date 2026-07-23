# hall-ray

このレポジトリでは、Lagrange スペクトラムにおける Hall's ray の存在を
Lean 4 と Mathlib で形式化する。目標は、両側無限連分数による
Lagrange スペクトラムの定義を用いて

```text
[6, ∞) ⊆ L
```

を証明することである。数学的な証明と形式化方針は
[`doc/main.tex`](doc/main.tex) にまとめている。

## 形式化の方法
形式化にあたって、次のような手順を行った。2. 以降の作業において、CodexとGrok Buildを活用して行った。

1. Hall's rayの証明を書き下す
2. その行間を可読性を損なわない程度に埋める
3. ドキュメントを元に、中身のない骨組みを作成する
4. 定義と主結果の形式化を行い、正しい内容が形式化されているか確認する
5. 補題や定理の証明の形式化を行う

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

依存関係は概ね次の向きである。

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

## 現在確認できる定義と主結果

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
| `[6,∞) ⊆ L` | `hall_ray` | [`Theorems/HallRay.lean`](HallRay/Theorems/HallRay.lean) |

現在は定義と主定理の型までを実装している。`hall_C4` と `hall_ray` の証明には
意図的に `sorry` を残しており、次の段階で `doc/main.tex` の補題分解に従って
証明を埋める。
