# Delbaen–Schachermayer 閉性定理の Lean 形式化

[English](README.md)

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.22974586.svg)](https://doi.org/10.5281/zenodo.22974586)

Delbaen–Schachermayer の *A General Version of the Fundamental Theorem of Asset Pricing* の
Theorem 4.2 を、有界実数値セミマルチンゲールについて Lean 4 で証明する。
FTAP は Fundamental Theorem of Asset Pricing（資産価格付けの基本定理）の略であり、
ここで形式化する成果はその閉性定理である。

元価格の admissible な一般予測可能積分の終端利得集合を K₀ とし、
C₀ = K₀ − L⁰₊、C = C₀ ∩ L∞ と置く。NFLVR の下で、C₀ の Fatou 閉性と
C の実際の σ(L∞, L¹) 位相での閉性を得る。

Lean では、差し引く剰余の可測性を課さず、生の関数全体で下方包を定める。
概可測な請求権に制限すれば、これは通常の `K₀ − L⁰₊` と一致する。
実際、`g ∈ K₀` と `f ≤ g` a.e. に対して、`g − f` が概可測な非負の剰余となる。
この同値性は [Core/Basic.lean](FTAPTheorem42/Core/Basic.lean) の
`C0AsDifference_iff_measurable_residual` で証明する。概同値類へ移れば通常の
`L⁰` 上の定式化が得られ、`L∞` の錐と NFLVR は変わらない。

```lean
import FTAPTheorem42

#check FTAPTheorem42.BoundedSourceIntegralMarket.theorem42_generalMarket
```

公開定理は [Main.lean](FTAPTheorem42/Main.lean) にある。入力は有界セミマルチンゲールの
source と、その一般積分市場の NFLVR である。source は通常条件、適合した càdlàg な道、
全時間の一様有界性、elementary good-integrator 性を記録する。
終端には利得自身の連続時間での概収束極限を用いる。

Lean の文脈には確率測度と `SigmaFiniteFiltration` も明示される。後者は確率測度で成立する。
source は全経路で càdlàg な代表元を取り、一つの決定論的上界が概至る所で全時刻に共通することを要求する。
Fatou 閉性の定義は共通下界を `−1` に正規化する。錐の正のスカラー倍により、
任意の定数を共通下界とする通常の主張が得られる。

公開する結果は `FTAPTheorem42.BoundedSourceIntegralMarket.theorem42_generalMarket` である。
第一・第二成分からそれぞれ Fatou 閉性・弱スター閉性を取り出せる。
同じ module の `maximal_mem_general_K1` は最大閉包元の実現を与える。
Lean の名前空間 `FTAPTheorem42` は原論文の定理番号を表し、リポジトリ名とは独立である。

完成範囲は有界実数値版 Theorem 4.2 である。多次元版、局所有界版、
同値マルチンゲール測度の存在は別の結果であり、この定理の結論には含めない。

## ビルドと検証

Lean 4.34.0 / mathlib v4.34.0 に固定している。Git と Lean の toolchain manager `elan` を
導入する。監査スクリプトには Python 3 も必要である。次のコマンドで取得・ビルドできる。

```sh
git clone https://github.com/selpoG/lean-ftap-closedness.git
cd lean-ftap-closedness
lake exe cache get
lake build
```

`lake exe cache get` は mathlib のコンパイル済み依存キャッシュを取得する。
この project 自体はソースからビルドする。他の Lake project で利用する場合は、
この Git リポジトリをコミット指定で依存に追加し、`FTAPTheorem42` を import する。

[Task](https://taskfile.dev/) を用いると、検証一式をまとめて実行できる。

```sh
task verify
```

個別のコマンドは次のとおりである。

```sh
python3 scripts/check_structure.py
lake build
lake exe lint-style FTAPTheorem42
python3 scripts/check_declaration_closure.py
lake env lean scripts/AuditProject.lean
python3 scripts/check_analytic_isolation.py
```

依存監査は宣言の型と不透明な証明項も再帰的に調べる。主定理の公理を
`propext`・`Classical.choice`・`Quot.sound` に限定し、公開ライブラリの各ソース宣言が
主定理の依存に寄与することを検査する。自動生成される射影・recursor・補助宣言は
元のソース宣言とまとめて扱う。
数学文書の対応表に記載した宣言についても、存在と主定理への依存を照合する。
主部の証明から確率解析の内部構成を直接使う依存も拒否する。許容する数学的境界は
[モジュール構成](docs/architecture.ja.md) に記載する。
隔離検査では `Stochastic/` を配置せず、正確なインターフェースの型を一時的な仮定に置き換え、
主部の証明を変更せず再ビルドする。通常版ではこれらの入力も証明し、三公理のみの監査を行う。

## 証明とモジュール

最大閉包元の全時間一様な過程極限を構成し、同じ凸平均列のマルチンゲール成分と
有限変動成分を Cauchy にする。その極限を元市場で実現し、Fatou 閉性と弱スター閉性へ渡す。

| 配置 | 役割 |
| --- | --- |
| [Main.lean](FTAPTheorem42/Main.lean) | 最大閉包元の実現と公開主定理。 |
| `Core/`、`PositiveTail/`、`Trading/` | 関数解析、終端利得の凸コンパクト性、閉性。 |
| `Stochastic/Process/`、`Stopping/`、`Predictable/` | 過程の正則性、停止時刻、予測可能性。 |
| `Stochastic/Martingale/`、`FiniteVariation/`、`Decomposition/` | 成分評価とセミマルチンゲールの分解。 |
| `Stochastic/Integral/`、`Topology/`、`Memin/` | 積分構成、位相比較、積分領域の閉性。 |
| `Stochastic/Compactness/`、`DS/`、`Market/`、`Construction/` | 解析的局所化、有限尺度のリスク・尾部・Hahn評価、取引の実現。 |
| `Proof/Selection/`、`Proof/Components/` | DS Lemma 4.5・4.7–4.10：最大性、NFLVRによる矛盾、共通凸化。 |
| `Foundations/` | 過程・停止・変動等の共有定義と基本補題。`Stochastic/` に依存しない。 |
| `Interface/` | 局所化スケジュールや積分 carrier を公開しない、過程と評価による解析的入力。 |
| `Closedness/` | 最大性、FV Cauchy 評価、最大閉包元の実現、二つの閉性。 |

安定した公開入口は `import FTAPTheorem42` である。内部の module path は証明の配置を表し、
保守に伴って変更する場合がある。

数学的証明を [日本語](docs/proof.ja.pdf) と [英語](docs/proof.pdf) で提供する。
どちらも Lean に対応する主証明と確率論の構成を記し、末尾に宣言との対応表を置く。
数学本文では有界な Bichteler–Dellacherie の特徴付けと補償過程の存在定理を基礎結果として明示して引用する。
Lean ではこれらも構成している。[モジュール構成](docs/architecture.ja.md) と
[文書案内](docs/README.ja.md) も参照できる。

両 PDF の再生成には upLaTeX、dvipdfmx、pdfLaTeX を用いる。

```sh
task docs
```

Task を使わず `python3 scripts/build_docs.py` でも生成できる。Debian/Ubuntu では
`texlive-lang-japanese`、`texlive-latex-extra`、`texlive-fonts-recommended`、`lmodern` を用いる。
最終ログの未解決参照と Overfull/Underfull を検査してから PDF を更新する。
CI でも Lean の検証と、この文書ビルドを実行する。

## ライセンスと引用

著者: **Mocho Go**（[selpoG](https://github.com/selpoG)）。
[ORCID: 0009-0000-8123-9408](https://orcid.org/0009-0000-8123-9408).

ソフトウェアとしての引用情報は [CITATION.cff](CITATION.cff) に記載しています。
引用した形式化を再現できるよう、使用したリリースまたは commit を明記してください。

保存済みの **v0.1.1** は
[10.5281/zenodo.22974587](https://doi.org/10.5281/zenodo.22974587) から参照できます。
冒頭の DOI バッジは、このソフトウェアの全バージョンをまとめたレコードを指します。

[Apache License 2.0](LICENSE) の下で公開しています。
