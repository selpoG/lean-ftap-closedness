# モジュール構成

[English](architecture.md)

公開入口は `import FTAPTheorem42` である。主定理は
[Main.lean](../FTAPTheorem42/Main.lean) の
`FTAPTheorem42.BoundedSourceIntegralMarket.theorem42_generalMarket` である。
内部のパスは証明を整理するためのものであり、個別の互換 API としては扱わない。

## 主部と解析付録

| 層 | 数学上の役割 |
| --- | --- |
| `PositiveTail/`、`Trading/`、`Core/` | 前方凸結合のコンパクト性（DS A1.1・Proposition 3.1）、最大元（4.3）、Fatou 閉性の判定、弱スター閉性。 |
| `Proof/Selection/` | 終端下界からの全時刻下界制御、最初に差が生じる時刻での貼り合わせ、最大候補に対応する一様過程極限（4.5）。 |
| `Proof/Components/` | 添字付き利得族に対する NFLVR 矛盾（4.7）、尾部の正規化による矛盾（4.8）、全 test に共通する閾値（4.9）、共通の Hilbert 凸化（4.10）。 |
| `Proof/OrientedSequence.lean` | 元の利得、成分の凸重み、一様極限、終端を同じものに保ち、有限時間の Hahn 改善を組み立てる。 |
| `Closedness/`、`Main.lean` | Hahn 改善を最大性の矛盾に使い（4.11）、FV Cauchy 評価、最大終端利得の実現、二つの閉性を導く。 |
| `Interface/` | 主部が使用する、過程と評価で記述された解析入力。通常版では全て証明する。 |
| `Stochastic/` | 分解、補償、積分構成、局所化、位相比較、有限尺度のリスク・尾部・Hahn 評価。 |
| `Foundations/` | 共有する具体的な定義と、確率・過程・停止・変動・凸性の基本補題。解析実装やインターフェースを import しない。 |

主部は列と凸重みを選び、Cauchy 性を証明する。これらの結論を解析側の仮定として受け取らない。
解析実装は `Proof/`、`Closedness/`、`Main.lean` を import しない。
一部の実装モジュールは、具体的なインターフェースの record を import してその値を構成する。
モジュールの依存関係に循環はない。

`Proof/Components/ClassBoundedness`・`TailBoundedness`・`TailTests` は、DS Lemma 4.7・4.8・4.9の
一般の矛盾・評価と、元価格の市場での適用をそれぞれ同じモジュールにまとめる。
共有する型や解析入力は、小さくても依存境界として独立させる。

## 数学的な接続点

日英の証明解説は、同じ数学的境界を記述する。
宣言対応表には、主部の議論と解析入力の対応箇所を載せている。

| 数学的な入力 | インターフェースのモジュール |
| --- | --- |
| 正則経路の完備性、可測包絡、指数密度による測度変更 | `PathLimits`、`Envelope` |
| 利得の L² 包絡の下での special 分解 | `GainDecomposition` |
| 元市場の同定、有限回の切替、停止、有限凸和、終端極限 | `IntegralClosure`、`MarketOperations`、`GainStopping`、`GainConvexity`、`TerminalMarket` |
| 有限尺度の消失リスク・正規化尾部・test 評価、停止前成分の L² 評価 | `FiniteRisk`、`TailNormalization`、`TailTests`、`PrefixEnergy` |
| L² マルチンゲールの test 評価と一様近似による判定 | `MartingaleApproximation` |
| 閉停止時の下界と元市場の終端帰属を持つ有限 Hahn 改善 | `FiniteHahn` |
| 成分評価からの共通極限の積分実現 | `IntegralClosure` |

これらの入力は NFLVR や最大性を仮定せず、市場の選択列の収束を結論しない。
例えば尾部の正規化入力は、一つの尺度で正規化利得を構成する。
主部が尺度を選び、得られた族に Lemma 4.7 を適用する。

`GainData`、`MarketData`、`HahnData` は具体的な record である。
そのフィールドは、過程、元価格の積分 graph、正則な成分、有限操作、定量的な不等式を記述する。
局所化スケジュールや内部の積分表現用データは、主部の型に現れない。
`generalAdmissibleClaims` と `generalTerminalClaims` も、積分 graph、全時刻の下界、
候補自身の連続時間での終端極限から定義した具体的な集合である。

数学文書の第2節は、上表の七群を七つの命題として述べ、合計20項を明示する。
積分graphと市場の二つのデータ定義を合わせ、各項の識別子を実際の隔離入力の宣言名へ対応付ける。
付録A–Cは内部構成、Dは七入力の証明、Eは宣言対応表である。
`check_structure.py` は日英の対応表と入力一覧の一致、および本文から付録内部への直接参照がないことを検査する。
隔離検査はこの一覧を Lean から出力した宣言集合と照合する。参照の検査は数学文の意味自体の自動検証ではない。

## 分離の検証

[AuditMainTheorem.lean](../scripts/AuditMainTheorem.lean) は、`Proof/`、`Closedness/`、
`Main.lean` に属する全宣言の型と証明項を調べる。自動生成された補助宣言も対象とし、
`Stochastic/` の定数への直接依存があれば失敗する。
また、主部の列選択、添字付き族評価、尾部評価、共通凸化、最大性、閉性の議論が、
最終証明に実際に現れることを検査する。
主定理に許す公理は `propext`、`Classical.choice`、`Quot.sound` のみである。

[check_analytic_isolation.py](../scripts/check_analytic_isolation.py) は、一時プロジェクトから
`Stochastic/` 全体を除去する。20 個の解析定理と二つのデータ定義
（`GeneralIntegralGraph`、`generalMarket`）について、通常版から正確な型を出力し、
それらだけを一時的な仮定に置き換え、主部を変更せずに再コンパイルする。
利得・市場操作・Hahn 改善の record と終端集合の具体的定義は維持する。
共有するキャッシュは第三者パッケージのものだけであり、プロジェクト自身の成果物は再生成する。
最後に、使用する公理が指定した入力と通常の三公理だけであることを監査する。
検査用仮定は通常版や公開版のライブラリに含めない。
型の出力、隔離ビルド、最終監査はいずれも、警告が出た場合に検査を失敗させる。

公開定理の元の切断市場に関する仕様も維持している。
元の仕様と公開名で書いた仕様の定義上の一致を、Lean による型検査で確認する。

## 保守時の方針

対象の定義と直接の性質はまとめて配置する。行数や宣言数は点検の指標であり、固定の上限ではない。
積分表現や測度をまたぐ箇所には、対応を示す補題を明示する。
special 分解が同値測度間で無条件に保存されるとは仮定しない。

`task verify` は構造、ビルド、宣言の依存閉包、文書中の宣言参照、公理、解析側の分離を検査する。
各ソース宣言は、それ自体または自動生成宣言を通して主定理に寄与しなければならない。
型検査に必要なコマンド、記法、インスタンス属性も、再ビルドできる状態に保つ。
数学本文を変更したら `task docs` を実行し、日英両方の PDF を更新する。
標準の mathlib linter を有効に保ち、警告は原因を修正して解消する。
