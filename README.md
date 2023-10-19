# Mathematics in Leanの日本語訳
* [原文](https://leanprover-community.github.io/mathematics_in_lean/index.html)
  * [原文の学習用リポジトリ](https://github.com/leanprover-community/mathematics_in_lean)
* [原文のソースコード](https://github.com/avigad/mathematics_in_lean_source)
* [対訳表]()

## 翻訳する際のルール

* 文体は常に敬体（です・ます調）とする.
* 英文をコメントアウトして，その直下に和訳を書く．
  * 英文は`OMIT`でくくること．（README.origin.md参照）
* 和訳文を改行すると，その位置に空白が入ってしまうので段落内で改行しない.
* 句読点には `,` `.` を用いる.
* 3音以上のカタカナ語の末尾の長音記号「ー」は省く．
* カタカナ語のままで違和感のない用語はカタカナ語のまま使う．

## 輪読方針

* masterブランチで和訳したい章に対応する下記の表に自分の名前を入れてpush．
* 対象の章名でブランチを切り翻訳を行う．
* 翻訳が終わったらブランチをpushしてプルリクエストを出す．
* 輪読に参加しているメンバーでレビューを行い、全て解決したらマージする．

### 参加者

* [s-taiga](https://github.com/s-taiga)
* [Taka](https://github.com/Taka0007)

### 翻訳担当

* C01_Introduction

| 章名 | 担当 |
| --- | --- |
| C01_Introduction.rst | |
| S01_Getting_Started.lean | [s-taiga](https://github.com/s-taiga) |
| S02_Overview.lean | [s-taiga](https://github.com/s-taiga) |

* C02_Basics

| 章名 | 担当 |
| --- | --- |
| C02_Basics.rst | |
| S01_Calculating.lean | [Taka](https://github.com/Taka0007) |
| S02_Proving_Identities_in_Algebraic_Structures.lean | [s-taiga](https://github.com/s-taiga) |
| S03_Using_Theorems_and_Lemmas.lean | [s-taiga](https://github.com/s-taiga) |
| S04_More_on_Order_and_Divisibility.lean | [s-taiga](https://github.com/s-taiga) |
| S05_Proving_Facts_about_Algebraic_Structures.lean | [s-taiga](https://github.com/s-taiga) |

* C03_Logic

| 章名 | 担当 |
| --- | --- |
| C03_Logic.rst ||
| S01_Implication_and_the_Universal_Quantifier.lean ||
| S02_The_Existential_Quantifier.lean ||
| S03_Negation.lean ||
| S04_Conjunction_and_Iff.lean ||
| S05_Disjunction.lean ||
| S06_Sequences_and_Convergence.lean ||

* C04_Sets_and_Functions

| 章名 | 担当 |
| --- | --- |
| C04_Sets_and_Functions.rst ||
| S01_Sets.lean ||
| S02_Functions.lean ||
| S03_The_Schroeder_Bernstein_Theorem.lean ||

* C05_Elementary_Number_Theory

| 章名 | 担当 |
| --- | --- |
| C05_Elementary_Number_Theory.rst ||
| S01_Irrational_Roots.lean ||
| S02_Induction_and_Recursion.lean ||
| S03_Infinitely_Many_Primes.lean ||

* C06_Structures

| 章名 | 担当 |
| --- | --- |
| C06_Structures.rst ||
| S01_Structures.lean ||
| S02_Algebraic_Structures.lean ||
| S03_Building_the_Gaussian_Integers.lean ||

* C07_Hierarchies

| 章名 | 担当 |
| --- | --- |
| C07_Hierarchies.rst ||
| S01_Basics.lean ||
| S02_Morphisms.lean ||
| S03_Subobjects.lean ||

* C08_Topology

| 章名 | 担当 |
| --- | --- |
| C08_Topology.rst ||
| S01_Filters.lean ||
| S02_Metric_Spaces.lean ||
| S03_Topological_Spaces.lean ||

* C09_Differential_Calculus

| 章名 | 担当 |
| --- | --- |
| C09_Differential_Calculus.rst ||
| S01_Elementary_Differential_Calculus.lean ||
| S02_Differential_Calculus_in_Normed_Spaces.lean ||

* C10_Integration_and_Measure_Theory

| 章名 | 担当 |
| --- | --- |
| C10_Integration_and_Measure_Theory.rst ||
| S01_Elementary_Integration.lean ||
| S02_Measure_Theory.lean ||
| S03_Integration.lean ||
