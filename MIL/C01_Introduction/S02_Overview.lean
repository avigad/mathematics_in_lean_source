import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Parity
import MIL.Common

open Nat

-- SOLUTIONS:
-- There are no exercises in this section.
/- OMIT:
Overview
--------

OMIT. -/
/- TEXT:
概要
----

TEXT. -/
/- OMIT:
Put simply, Lean is a tool for building complex expressions in a formal language
known as *dependent type theory*.

Every expression has a *type*, and you can use the `#check` command to
print it.
Some expressions have types like `ℕ` or `ℕ → ℕ`.
These are mathematical objects.
OMIT. -/
/- TEXT:
一言で言うならば，Leanは *依存型理論* と呼ばれる形式言語を用いて複雑な式を構築するためのツールです．

.. index:: check, commands ; check

それぞれの式は *型* を持ち，そしてそれは `#check` コマンドで表示することができます．例えば `ℕ` や `ℕ → ℕ` のような型があります．これらは数学的な対象です．
TEXT. -/
-- These are pieces of data.
-- QUOTE:
#check 2 + 2

def f (x : ℕ) :=
  x + 3

#check f
-- QUOTE.

/- OMIT:
Some expressions have type `Prop`.
These are mathematical statements.
OMIT. -/
/- TEXT:
式の中には型として `Prop` を持つものも存在します．これらは数学的な命題です．
TEXT. -/
-- These are propositions, of type `Prop`.
-- QUOTE:
#check 2 + 2 = 4

def FermatLastTheorem :=
  ∀ x y z n : ℕ, n > 2 ∧ x * y * z ≠ 0 → x ^ n + y ^ n ≠ z ^ n

#check FermatLastTheorem
-- QUOTE.

/- OMIT:
Some expressions have a type, `P`, where `P` itself has type `Prop`.
Such an expression is a proof of the proposition `P`.
OMIT. -/
/- TEXT:
また式の中には `Prop` 型の式 `P` 自体を型としてもつものもあります．このような式は命題 `P` の証明です．
TEXT. -/
-- These are proofs of propositions.
-- QUOTE:
theorem easy : 2 + 2 = 4 :=
  rfl

#check easy

theorem hard : FermatLastTheorem :=
  sorry

#check hard
-- QUOTE.

/- OMIT:
If you manage to construct an expression of type ``FermatLastTheorem`` and
Lean accepts it as a term of that type,
you have done something very impressive.
(Using ``sorry`` is cheating, and Lean knows it.)
So now you know the game.
All that is left to learn are the rules.

OMIT. -/
/- TEXT:
もしなんとかして ``FermatLastTheorem`` 型の式を構成でき，Leanに受け入れさせることができたら，とても素晴らしいことを成し遂げたことになります．（ここで ``sorry`` を使うのはズルで，Leanもそのことを知っています．）これでLeanがどういうものであるかわかったでしょう．あとはルールを覚えるだけです．

TEXT. -/
/- OMIT:
This book is complementary to a companion tutorial,
`Theorem Proving in Lean <https://leanprover.github.io/theorem_proving_in_lean4/>`_,
which provides a more thorough introduction to the underlying logical framework
and core syntax of Lean.
*Theorem Proving in Lean* is for people who prefer to read a user manual cover to cover before
using a new dishwasher.
If you are the kind of person who prefers to hit the *start* button and
figure out how to activate the potscrubber feature later,
it makes more sense to start here and refer back to
*Theorem Proving in Lean* as necessary.

OMIT. -/
/- TEXT:
本書は同種のチュートリアルである `Theorem Proving in Lean <https://leanprover.github.io/theorem_proving_in_lean4/>`_ を補完するものです． (訳注: 有志による日本語訳が `こちら <https://aconite-ac.github.io/theorem_proving_in_lean4_ja/>`_ にあります.)あちらはLeanの根幹にある論理フレームワークとコア構文についてより包括的に説明しています． *Theorem Proving in Lean* は新しい食洗器を使う前に取説を隅から隅まで読みたい人向けです．もし読者がとりあえず *スタート* ボタンを押してから食洗器内の洗浄ブラシがどう動くのかみてみたいタイプであるならば，本書から始めて必要に応じて *Theorem Proving in Lean* を参照する方が理にかなっているでしょう．

TEXT. -/
/- OMIT:
Another thing that distinguishes *Mathematics in Lean* from
*Theorem Proving in Lean* is that here we place a much greater
emphasis on the use of *tactics*.
Given that we are trying to build complex expressions,
Lean offers two ways of going about it:
we can write down the expressions themselves
(that is, suitable text descriptions thereof),
or we can provide Lean with *instructions* as to how to construct them.
For example, the following expression represents a proof of the fact that
if ``n`` is even then so is ``m * n``:
OMIT. -/
/- TEXT:
*Mathematics in Lean* と *Theorem Proving in Lean* のもう一つの違いは，本書では *タクティク* の使用にずっと重点を置いていることです．Leanで複雑な式を作り上げたい時，2種類の方法があります:1つ目は式を直接書き下す方法．（これはテキストの記述に向いています）2つ目はLeanに式をどのように構成するかを *指示* する方法です．例えば以下の式は ``n`` が偶数なら ``m * n`` も偶数であることの証明を表しています．
TEXT. -/
-- Here are some proofs.
-- QUOTE:
example : ∀ m n : Nat, Even n → Even (m * n) := fun m n ⟨k, (hk : n = k + k)⟩ ↦
  have hmn : m * n = m * k + m * k := by rw [hk, mul_add]
  show ∃ l, m * n = l + l from ⟨_, hmn⟩
-- QUOTE.

/- OMIT:
The *proof term* can be compressed to a single line:
OMIT. -/
/- TEXT:
この *証明項* は1行に圧縮することができます:
TEXT. -/
-- QUOTE:
example : ∀ m n : Nat, Even n → Even (m * n) :=
fun m n ⟨k, hk⟩ ↦ ⟨m * k, by rw [hk, mul_add]⟩
-- QUOTE.

/- OMIT:
The following is, instead, a *tactic-style* proof of the same theorem, where lines
starting with ``--`` are comments, hence ignored by Lean:
OMIT. -/
/- TEXT:
以下は，同じ定理を証明項の代わりに *タクティクスタイル* で証明したものです．ここで ``--`` で始まる行はコメントで，Leanに無視されます．
TEXT. -/
-- QUOTE:
example : ∀ m n : Nat, Even n → Even (m * n) := by
  -- Say m and n are natural numbers, and assume n=2*k.
  -- mとnを自然数とし，n=2*kと仮定．
  rintro m n ⟨k, hk⟩
  -- We need to prove m*n is twice a natural number. Let's show it's twice m*k.
  -- m*nがある自然数の2倍であることを証明する必要がある．そこでm*kの2倍であることを示す．
  use m * k
  -- Substitute for n,
  -- nを置換する．
  rw [hk]
  -- and now it's obvious.
  -- 後は明らか．
  ring
-- QUOTE.

/- OMIT:
As you enter each line of such a proof in VS Code,
Lean displays the *proof state* in a separate window,
telling you what facts you have already established and what
tasks remain to prove your theorem.
You can replay the proof by stepping through the lines,
since Lean will continue to show you the state of the proof
at the point where the cursor is.
In this example, you will then see that
the first line of the proof introduces ``m`` and ``n``
(we could have renamed them at that point, if we wanted to),
and also decomposes the hypothesis ``Even n`` to
a ``k`` and the assumption that ``n = 2 * k``.
The second line, ``use m * k``,
declares that we are going to show that ``m * n`` is even by
showing ``m * n = 2 * (m * k)``.
The next line uses the ``rewrite`` tactic
to replace ``n`` by ``2 * k`` in the goal,
and the ``ring`` tactic solves the resulting goal ``m * (2 * k) = 2 * (m * k)``.

OMIT. -/
/- TEXT:
VSCode上でこのような証明の各行にカーソルを合わせると，Leanは *証明の状態* を別画面に表示し，その時点までで証明をどこまで構築したか，そして目指す定理のためにあと何を示せばよいかを教えてくれます．また，Leanはカーソル位置での証明の状態を表示し続けるので，VSCode上で証明を一行一行たどることで，証明を追いかけることができます．この例では，証明の1行目で ``m`` と ``n`` （必要があればここで別の名前にすることもできます）を導入し，そして ``Even n`` を ``k`` と仮定 ``n = 2 * k`` の二つに分割しています．2行目の ``use m * k`` では ``m * n`` が偶数であることを ``m * n = 2 * (m * k)`` を示すことで証明していくと宣言しています．次の行では ``rewrite`` タクティクを用いてゴール中の ``n`` を ``2 * k`` に置換しています．そして ``ring`` タクティクで ``m * (2 * k) = 2 * (m * k)`` を解いています．[#f1]_

TEXT. -/
/- OMIT:
The ability to build a proof in small steps with incremental feedback
is extremely powerful. For that reason,
tactic proofs are often easier and quicker to write than
proof terms.
There isn't a sharp distinction between the two:
tactic proofs can be inserted in proof terms,
as we did with the phrase ``by rw [hk, mul_left_comm]`` in the example above.
We will also see that, conversely,
it is often useful to insert a short proof term in the middle of a tactic proof.
That said, in this book, our emphasis will be on the use of tactics.

OMIT. -/
/- TEXT:
証明を組み立てるうえで，細かいステップごとに段階的にフィードバックを受けられることは，非常に役に立ちます．このため，タクティクを使うと証明項を書き下すよりも早く，簡単に証明を書くことができます．とはいえタクティクスタイルと項スタイルの間に明確な線引きは存在しません:上記の例の ``by rw [hk, mul_left_comm]`` のように，項スタイルの証明の途中にタクティクスタイルの証明を入れることが可能です．そして反対に，この後見ていくようにタクティクスタイルの証明中で短い項による証明を用いるのが便利なこともよくあります．とはいえ，本書ではタクティクの使用に重点を置くこととしています．

TEXT. -/
/- OMIT:
In our example, the tactic proof can also be reduced to a one-liner:
OMIT. -/
/- TEXT:
上記のタクティクスタイルの証明例について，証明を一行にまとめることも可能です．
TEXT. -/
-- QUOTE:
example : ∀ m n : Nat, Even n → Even (m * n) := by
  rintro m n ⟨k, hk⟩; use m * k; rw [hk]; ring
-- QUOTE.

/- OMIT:
Here we have used tactics to carry out small proof steps.
But they can also provide substantial automation,
and justify longer calculations and bigger inferential steps.
For example, we can invoke Lean's simplifier with
specific rules for simplifying statements about parity to
prove our theorem automatically.
OMIT. -/
/- TEXT:
ここまで証明の小さなステップのためにタクティクを用いてきました．しかしタクティクで大幅な自動化も行うこともでき，長い計算と大きな推論ステップを正当化することができます．例えば，Leanの簡約化器である ``simp`` タクティクに，個別の簡約ルールとして偶奇についての命題を与えることで，同じ定理を自動的に証明することができます．
TEXT. -/
-- QUOTE:
example : ∀ m n : Nat, Even n → Even (m * n) := by
  intros; simp [*, parity_simps]
-- QUOTE.

/- OMIT:
Another big difference between the two introductions is that
*Theorem Proving in Lean* depends only on core Lean and its built-in
tactics, whereas *Mathematics in Lean* is built on top of Lean's
powerful and ever-growing library, *Mathlib*.
As a result, we can show you how to use some of the mathematical
objects and theorems in the library,
and some of the very useful tactics.
This book is not meant to be used as an complete overview of the library;
the `community <https://leanprover-community.github.io/>`_
web pages contain extensive documentation.
Rather, our goal is to introduce you to the style of thinking that
underlies that formalization, and point out basic entry points
so that you are comfortable browsing the library and
finding things on your own.

OMIT. -/
/- TEXT:
本書と *Theorem Proving in Lean* の間のもうひとつの大きな違いは， *Theorem Proving in Lean* はLeanのコアと組み込みのタクティクのみに依存しているのに対し， *Mathematics in Lean* は *Mathlib* という発展を続ける強力なライブラリの上に構築されていることです．そのため，ライブラリにある数学的概念や定理，そして非常に便利なタクティクなどの使い方を紹介することができます．本書ではライブラリの完全な説明書として利用されることを意図していません;その代わりに `コミュニティ <https://leanprover-community.github.io/>`_ のページに広範なドキュメントが掲載されています．むしろ，本書のゴールはライブラリにおける形式化の根底にある考え方を紹介し基本をおさえてもらうことで，ライブラリを自由に眺めて，その中から自力で必要なものを見つけられるようにすることです．

TEXT. -/
/- OMIT:
Interactive theorem proving can be frustrating,
and the learning curve is steep.
But the Lean community is very welcoming to newcomers,
and people are available on the
`Lean Zulip chat group <https://leanprover.zulipchat.com/>`_ round the clock
to answer questions.
We hope to see you there, and have no doubt that
soon enough you, too, will be able to answer such questions
and contribute to the development of *Mathlib*.

OMIT. -/
/- TEXT:
対話的な定理証明はなかなか思い通りにいかないものなので，学習曲線は険しいものになるでしょう．しかしLeanコミュニティは初心者をとても歓迎しており， `Lean Zulip chat group <https://leanprover.zulipchat.com/>`_ では24時間体制で質問に答えています．そこであなたにお会いできることを楽しみにしています．きっとあなたもすぐに初心者の質問に答えたり， *Mathlib* の発展に貢献したりできるようになることでしょう．

TEXT. -/
/- OMIT:
So here is your mission, should you choose to accept it:
dive in, try the exercises, come to Zulip with questions, and have fun.
But be forewarned:
interactive theorem proving will challenge you to think about
mathematics and mathematical reasoning in fundamentally new ways.
Your life may never be the same.

OMIT. -/
/- TEXT:
そこで君のミッションを説明しよう: とにかくやってみて，演習問題に取り組み，Zulipで質問をし，そして楽しむことです．しかし先に警告しておきますが，対話的な定理証明は数学や数学的な推論について根本的に新しい考え方を迫るものです．あなたの人生は永久に変わってしまうでしょう！

*Acknowledgments.* We are grateful to Gabriel Ebner for setting up the
infrastructure for running this tutorial in VS Code,
and to Scott Morrison and Mario Carneiro for help porting it from Lean 4.
We are also grateful for help and corrections from
Julian Berman, Alex Best,
Bulwi Cha, Bryan Gin-ge Chen, Mauricio Collaris, Johan Commelin, Mark Czubin,
Denis Gorbachev, Winston de Greef,
Mathieu Guay-Paquet, Julian Külshammer,
Martin C. Martin,
Giovanni Mascellani, Isaiah Mindich, Hunter Monroe, Pietro Monticone, Oliver Nash,
Bartosz Piotrowski, Nicolas Rolland, Guilherme Silva, Floris van Doorn, and Eric Wieser.
Our work has been partially supported by the Hoskinson Center for
Formal Mathematics.

.. [#f1] 訳注: コード中で使用されているのは ``rw`` ですが，これは ``rewrite`` の後に ``rfl`` を実行するというタクティクで，ほぼ ``rewrite`` と同じものだと思ってください．
TEXT. -/
