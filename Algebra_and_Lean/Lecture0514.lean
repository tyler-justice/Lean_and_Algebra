import Mathlib

section review_of_previous_lecture

/- example 仮定 : 主張 := 仮定を主張に変換する関数
 前回は Lean でどのようなコマンドで式変形をするか? について解説した.
 前回紹介したものは全て同値変形. このような変形を適用する場合は rw = rewrite を使う.
-/

example (a b : ℝ) : (a + b)*(a - b) = a^2 - b^2 := by
  rw [add_mul] -- (a + b)*(a-b) を a*(a-b) + b*(a-b) に展開
  rw [mul_sub, mul_sub] -- a*(a-b) を a*a - a*b に展開
  rw [sub_add]
  rw [← sub_add (a*b) (b*a) (b*b)]
  rw [mul_comm a b]
  rw [sub_self]
  rw [zero_add]
  rw [pow_two,pow_two]
-- Lean のプログラムを読む一つのコツ
-- 命令の後に何をしたのか自分なりの解釈を書き込む

example (a b : ℝ) : (a + b)*(a - b) = a^2 - b^2 := by ring

/-
ほとんどの受講者はこのような等式変形は出来るんだー以上の興味がない. ring で一発で変形出来れば十分.
-/
end review_of_previous_lecture

section Reason_Backwards

/-
Reason Backwards とはシャーロックホームズシリーズの最初の作品, 緋色の研究の一節に現れる言葉である.

In solving a problem of this sort, the grand thing is to be able to reason backwards.
That is a very useful accomplishment, and a very easy one, but people do not practise it much.
In the everyday affairs of life it is more useful to reason forwards, and so the other comes to be neglected.
There are fifty who can reason synthetically for one who can reason analytically.”

“I confess,” said I, “that I do not quite follow you.”

“I hardly expected that you would. Let me see if I can make it clearer.
Most people, if you describe a train of events to them, will tell you what the result would be.
They can put those events together in their minds, and argue from them that something will come to pass.
There are few people, however, who, if you told them a result, would be able to evolve from their own inner consciousness
what the steps were which led up to that result.
This power is what I mean when I talk of reasoning backwards, or analytically.”

前回, Lean で等式, あるいは方程式の解に関する主張を証明する場合は
適切な関数を用いて式を変形するということを紹介した.
数学の証明に他にどのようなものがあるか? を考えてみると最も普遍的な形として
仮定 A から主張 B を導くというものがあげられる.
Lean でももちろんこのような論法はある.これは主に仮定を書き換えることによって行われる.
-/

variable (a b c x: ℝ)

example (h1 :x^2 - 3*x + 2 ≥ 0) : x ≤ 1 ∨  x ≥  2 := by
  have aux : x^2 - 3*x + 2 = (x - 1)*(x - 2) := by ring -- 仮定を因数分解する
  have aux2 : 0 ≤ (x - 1)*(x -2) := by
    rw [← aux] -- 因数分解の逆
    exact h1
  rw [mul_nonneg_iff] at aux2 -- ab ≥ 0 ならば a, b が同じ符号を取る
  rcases aux2 with A|B -- 二つの因数が共に正 A または負 B の場合に分けた
  ·  right -- x ≥ 2 を証明しようとしている
     rw [ge_iff_le]
     rw [← sub_nonneg]
     obtain ⟨X1,X2⟩ := A -- かつで結ばれている仮定を二つに分解する
     assumption
  ·  left
     obtain ⟨X1,X2⟩ := B
     rw [← sub_nonpos]
     assumption

/-
  以下は Reason Backwards の例である.
-/

-- 2009 東北大学入試問題より

example (h1 : a + b ≥ c) : a^3 + b^3 + 3*a*b*c ≥ c^3 := by
  -- まず必要な因数分解を準備する
  have aux : a^3 + b^3 + 3*a*b*c - c^3 = (a+b-c)*(a^2 + b^2 + c^2 - a*b + b*c + c*a) := by ring
  have aux2 : a^2 + b^2 + c^2 - a*b + b*c + c*a = (1/2)*((a-b)^2 + (b + c)^2 + (c + a)^2) := by ring
  rw [ge_iff_le] -- x ≥ y を y ≤ x に書き換える.
  apply le_of_sub_nonneg -- A ≤ B を 0 ≤ B - A に書き換える
  rw [aux]
  rw [aux2] -- Goal に必要な式変形を行う
  apply Left.mul_nonneg
  apply sub_nonneg_of_le
  apply h1
  apply Left.mul_nonneg
  norm_num
  repeat
    apply Left.add_nonneg
  repeat
    apply sq_nonneg




end Reason_Backwards


section Minimum

variable (a b c : ℝ)


example : min a b = min b a := by
  apply le_antisymm -- a = b を a ≤ b と a ≥ b に分解
  apply le_min -- 何か ≤  min a b ←  何か ≤ a かつ 何か ≤ b
  apply min_le_right -- min a b ≤ b
  apply min_le_left -- min a b ≤  a
  apply le_min
  apply min_le_right
  apply min_le_left

example : max a b = max b a := by
  apply le_antisymm -- a = b を a ≤ b と a ≥ b に分割
  ·  apply max_le -- max a b ≤  何か ←  a ≤  何か かつ 何か ≤ b
     · apply le_max_right  -- a ≤ max a b
     · exact le_max_left b a
  ·  apply max_le
     · exact le_max_right a b
     · exact le_max_left a b

example : min (min a b) c = min a (min b c) := by
  apply le_antisymm
  · apply le_min
    apply le_trans
    apply min_le_left
    apply min_le_left
    apply le_min
    apply le_trans
    apply min_le_left
    apply min_le_right
    apply min_le_right
  · apply le_min
    apply le_min
    apply min_le_left
    apply le_trans
    apply min_le_right
    apply min_le_left
    apply le_trans
    apply min_le_right
    apply min_le_right

/-
  ここまでで lean で何か証明するときは適切なコマンドを見つけることが非常に重要であることが
  わかってくれたと思う. どうすれば適切なコマンドが見つかるか ← 五年間 Lean を使ってまだ
  有効な方法は見つけられていない.
  Leanserch https://leansearch.net
  は有用かもしれない.

-/

#loogle "add_le"

theorem aux : min a b + c ≤ min (a + c) (b + c) := by
   apply le_min -- 最小値の性質を用いて分解
   apply add_le_add_right -- c を消す
   apply min_le_left
   apply add_le_add_right
   apply min_le_right

example : min a b + c = min (a + c) (b + c) := by
   apply le_antisymm
   · apply aux -- min a b + c ≤ min (a+c) (b+c) は上の theorem そのもの
   · have aux2 : min (a+c) (b+c) - c + c =  min (a+c) (b+c) := by  rw [sub_add_cancel]
     rw  [←aux2] -- min (a+c) (b+c) -c + c
     apply add_le_add_right -- min (a+c) (b+c) ≤  min a b - c と移項するのに少し手間がかかる.
     rw [sub_eq_add_neg] -- -c を + (-c) と書き換え
     apply le_trans
     apply aux -- 協力なパターンマッチング
     rw [add_neg_cancel_right, add_neg_cancel_right]

/-
   x y ∈ ℝ  に対し
   和 : x ⊕ y = min x y
   積 : x • y = x + y
   と演算を定めると, これは可換環の公理を ⊕ に関する逆元の存在及び単位元の存在を除いて満たす.

   x • (y + z) x+ min (y,z)
   x • y + x • z = min (x+y) (x+z)
   上の二つが等しいことは 166 行目の主張と同じ!

   x ⊕ (y ⊕   z) = min x min y z
   (x ⊕ y) ⊕  z = min (min x y) z
   上の二つが等しいことは 127 行目の主張

   ∀ x, x ⊕ y = min x y = x となる y は ℝ の全ての元よりも大きい必要があり, そのようなものは
    ℝ の元にはない. ℝ ∪ {∞} にすれば ∞ は単位元となる.

   このようなものを半環 (semiring) と言う. 可換環の代わりにこの半環を用いて代数幾何を
   展開する分野をトロピカル幾何と言い, 非常に多くの分野と関わりがあることがわかってきている.
   (6/23 - 27 に集中講義)
-/

end Minimum
