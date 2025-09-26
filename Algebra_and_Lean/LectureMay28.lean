import Mathlib

/-
  行列の扱い
-/

section Matrix

#eval !![1,2;3,4]

#eval (!![1,1;0,1] : Matrix (Fin 2) (Fin 2) ℤ) - !![2,3;1,2] /-足し算, 引き算等もやってみる -/
-- 等式あるいは不等式で型を自動的合わせてくれる機能を coerision という. ↑ などの上向き矢印はこの coerusion が起こった時に表示される.


def Uppertriangle (A : Matrix (Fin n) (Fin n) ℝ) : Prop := ∀ ⦃i j⦄ , i > j → A i j = 0



example (A B : Matrix (Fin n) (Fin n) ℝ) (h1 : Uppertriangle A) (h2 : Uppertriangle B):
    Uppertriangle (A + B) := by
    dsimp [Uppertriangle] at *
  -- 定義を使って書き直した. dsimp は定義を書き下す命令
    intro i j Hij
    specialize h1 Hij
  -- A が上半三角であることを利用して A i j = 0 を導いた
    specialize h2 Hij
    rw [h1, h2]
    ring

example (A B : Matrix (Fin n) (Fin n) ℝ) (h1 : Uppertriangle A) (h2 : Uppertriangle B):
    Uppertriangle (A - B) := by sorry

-- Fin n = {0,1,2,...,n-1}

/-
A,B が上半三角行列 => 積 A*B も上半三角行列は通常以下のように示す.

i > j とする.
A*B の (i,j) 成分 = ∑ a(i,k)*b(k,j)
                 = ∑ (k ≤  j) a(i,k)*b(k,j) + ∑ (k > j) a(i,k)*b(k,j)

一番目の和は i > j ≥ k より a(i,k) = 0
二番目の和は k > j より b(k,j) = 0
よって ∑ 記号の中の項はすべて 0 となるので A*B の (i,j) 成分は 0
-/


example (A B : Matrix (Fin n) (Fin n) ℝ) (h1 : Uppertriangle A) (h2 : Uppertriangle B):
     Uppertriangle (A*B) := by
     dsimp [Uppertriangle] at *
  -- 定義を使って書き直した
     intro i j Hij
     dsimp [Matrix.mul_apply]
  -- n x n 行列の掛け算の定義を書き直した
     apply Finset.sum_eq_zero
  -- 総和が 0 となる <= 各項が 0 であれば良い, Reason Backward!
     intro k Hk
     by_cases hki : k < i
  -- k < i の場合と k ≥ i の場合に分けた
     · specialize h1 hki
  -- k < i の場合 a i k = 0
       rw [h1]
       simp
     apply le_of_not_gt at hki
  -- 人間のように ¬ i>k を自動で書き換えてはくれない
     have aux : k > j := by
  -- b k j = 0 を得るために必要な不等式
      apply lt_of_lt_of_le
      show i > j
      assumption
      assumption
     specialize h2 aux
     rw [h2]
     simp


end Matrix

section Existence_of_base

open Submodule Function Set Classical Module

variable (K V: Type*) [Field K] [AddCommGroup V] [Module K V] (t : Set V)

theorem myself.zorn_subset_nonempty (S : Set (Set α))
    (H : ∀ c ⊆ S, IsChain (· ⊆ ·) c → c.Nonempty → ∃ ub ∈ S, ∀ s ∈ c, s ⊆ ub) (x) (hx : x ∈ S) :
    ∃ m, x ⊆ m ∧ Maximal (· ∈ S) m :=
  zorn_le_nonempty₀ _ (fun _ cS hc y yc => H _ cS hc ⟨y, yc⟩) _ hx

/-
 K-vector 空間 V が基底を持つことは以下のように示す.
 V の部分集合からなる集合を Set V とする. s ∈ Set V に対して,
 S = { t ∈ Set V | s ⊆  t ∧ t は線型独立  }
 を考える. S には包含関係で半順序が定まる. S の全順序部分集合 S₀ で空でないものに対し, S₀ の元
 すべての合併集合 S₁ は
 - s を含む
 - (x₁,...,xₘ) ⊆ S₁ は定義からある S の元 X に含まれる. よって線型独立
 となるので S₁ は S₀ の元の上界となる. よって Zorn の補題により S に極大元が存在する. それを b とすると,
 - b は定義から線型独立.
 - b が張る V のベクトル空間が V でないとすると, V に b 上線型独立であるような元 x がある.
   b に x を加えた集合は線型独立かつ t を含むので s の極大性に矛盾する.
 よって b が求める基底である.
-/


theorem myself.exists_linearIndepOn_id_extension (hs : LinearIndepOn K id s) (hst : s ⊆ t) :
    ∃ b ⊆ t, s ⊆ b ∧ t ⊆ span K b ∧ LinearIndepOn K id b := by
  obtain ⟨b, sb, h⟩ := by
  /-
     Zorn の補題を使って b sb h を得る. それらは Zorn の補題の出力と同じ. 上の m, x ⊆ m, Maximal m を得る
     そのための仮定が H,x,hx が必要.
  -/
    refine zorn_subset_nonempty { b | b ⊆ t ∧ LinearIndepOn K id b} ?_ _ ⟨hst, hs⟩
    · refine fun c hc cc _c0 => ⟨⋃₀ c, ⟨?_, ?_⟩, fun x => ?_⟩
  -- refine は Goal を証明すべき Goal に書き換える命令 ← Reason Backward
  /-
    c は V の部分集合からなる集合の部分集合
    hc は c が t に含まれまた LinearIndependent であること
    cc は c が chain であること
    _c0 は c が nonempty であること
  -/
      · exact sUnion_subset fun x xc => (hc xc).1
  -- sᵢ ⊆ t であれば ∪ᵢ sᵢ ⊆ t を示す. x ∈ c, c は c ⊆ t ∧ c は LinearIndependent を満たす. .1 は左側を取る
      · exact linearIndepOn_sUnion_of_directed cc.directedOn fun x xc => (hc xc).2
  /-
     sᵢ ⊆ sⱼ または sⱼ ⊆  sᵢ が成り立つ集合に対して ∪ sᵢ が linearIndependent directOn は
     x,y ∈ S ⇒ ∃ z ∈ S, x ≤ z ∨ y ≤ z と言う条件を満たすもの
  -/
      · exact subset_sUnion_of_mem
  -- sᵢ ⊆  s であれば ∪ᵢ sᵢ ⊆  s
  use b
  constructor
  ·  apply h.prop.1
  -- b は t に含まれる, 定義から
  constructor
  exact sb
  -- s ⊆ b 定義から
  constructor
  {
--  このカッコの中で b で生成される部分空間が V と一致しないのであれば矛盾を示す.
    intro x hx
    by_contra hnotinx

    have aux4 : x ∉ b := by
    -- x が b で生成される部分空間に入らないのであれば, 当然 b にも含まれない.
        intro H
        apply hnotinx
        have : b ⊆ span K b := by exact subset_span
        apply this at H
        assumption
    have aux : LinearIndepOn K id (insert x b) := by
    -- b に x をつくけ加えたものも一次独立
      rw [linearIndepOn_id_insert]
      constructor
      apply h.prop.2
      assumption
      exact aux4
    have aux2 : insert x b ⊆ t := by
    -- b に x を付け加えたものが t に含まれることを示す.
      refine insert_subset_iff.mpr ?_
      constructor
      assumption
      apply h.prop.1
/-    have aux3 : insert x b ⊇ b ∧ insert x b ≠ b := by
      constructor
      exact subset_insert x b
      refine insert_ne_self.mpr ?_
      exact aux4
-/
    have : x ∈ b := by
      apply h.mem_of_prop_insert
    -- Set V の元 c が c ⊆ t かつ c 線型独立 となれば c ⊆ b であることを利用して x ∈ b を示す.
      exact mem_sep aux2 aux
    -- 上の二つの条件を満たすことが aux たちからわかる.
    contradiction
  }
  apply h.prop.2


theorem existence_of_basis : ∃ b : Set V, ↑(span K b) = (univ : Set V) ∧ LinearIndepOn K id b := by
  obtain ⟨b, H1,H2,H3,H4⟩ := by
    refine exists_linearIndepOn_id_extension (linearIndepOn_empty K id) (empty_subset (univ:Set V))
  use b
  constructor
  exact eq_univ_of_univ_subset H3
  exact H4

end Existence_of_base

/-
What's next?
  この講義に続いて勉強するのであれば ⇒
  - 北大数学科の基礎数学シリーズの内容から
    - 数学的帰納法 ← これは扱いたかった.
    - 微分積分 (一変数)
    - 集合と位相
    - MIL = Mathematics_in_Lean にはこれらの項目がある.
  - 他変数の微分積分, 上記の MIL にはこの項目がない.
  - Mathlib を読む ← これは結構難しい
  - https://leanprover-community.github.io/mathlib-overview.html からどのように形式化されているか知りたい項目を探す
  - Mathlib は例えば選択公理などその名前のついた theorem があるのだが, それはいわゆる alias で本質的なところを形式化したも
    のはその前後の lemma だったりすることが多い. 上の方法を紹介はしたが, 個人的な経験からはあまり役に立っていない.
  - LeanSearch という検索エンジンが少しいいようだ
  - 冬学期に代数学続論と言う科目で Lean を使った講義を行う. 今度は代数系に特化した形でやるつもり.
-/

/-
  形式手法
  - プログラムにはバグがつきもの. つまり関数を定義しても入力の値によって思わぬ出力が出てくる場合がある.
  - Lean を用いれば, 関数 f が適切に定義されていれば, その性質は「証明」出来る.
  - もし関数 f の証明した性質を持たない実例が得られれば, 第一回の講義で述べたように Lean で命題 P : 関数 f はある性質を持つ
    その否定, 関数 fはある性質を持たない, が同時に「証明」されたことになる.
  - すると ZFC + 到達不可能基数の存在に矛盾があることになる.
  - このようなことはそうそう起こらない
  - 従ってバグは潜在的にない !
  - このようにプログラムを証明しながら作成することを形式手法と呼ぶ.
-/
