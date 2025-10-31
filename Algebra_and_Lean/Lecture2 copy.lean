import Mathlib

/-
前回の復習
    Lean では「数式は」左結合, つまり a*b*c = (a*b)*c, a+b+c+d = (((a+b)+c)+d)
-/

example (a b c: ℝ) : a*(b*c) = b*(a*c) := by
  calc
  _ = a*b*c := by rw [mul_assoc]
  _ = b*a*c := by rw [mul_comm a b]
  _ = b*(a*c) := by rw [mul_assoc]

#check pow_two
#check pow_three
#check sub_mul
#check sub_add
#check add_assoc
#check two_mul -- 2*n = n+n
#check sub_sub

example (a b : ℝ ): (a - b)^2 = a^2 - 2*a*b + b^2 :=
  calc
    _ = (a - b)*(a - b) := by rw [pow_two]
    _ = a*a - b*a - (a*b - b*b) := by rw [mul_sub, sub_mul,sub_mul]
    _ = a*a - b*a - a*b + b*b := by sorry
    _ = a*a - a*b - a*b + b*b := by sorry
    _ = a^2 - a*b - a*b + b^2:= by sorry
    _ = a^2 - 2*a*b + b^2 := by ring

example (a b : ℝ ): (a - b)^2 = a^2 - 2*a*b + b^2 := by ring

/-
不等式の証明
   前回は因数分解など中高の数学に現れる等式を証明した. 今回は不等式の証明をやってみる.
-/

#check add_le_add
#check le_refl
#check Left.mul_nonneg
#check Left.add_nonneg
#check pow_two_nonneg
#check ge_iff_le


lemma AMGM2 (a b : ℝ) : 2*a*b ≤ a^2 + b^2 := by
/-
  a^2 +  b^2 - 2*a*b = (a -b )^2 ≥ 0
-/
  have h : 0 ≤ a^2 + b^2 - 2*a*b := by
    rw [←ge_iff_le]
    calc
      _ = (a - b)^2 := by ring
      _ ≥ 0 := by apply pow_two_nonneg
  calc
    _ = 2*a*b + 0 := by rw [add_zero]
    _ ≤ 2*a*b +(a^2 + b^2 - 2*a*b) := by exact add_le_add (le_refl (2*a*b)) h
    _ = a^2 + b^2 := by ring



lemma AGMG3 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) : 3*a*b*c ≤ a^3 + b^3 + c^3 := by
  have h1 : a^3 + b^3 + c^3 - 3*a*b*c =
           (a + b + c)*(a^2 + b^2 + c^2 - a*b - b*c - c*a) := by ring -- 補助的な因数分解
  have h2 : 0 ≤ a^2 + b^2 + c^2 - a*b - b*c - c*a := by
    have h3 : a^2 + b^2 + c^2 - a*b - b*c - c*a = ((a-b)^2 + (b-c)^2 + (c-a)^2)/2 := by ring -- 平方完成のようなもの
    rw [h3]
    apply Left.mul_nonneg
    apply Left.add_nonneg
    apply Left.add_nonneg
    apply pow_two_nonneg
    apply pow_two_nonneg
    apply pow_two_nonneg
    norm_num
  have h4 : 0 ≤ a^3 + b^3 + c^3 - 3*a*b*c  := by
    rw [h1]
    apply Left.mul_nonneg
    linarith
    exact h2
  calc
    _ = 3*a*b*c + 0 :=by rw [add_zero]
    _ ≤ 3*a*b*c + (a^3 + b^3 + c^3 - 3*a*b*c) := by exact add_le_add (le_refl (3*a*b*c)) h4
    _ = a^3 + b^3 + c^3 := by ring


  /-
Reason Backwards とはシャーロックホームズシリーズの最初の作品, 緋色の研究の一節に現れる言葉である.
これは事件の現場を見て, そこから何が起こったのか逆向きに考えることで犯人を突き止めることを指す.
Lean においては証明を構成するときの基本的な考え方もこれと同じで,
結論を見て, 種々のコマンドをどのように使って仮定に還元するか?
を考えることが基本姿勢となる.
-/

#check min_le_left
#check min_le_right
#check le_min

#check le_antisymm
#check le_trans
#check le_refl



example (a b c : ℝ) : min (min a b) c = min a (min b c) := by
  apply le_antisymm
--  have h : min a b ≤ a := by exact min_le_left a b
  {
   apply le_min
   {
    apply le_trans
    show min (min a b) c ≤ min a b
    apply min_le_left
    apply min_le_left
   }
   {
    apply le_min
    {
      apply le_trans
      show min (min a b) c ≤ min a b
      apply min_le_left
      apply min_le_right
    }
    {
      apply min_le_right
    }
   }
  }
  {
    apply le_min
    {
      apply le_min
      apply min_le_left
      apply le_trans
      show min a (min b c) ≤ min b c
      apply min_le_right
      apply min_le_left
    }
    {
      apply le_trans
      show min a (min b c) ≤   min b c
      apply min_le_right
      apply min_le_right
    }
  }
