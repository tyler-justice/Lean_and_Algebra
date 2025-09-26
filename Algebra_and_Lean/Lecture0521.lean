import Mathlib

section Depencency

/- Lean では全ての項は「型」を持つ. これがプログラムにどのような影響があるか? を
 実例で確認する.
 型とはラベルのようなもの
-/

#check 3
#check (3:ℤ)
#check (3:ℝ)
#check (3:ℂ) -- 複素数では? バックスラッシュ + C でタブキーを押す

#eval 1 - 2
-- 自然数では m + n は m の n 個後の数を返す関数と定義されている.
#eval (1 : ℤ) - (2 : ℤ)
#eval (1 : ℤ)/(2 : ℤ)
#eval (1 : ℚ)/(2 : ℚ)
-- #eval (1 : ℝ)/(2 : ℝ) -- 実数は基本的に計算出来ない.

#check (1 : ℝ)/(2 : ℝ)

#eval (2 : ℝ)/(3 : ℝ) * (3 : ℝ)
#eval (2 : ℚ)/(3 : ℚ) * (3 : ℚ)

end Depencency

section converge

/-
 Lean では実数は有理数からなる Cauchy 列の同値類として定義される.
 Lean では

 環境名 仮定 : 主張 := 具体的な過程から主張を得るプロセス
-/

def ConvergesTo (s : ℕ → ℝ) (a : ℝ) : Prop :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |s n - a| < ε

theorem convergesTo_const (a : ℝ) : ConvergesTo (fun x : ℕ ↦ a) a := by
-- 定義を書き直すと ∀ε > 0, ∃ N, ∀ n ≥  N, |x n - a| < ε  を示す
  intro ε εpot
  use 0
-- Lean では自然数は 0 から始まる
  intro n nge
  simp
  -- rw [sub_self, abs_zero]
  apply εpot

theorem convergesTo_add {s t : ℕ → ℝ} {a b : ℝ}
      (cs : ConvergesTo s a) (ct : ConvergesTo t b) :
    ConvergesTo (fun n ↦ s n + t n) (a + b) := by
  -- 定義を書き直してみる.
  intro ε εpos
  dsimp -- this line is not needed but cleans up the goal a bit.
  have ε2pos : 0 < ε / 2 := by linarith
  rcases cs (ε / 2) ε2pos with ⟨Ns, hs⟩
  rcases ct (ε / 2) ε2pos with ⟨Nt, ht⟩
  use max Ns Nt
  intro n HN
  -- P → Q を示すとき, intro P で P を仮定の一部として, 結論 Q を示す
  have ngeNs : n ≥  Ns := by exact le_of_max_le_left HN
  have ngeNt : n ≥  Nt := by exact le_of_max_le_right HN
  calc
    _ = |(s n - a) + (t n - b)| := by ring
    _ ≤ |s n - a| + |t n - b| := by apply abs_add
    _ < ε/2 + ε/2 := by apply add_lt_add (hs n ngeNs) (ht n ngeNt)
    _ = ε := by norm_num


theorem convergesTo_mul_const {s : ℕ → ℝ} {a : ℝ} (c : ℝ) (cs : ConvergesTo s a) :
    ConvergesTo (fun n ↦ c * s n) (c * a) := by
  by_cases h : c = 0
  · convert convergesTo_const 0
    · rw [h]
      ring
    rw [h]
    ring
  have acpos : 0 < |c| := abs_pos.mpr h
  intro ε Epos
  have ecpos : 0 < ε/|c| := by exact div_pos Epos acpos
  rcases cs (ε/|c|) ecpos with ⟨Ns, hs⟩
  use Ns
  intro n HNs
  simp
  calc
    _ = |c*(s n - a)| := by ring
    _ = |c| * |s n - a| := by rw [abs_mul]
    _ < |c| * (ε/|c|) := by apply mul_lt_mul_of_pos_left (hs n HNs) acpos
    _ = ε := by exact mul_div_cancel₀ _ (ne_of_lt acpos).symm

  theorem exists_abs_le_of_convergesTo {s : ℕ → ℝ} {a : ℝ} (cs : ConvergesTo s a) :
    ∃ N b, ∀ n, N ≤ n → |s n| < b := by
  rcases cs 1 zero_lt_one with ⟨N, h⟩
  -- | s n - a | < 1 となる N を設定
  use N, |a| + 1
  intro n1 Hn1
  calc
   _ = |s n1 - a + a| := by ring
   _ ≤  |s n1 - a| + |a| := by apply abs_add (s n1 - a) a
   _ < 1 + |a| := by exact (add_lt_add_iff_right |a|).2 (h n1 Hn1)
   _ = |a| + 1 := by ring




  theorem aux {s t : ℕ → ℝ} {a : ℝ} (cs : ConvergesTo s a) (ct : ConvergesTo t 0) :
    ConvergesTo (fun n ↦ s n * t n) 0 := by
  -- 二つの収束する数列の積は収束先の積に収束することを示すための補助定理
  intro ε εpos
  dsimp
  rcases exists_abs_le_of_convergesTo cs with ⟨N₀, B, h₀⟩
  -- 一つ上の bound を数列 s に対して上限 B, 閾値 N₀ として適用
  have Bpos : 0 < B := by apply lt_of_le_of_lt (abs_nonneg _)  (h₀ N₀ (le_refl _))
  -- 始めの nonneg で 0 ≤ |s n| を次の h₀ N₀ le_refl で N₀ 自身が N₀ であることを示して h₀ を利用している.
  have pos₀ : ε / B > 0 := div_pos εpos Bpos
  rcases ct _ pos₀ with ⟨N₁, h₁⟩
  -- 数列 t が ε / B よりも小さくなる n を N₁ としている.
  simp at *
  use max N₀ N₁
  intro n Hn
  have ngeN₀ : n ≥  N₀ := by exact le_of_max_le_left Hn
  have ngeN₁ : n ≥  N₁ := by exact le_of_max_le_right Hn
  calc
    _ = |s n| * |t n| := by apply abs_mul
    _ < B * (ε / B) :=  by apply mul_lt_mul'' (h₀ n (ngeN₀)) (h₁ n (ngeN₁)) (abs_nonneg _) (abs_nonneg _)
    _ = ε := by field_simp

  theorem convergesTo_mul {s t : ℕ → ℝ} {a b : ℝ}
      (cs : ConvergesTo s a) (ct : ConvergesTo t b) :
    ConvergesTo (fun n ↦ s n * t n) (a * b) := by
  -- 今度は収束する数列の積は収束する値の積に収束することの証明
  have h₁ : ConvergesTo (fun n ↦ s n * (t n + -b)) 0 := by
  -- s n * (t n + -b) が 0 に収束することを途中で証明
    apply aux cs
  -- Reason backward. aux の仮定を示せば良い
    convert convergesTo_add ct (convergesTo_const (-b))
  -- 収束する二つの数列の和に分解
    ring
  have  := convergesTo_add h₁ (convergesTo_mul_const b cs)
-- s n * (t n - b) → 0 と b s n →  b * a を足し算したもの
  convert convergesTo_add h₁ (convergesTo_mul_const b cs) using 1
-- Goal を s n + t n を s n + (t n + - b) と b * s n の和に分解, using の後は適用回数
  · ext; ring
  ring

/-
  theorem convergesTo_mul2 {s t : ℕ → ℝ} {a b : ℝ}
      (cs : ConvergesTo s a) (ct : ConvergesTo t b) :
    ConvergesTo (fun n ↦ s n * t n) (a * b) := by
-- 別証明を試みる
    intro ε εpos
    rcases cs ε εpos with ⟨Ns, hs⟩
    rcases ct ε εpos with ⟨Nt, ht⟩
    rcases exists_abs_le_of_convergesTo ct with ⟨Nb, B, hb⟩
    use max (max Ns Nt) Nb
    intro n Hn
    have ngeNs : n ≥  Ns := by sorry
    have ngeNt : n ≥  Nt := by sorry
    have ngeNb : n ≥  Nb := by sorry
    simp
    calc
      _ = |(s n * t n - a * t n) +(a * t n - a * b)| := by ring
      _ ≤ |s n * t n - a * t n| + |a*t n - a * b| := by apply abs_add _ _
      _ = |(s n - a)*t n| + |a*(t n - b)| := by ring
      _ = |s n - a| * |t n| + |a| * |t n - b| := by rw [abs_mul, abs_mul]
      _ <  ε * B + |a| * |t n - b| := by apply (mul_lt_mul'' (hs n (ngeNs)) (hb n (ngeNb)) (abs_nonneg _) (abs_nonneg _))
-/
  -- ここで不等式の評価が難しいので t n - b と言う数列を別に考えたと思われる


--
/-
  ここで Lean における「否定」に触れる. Lean において Prop P の否定 ¬P は
  P を仮定すると矛盾が起きる, すなわち P → false である.
  by_contra とは結論 Q の否定を仮定に加え, 矛盾 false を新しい結論
  とする tactics である.
-/
  example (P Q : Prop) : (P → Q) →  ¬ (P ∧ ¬ Q) := by
    intro H1 H2
    obtain ⟨H3,H4⟩ := H2
    apply H4
    apply H1
    assumption

  example (P Q : Prop) : ¬ (P ∧ ¬ Q) → (P → ¬¬Q) := by
    intro H1 H2 H3
    apply H1
    constructor
    exact H2
    exact H3




  example(Q : Prop) (h : ¬¬Q) : Q := by
    by_contra
  -- 証明には排中律が必要
    apply h
    assumption

  example (Q : Prop) (h : Q) : ¬¬Q := by
    intro H
    exact H h

  example (h : ∀ P : Prop, P ∨  ¬ P) : ¬¬P → P := by
    intro H
    by_cases P
    assumption
    contradiction

  example (h : ∀ P : Prop, ¬¬P → P) : P ∨ ¬P := by
    apply h
    intro H
    push_neg at H
    obtain ⟨P,NP⟩ := H
    contradiction










  theorem convergesTo_unique {s : ℕ → ℝ} {a b : ℝ}
      (sa : ConvergesTo s a) (sb : ConvergesTo s b) :
    a = b := by
  by_contra abne
  -- 結論を否定して矛盾を導く
  have : |a - b| > 0 := by
    apply lt_of_le_of_ne
    -- ≤ と ≠ から < が出る
    apply abs_nonneg
    -- 絶対値の非負性
    intro H
    -- ≠  は a = b とすると false という意味
    apply abne
    apply eq_of_abs_sub_eq_zero H.symm
  let ε := |a - b| / 2
  have εpos : ε > 0 := by
    change |a - b| / 2 > 0
  -- change ゴールを定義が同じもので置き換える. この場合仮定 ε が |a - b|/2 と同じことを利用.
    linarith
  rcases sa ε εpos with ⟨Na, hNa⟩
  rcases sb ε εpos with ⟨Nb, hNb⟩
  -- 数列の二つの収束値に現れる量を取り出す
  let N := max Na Nb
  have absa : |s N - a| < ε := by
    apply hNa
    apply le_max_left
  have absb : |s N - b| < ε := by
    apply hNb
    apply le_max_right
  have : |a - b| < |a - b| := by
    calc
    _ = |(a - s N) + (s N - b)| := by ring
    _ ≤ |a - s N| + |s N - b| := by apply abs_add (a - s N) (s N - b)
    _ = |-(a - s N)| + |s N - b| := by  rw [abs_neg]
    _ = |s N - a| + |s N - b| := by ring
    _ < ε + ε  := by apply add_lt_add absa absb
    _ = 2*ε := by ring
    _ = |a - b| := by norm_num [ε]  ; ring
  exact lt_irrefl _ this
  -- lt_irrefl の後の _ はここでは順序は実数の大小関係を使っていると言うことの明記

end converge
