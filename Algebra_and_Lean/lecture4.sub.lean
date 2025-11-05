import Mathlib

/-第五回 否定, and, or の構文 -/

variable {α : Type*} (P : α → Prop) (Q : Prop)

/- 以下の四つの問題は意味をちゃんと取らないといけない. -/

/- 記法 ¬P で P → False を表す. -/

example (h : ¬∃ x, P x) : ∀ x, ¬P x := by
  intro x nothx
  apply h
  use x

example (h : ¬∃ x, P x) : ∀ x, ¬P x := by
  push_neg at h
  assumption

/- 仮定 : ある x に対して 命題 P が成り立つことはない. => 全ての x に対し, P x は成り立たない-/

example (h : ∀ x, ¬P x) : ¬∃ x, P x := by
  intro hnotx
  rcases hnotx with ⟨x, hx⟩
  specialize h x
  contradiction

/- 仮定 : 全ての x に対し, P x は成り立たない => ある x に対し P x が成り立つことはない-/

example (h : ¬∀ x, P x) : ∃ x, ¬P x := by
  by_contra hx -- by_contra Goal を否定して, 仮定に移し, Goal を False に替える
  apply h
  intro x
  by_contra h2
  apply hx
  use x



/- 仮定 : 全ての x に対し, P x が成り立つわけではない => ある x に対し, P x が成り立たないことがある -/

example (h : ∃ x, ¬P x) : ¬∀ x, P x := by
  intro hx
  rcases h with ⟨x, hnotx⟩
  apply hnotx
  specialize hx x
  assumption

/- 仮定 : ある x に対し P x は成り立たない => 全ての x に対し P x が成り立つわけではない-/

example (h : ¬¬Q) : Q := by
  by_cases Q  -- ここで排中律を使っている
  assumption
  contradiction

example (h : ¬¬Q) : Q := by
  by_contra H
  apply h
  assumption

example (h : Q) : ¬¬Q := by
  intro h2
  apply h2
  assumption

  /- by_contra : P → Q の替わりに P ∧ ¬ Q → False を示す -/

example (P Q : Prop) :  (P → Q) → (P ∧ ¬Q → False ):= by
  intro HPQ HandnotQ
  obtain ⟨HP,HnotQ⟩ := HandnotQ
  apply HnotQ
  apply HPQ
  assumption

example (P Q : Prop) : (P ∧ ¬Q → False ) → (P → ¬¬Q) := by
  intro HPQF  HP notQ
  apply HPQF
  constructor
  assumption
  assumption

example (P Q : Prop) : (P → Q) → (¬Q → ¬P) := by
  intro HPQ notQ HP
  apply notQ
  apply HPQ
  assumption

example (P Q : Prop)  : (¬ Q → ¬ P) → (P → Q) := by
  intro notQP HP
  by_contra notQ
  apply notQP  -- apply では数段階あっても最初と最後だけが意味を持つ
  assumption
  assumption


/- and が仮定あるいは結論にある命題の処理 -/

example {m n : ℕ} (h : m ∣ n ∧ m ≠ n) : m ∣ n ∧ ¬n ∣ m := by
  obtain ⟨h1,h2⟩ := h
  constructor
  assumption
  by_contra hn
  -- obtain ⟨h1,h2⟩ := h
  apply h2
  exact Nat.dvd_antisymm h1 hn -- 0 の場合がどう処理されているかはまだ未確認

example {m n : ℕ} (h : m ∣ n ∧ m ≠ n) : m ∣ n ∧ ¬n ∣ m := by
  rcases h with ⟨h1,h2⟩
  constructor
  assumption
  intro hn
  apply h2
  exact Nat.dvd_antisymm h1 hn


theorem aux {x y : ℝ} (h : x ^ 2 + y ^ 2 = 0) : x = 0 := by
  have h' : x ^ 2 = 0 := by linarith [pow_two_nonneg x, pow_two_nonneg y]
  -- linarith は後ろの [] の中の不等式と Goal で矛盾を導く. この場合は?
  exact pow_eq_zero h'

example (x y : ℝ) : x ^ 2 + y ^ 2 = 0 ↔ x = 0 ∧ y = 0 := by
  constructor
  ·  intro H
     constructor
     · apply aux H
     · rw [add_comm] at H
       apply aux H

  ·  intro Hxy
     obtain ⟨hx,hy⟩ := Hxy
     rw [hx,hy]
     norm_num

/- or の処理 -/
namespace MyAbs

#loogle abs

theorem le_abs_self (x : ℝ) : x ≤ |x| := by
  cases le_or_gt 0 x -- 三つに場合分けする場合は
  next h =>
    rw [abs_of_nonneg]
    assumption
  next h =>
    rw [abs_of_neg]
    linarith
    assumption


theorem neg_le_abs_self (x : ℝ) : -x ≤ |x| := by
  cases lt_or_ge 0 x
  next h =>
    apply le_trans
    show - x ≤ 0
    linarith
    exact abs_nonneg x
  next h =>
    rw [abs_of_nonpos]
    assumption

theorem abs_add (x y : ℝ) : |x + y| ≤ |x| + |y| := by
  cases le_or_gt 0 (x+y)
  next hxy =>
     rw [abs_of_nonneg]
     apply add_le_add
     apply le_abs_self
     apply le_abs_self
     apply hxy
  next hxy =>
     rw [abs_of_neg hxy]
     calc
       _ = -x + -y := by ring
       _ ≤  |x| + |y| := by apply add_le_add ;apply neg_le_abs_self;apply neg_le_abs_self
