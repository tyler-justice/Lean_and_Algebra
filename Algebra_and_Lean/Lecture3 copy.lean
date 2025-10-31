import Mathlib

/-
第三回
論理に関する講義をする予定
MIL では関数の upper bound などに関しての問題がある.
-/

variable (a b c : ℝ)

#check max_le
#check le_max_left

example : max (max a b) c = max a (max b c) := by
  apply le_antisymm
  · apply max_le
    · apply max_le
      exact le_max_left a (max b c)
      apply le_trans
      show b ≤  max b c
      apply le_max_left
      apply le_max_right a (max b c)
    · apply le_trans
      show c ≤  max b c
      apply le_max_right
      apply le_max_right
  · apply max_le
    ·  apply le_trans
       show a ≤ max a b
       apply le_max_left
       apply le_max_left
    ·  apply max_le
       apply le_trans
       show b ≤  max a b
       apply le_max_right
       apply le_max_left
       apply le_max_right

/- この「証明」をみてどう感じるか, 考えるか? -/


def upperbound (c : ℝ)(f : ℝ → ℝ): Prop := ∀x : ℝ,  f x ≤ c

example (a b : ℝ) (f g : ℝ → ℝ) (hf : upperbound a f) (hg : upperbound b g) :
   upperbound (a + b) (fun x ↦ f x + g x) := by
   rw [upperbound]
   intro x
   apply add_le_add
   · apply hf
   · apply hg

def upperbound2 (f : ℝ → ℝ) : Prop := ∃c : ℝ, ∀ x : ℝ, f x ≤ c

example  (f g : ℝ → ℝ) (hf : upperbound2  f) (hg : upperbound2 g) :
    upperbound2 (fun x ↦ f x + g x ) := by
    rw [upperbound2]
    rcases hf with ⟨a,ha⟩
    rcases hg with ⟨b,hb⟩
    use a+b
    intro x
    apply add_le_add
    apply ha
    apply hb

def even (g : ℝ →  ℝ) : Prop := ∀x : ℝ, g x = g (-x)
def odd (h : ℝ → ℝ ) :Prop := ∀ x : ℝ, h x = - h (- x)

example (f g : ℝ → ℝ) (hf : even f) (hg : even g) : even (fun x ↦ f x + g x)
  := by
    rw [even]
    intro x
    rw [hf]
    rw [hg]

/- 関数が odd をどうやって定義するか? -/

def convergence (f: ℝ → ℝ) (a : ℝ) (b : ℝ) : Prop :=
   ∀ ε > 0,  ∃ δ  > 0, ∀ x : ℝ, |x - a| < δ → |f x - b| < ε

example  (f : ℝ  →  ℝ  ) (hf :f = (fun x ↦ x)) : convergence f 1 1 := by
  rw [convergence]
  intro ε hε
  use ε
  constructor
  assumption
  intro x hx
  rw [hf]
  simp
  assumption


lemma sum  (f: ℝ → ℝ)  (g : ℝ → ℝ ) (a : ℝ) (b : ℝ)
      (hf : convergence f 1 a) (hg : convergence g 1 b)
      : convergence (fun x ↦ f x + g x) 1 (a + b) := by
    rw [convergence] at *
    intro ε εpos
    have ε2pos : 0 < ε / 2 := by linarith
    rcases hf (ε / 2) ε2pos with hf
    obtain  ⟨δ1,δ1pos,hf2⟩  := hf
    -- obtain  hδ1pos  := hδ1
    rcases hg (ε / 2) ε2pos with hg
    obtain  ⟨δ2,δ2pos,hg2⟩  := hg
    -- obtain  hδ2pos  := hδ2
    use min δ1 δ2
    constructor
    apply lt_min
    assumption
    assumption
    intro  x hx
    calc
      _ = |(f x - a) + (g x - b)| := by ring_nf
      _ ≤ |f x - a| + |g x - b| := by exact abs_add_le (f x - a) (g x - b)
    have aux1 : |f x - a| < ε /2 := by
      apply hf2
      apply lt_of_lt_of_le
      show |x - 1| < min δ1 δ2
      assumption
      apply min_le_left
    have aux2 : |g x - b| < ε /2 := by
      apply hg2
      apply lt_of_lt_of_le
      show |x - 1| < min δ1 δ2
      assumption
      apply min_le_right
    apply lt_of_lt_of_le
    show |f x - a| + |g x - b| < ε/2 + ε/2
    apply add_lt_add
    assumption
    assumption
    linarith

def continuous (f : ℝ → ℝ) : Prop :=  ∀ a : ℝ, ∀ ε > 0, ∃ δ > 0, ∀ x : ℝ, |x - a| < δ → |f x - f a| < ε

example  (f : ℝ → ℝ) (hf : f = id): continuous f := by
  sorry


example (f g : ℝ →  ℝ) (fcont : continuous f) (gcont : continuous g) :
   continuous (fun x ↦ f x + g x) := by sorry
