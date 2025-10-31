import Mathlib

example (a b c : ℝ): max (max a b) c = max a (max b c) := by
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
  · sorry


def even (f : ℝ → ℝ) : Prop := ∀x : ℝ, f x = f (-x)

def odd (f : ℝ → ℝ) : Prop := ∀x : ℝ, f (-x) = - (f x)

example (f g : ℝ → ℝ) (feven : even f) (godd : odd g) :
  odd (fun x ↦ (f x)*(g x)) := by sorry


def continuous (f : ℝ → ℝ) : Prop :=  ∀ a : ℝ, ∀ ε > 0, ∃ δ > 0, ∀ x : ℝ, |x - a| < δ → |f x - f a| < ε

example : continuous fun x ↦ x^2 := by sorry


example (f g : ℝ → ℝ) (fcont : continuous f) (gcont : continuous g) :
  continuous (fun x ↦ f x + g x) := by sorry
