import Zetahyperbolic.Section3.CothCore

/-!
Exact cotangent partial fractions at arbitrary positive pole spacing.
-/

noncomputable section
open scoped BigOperators

namespace ManuscriptChain.Hyperbolic

theorem coth_partial_fractions {t a : ℝ} (ht : 0 < t) (ha : 0 < a) :
    (∑' n : ℕ, 1 / (t ^ 2 + (a * ((n + 1 : ℕ) : ℝ)) ^ 2)) =
      Real.pi / (a * t) * (1 / 2 + 1 / (Real.exp (2 * Real.pi * t / a) - 1)) -
        1 / (2 * t ^ 2) := by
  have ha0 := ha.ne'
  have ht0 := ht.ne'
  have hscale : (∑' n : ℕ, 1 / (t ^ 2 + (a * ((n + 1 : ℕ) : ℝ)) ^ 2)) =
      (1 / a ^ 2) * ∑' n : ℕ, 1 / ((t / a) ^ 2 + ((n + 1 : ℕ) : ℝ) ^ 2) := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro n
    field_simp
  rw [hscale, coth_partial_fractions_one (div_pos ht ha)]
  rw [show 2 * Real.pi * (t / a) = 2 * Real.pi * t / a by ring]
  field_simp

end ManuscriptChain.Hyperbolic
