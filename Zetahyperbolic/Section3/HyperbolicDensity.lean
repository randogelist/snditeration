import Zetahyperbolic.Section2.Moments
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence

noncomputable section
open scoped BigOperators
open MeasureTheory Set

namespace ManuscriptChain.Hyperbolic

def exponentialTerm (k n : ℕ) (y : ℝ) : ℝ :=
  ((n + 1 : ℕ) : ℝ) ^ (2 * k) *
    Real.exp (-(2 * Real.pi * y) * ((n + 1 : ℕ) : ℝ))

def density (k : ℕ) (y : ℝ) : ℝ :=
  (2 * (2 * Real.pi) ^ (2 * k) / (Nat.factorial (2 * k) : ℝ)) *
    y ^ (2 * k + 1) * ∑' n : ℕ, exponentialTerm k n y

theorem exponentialTerm_pos (k n : ℕ) (y : ℝ) :
    0 < exponentialTerm k n y := by
  unfold exponentialTerm
  positivity

theorem summable_exponentialTerm (k : ℕ) {y : ℝ} (hy : 0 < y) :
    Summable (fun n : ℕ => exponentialTerm k n y) := by
  exact (summable_nat_add_iff 1).mpr
    (Real.summable_pow_mul_exp_neg_nat_mul (2 * k)
      (show 0 < 2 * Real.pi * y by positivity))

theorem exponentialSeries_pos (k : ℕ) {y : ℝ} (hy : 0 < y) :
    0 < ∑' n : ℕ, exponentialTerm k n y := by
  exact (summable_exponentialTerm k hy).tsum_pos
    (fun n => (exponentialTerm_pos k n y).le) 0 (exponentialTerm_pos k 0 y)

theorem density_pos (k : ℕ) {y : ℝ} (hy : 0 < y) : 0 < density k y := by
  unfold density
  exact mul_pos (by positivity) (exponentialSeries_pos k hy)

theorem density_nonneg (k : ℕ) {y : ℝ} (hy : 0 ≤ y) : 0 ≤ density k y := by
  rcases eq_or_lt_of_le hy with rfl | hy
  · simp [density]
  · exact (density_pos k hy).le

theorem density_zero (k : ℕ) : density k 0 = 0 := by
  simp [density]

theorem measurable_exponentialTerm (k n : ℕ) : Measurable (exponentialTerm k n) := by
  unfold exponentialTerm
  fun_prop

theorem measurable_density (k : ℕ) : Measurable (density k) := by
  unfold density
  exact (measurable_const.mul (measurable_id.pow_const _)).mul
    (Measurable.tsum (fun n => measurable_exponentialTerm k n))

end ManuscriptChain.Hyperbolic
