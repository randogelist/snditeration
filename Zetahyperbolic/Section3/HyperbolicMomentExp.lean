import Zetahyperbolic.Section3.HyperbolicMeasure
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Tactic

/-!
Polynomial moments of the actual positive density, part I.
Exponential kernels, integrability and interchange of sum and integral.
-/

noncomputable section
open scoped BigOperators
open Set MeasureTheory

namespace ManuscriptChain.Hyperbolic

theorem integral_pow_mul_exp (d : ℕ) {a : ℝ} (ha : 0 < a) :
    (∫ y : ℝ in Ioi 0, y ^ d * Real.exp (-(a * y))) =
      (Nat.factorial d : ℝ) / a ^ (d + 1) := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi
    (a := (d : ℝ) + 1) (r := a) (by positivity) ha
  simp only [add_sub_cancel_right, Real.rpow_natCast, Real.Gamma_nat_eq_factorial] at h
  rw [show (d : ℝ) + 1 = ((d + 1 : ℕ) : ℝ) by push_cast; rfl,
    Real.rpow_natCast, one_div_pow] at h
  simpa only [one_div, inv_mul_eq_div] using h

theorem integrableOn_pow_mul_exp (d : ℕ) {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun y : ℝ => y ^ d * Real.exp (-(a * y))) (Ioi 0) := by
  apply Integrable.of_integral_ne_zero
  rw [integral_pow_mul_exp d ha]
  positivity

def momentTerm (k e n : ℕ) (y : ℝ) : ℝ :=
  ((n + 1 : ℕ) : ℝ) ^ (2 * k) *
    (y ^ (2 * k + 2 * e + 1) *
      Real.exp (-((2 * Real.pi * ((n + 1 : ℕ) : ℝ)) * y)))

def momentCoefficient (k e : ℕ) : ℝ :=
  (Nat.factorial (2 * k + 2 * e + 1) : ℝ) /
    (2 * Real.pi) ^ (2 * k + 2 * e + 2)

theorem momentTerm_integrable (k e n : ℕ) :
    IntegrableOn (momentTerm k e n) (Ioi 0) := by
  unfold momentTerm
  exact (integrableOn_pow_mul_exp _ (by positivity)).const_mul _

theorem integral_momentTerm (k e n : ℕ) :
    (∫ y : ℝ in Ioi 0, momentTerm k e n y) =
      momentCoefficient k e * (1 / ((n + 1 : ℕ) : ℝ) ^ (2 * e + 2)) := by
  unfold momentTerm momentCoefficient
  rw [integral_const_mul, integral_pow_mul_exp _ (by positivity)]
  have hn : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hp : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  have he : 2 * k + 2 * e + 1 + 1 = 2 * k + (2 * e + 2) := by omega
  rw [he, mul_pow, pow_add, pow_add]
  field_simp
  simp only [pow_add]

theorem momentTerm_nonneg (k e n : ℕ) {y : ℝ} (hy : 0 ≤ y) :
    0 ≤ momentTerm k e n y := by
  unfold momentTerm
  positivity

theorem summable_integral_norm_momentTerm (k e : ℕ) :
    Summable (fun n => ∫ y : ℝ in Ioi 0, ‖momentTerm k e n y‖) := by
  have h (n : ℕ) : (∫ y : ℝ in Ioi 0, ‖momentTerm k e n y‖) =
      momentCoefficient k e * (1 / ((n + 1 : ℕ) : ℝ) ^ (2 * e + 2)) := by
    rw [← integral_momentTerm]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro y hy
    exact Real.norm_of_nonneg (momentTerm_nonneg k e n hy.le)
  simp_rw [h]
  exact (Real.zeta_series_summable (s := 2 * e + 2) (by omega)).mul_left _

theorem integral_tsum_momentTerm (k e : ℕ) :
    (∫ y : ℝ in Ioi 0, ∑' n, momentTerm k e n y) =
      momentCoefficient k e * Real.zeta (2 * e + 2) := by
  rw [← integral_tsum_of_summable_integral_norm (momentTerm_integrable k e)
    (summable_integral_norm_momentTerm k e)]
  simp_rw [integral_momentTerm]
  rw [tsum_mul_left]
  rfl

theorem integrableOn_tsum_momentTerm (k e : ℕ) :
    IntegrableOn (fun y : ℝ => ∑' n, momentTerm k e n y) (Ioi 0) := by
  apply Integrable.of_integral_ne_zero
  rw [integral_tsum_momentTerm]
  exact mul_ne_zero (ne_of_gt (by unfold momentCoefficient; positivity))
    (ne_of_gt (Real.zeta_pos (by omega)))

end ManuscriptChain.Hyperbolic
