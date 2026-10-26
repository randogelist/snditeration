import Zetahyperbolic.Section3.HyperbolicMomentBernoulli
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
Direct integral kernel scaling, part I: nonnegative terms and
integrability bounds for the paper's simple-pole kernel.
-/

noncomputable section
open scoped BigOperators
open Set MeasureTheory

namespace ManuscriptChain.Hyperbolic

def poleTerm (k n : ℕ) (a y : ℝ) : ℝ :=
  momentTerm k 0 n y / (y ^ 2 + a ^ 2)

def scaledPoleTerm (k n : ℕ) (a t : ℝ) : ℝ :=
  (t ^ (2 * k + 1) * Real.exp (-(2 * Real.pi * t))) /
    (t ^ 2 + (a * ((n + 1 : ℕ) : ℝ)) ^ 2)

theorem poleTerm_nonneg (k n : ℕ) {a y : ℝ} (hy : 0 ≤ y) :
    0 ≤ poleTerm k n a y := by
  unfold poleTerm
  exact div_nonneg (momentTerm_nonneg _ _ _ hy) (add_nonneg (sq_nonneg _) (sq_nonneg _))

theorem norm_poleTerm_le (k n : ℕ) {a y : ℝ} (ha : 0 < a) (hy : 0 ≤ y) :
    ‖poleTerm k n a y‖ ≤ (1 / a ^ 2) * momentTerm k 0 n y := by
  rw [Real.norm_of_nonneg (poleTerm_nonneg k n hy)]
  unfold poleTerm
  have h := div_le_div_of_nonneg_left (momentTerm_nonneg k 0 n hy)
    (show 0 < a ^ 2 by positivity) (show a ^ 2 ≤ y ^ 2 + a ^ 2 by nlinarith [sq_nonneg y])
  simpa [div_eq_mul_inv, mul_comm] using h

theorem poleTerm_integrable (k n : ℕ) {a : ℝ} (ha : 0 < a) :
    IntegrableOn (poleTerm k n a) (Ioi 0) := by
  apply ((momentTerm_integrable k 0 n).const_mul (1 / a ^ 2)).mono'
  · exact (show Measurable (poleTerm k n a) by
      unfold poleTerm momentTerm
      fun_prop).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    exact norm_poleTerm_le k n ha hy.le

theorem summable_integral_norm_poleTerm (k : ℕ) {a : ℝ} (ha : 0 < a) :
    Summable (fun n : ℕ => ∫ y in Ioi (0 : ℝ), ‖poleTerm k n a y‖) := by
  apply Summable.of_nonneg_of_le (fun _ => integral_nonneg (fun _ => norm_nonneg _)) _
    ((summable_integral_norm_momentTerm k 0).mul_left (1 / a ^ 2))
  intro n
  rw [← integral_const_mul]
  apply integral_mono_ae (poleTerm_integrable k n ha).norm
    ((momentTerm_integrable k 0 n).norm.const_mul _)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  rw [Real.norm_of_nonneg (momentTerm_nonneg k 0 n hy.le)]
  exact norm_poleTerm_le k n ha hy.le

theorem scaledPoleTerm_nonneg (k n : ℕ) {a t : ℝ} (ht : 0 ≤ t) :
    0 ≤ scaledPoleTerm k n a t := by
  unfold scaledPoleTerm
  positivity

theorem norm_scaledPoleTerm_le (k n : ℕ) {a t : ℝ} (ha : 0 < a) (ht : 0 ≤ t) :
    ‖scaledPoleTerm k n a t‖ ≤
      (1 / (a * ((n + 1 : ℕ) : ℝ)) ^ 2) *
        (t ^ (2 * k + 1) * Real.exp (-(2 * Real.pi * t))) := by
  rw [Real.norm_of_nonneg (scaledPoleTerm_nonneg k n ht)]
  unfold scaledPoleTerm
  have h := div_le_div_of_nonneg_left
    (show 0 ≤ t ^ (2 * k + 1) * Real.exp (-(2 * Real.pi * t)) by positivity)
    (show 0 < (a * ((n + 1 : ℕ) : ℝ)) ^ 2 by positivity)
    (show (a * ((n + 1 : ℕ) : ℝ)) ^ 2 ≤
      t ^ 2 + (a * ((n + 1 : ℕ) : ℝ)) ^ 2 by nlinarith [sq_nonneg t])
  simpa [div_eq_mul_inv, mul_comm] using h

theorem scaledPoleTerm_integrable (k n : ℕ) {a : ℝ} (ha : 0 < a) :
    IntegrableOn (scaledPoleTerm k n a) (Ioi 0) := by
  apply ((integrableOn_pow_mul_exp (2 * k + 1) (by positivity : 0 < 2 * Real.pi)).const_mul
    (1 / (a * ((n + 1 : ℕ) : ℝ)) ^ 2)).mono'
  · exact (show Measurable (scaledPoleTerm k n a) by
      unfold scaledPoleTerm
      fun_prop).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact norm_scaledPoleTerm_le k n ha ht.le

end ManuscriptChain.Hyperbolic
