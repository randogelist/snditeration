import Zetahyperbolic.Section3.PoleScalingCore

/-!
Rescaled simple-pole integral, part II:
the exact hyperbolic pole integral reduces to an elementary
resolvent sum. No special-function evaluation is assumed.
-/

noncomputable section
open scoped BigOperators
open Set MeasureTheory

namespace ManuscriptChain.Hyperbolic

theorem summable_scaledPole_bound (a : ℝ) :
    Summable (fun n : ℕ => 1 / (a * ((n + 1 : ℕ) : ℝ)) ^ 2) := by
  simp_rw [mul_pow, one_div, mul_inv]
  simpa only [one_div] using
    (Real.zeta_series_summable (s := 2) (by omega)).mul_left ((a ^ 2)⁻¹)

theorem summable_integral_norm_scaledPoleTerm (k : ℕ) {a : ℝ} (ha : 0 < a) :
    Summable (fun n => ∫ t in Ioi (0 : ℝ), ‖scaledPoleTerm k n a t‖) := by
  apply Summable.of_nonneg_of_le (fun _ => integral_nonneg (fun _ => norm_nonneg _)) _
    ((summable_scaledPole_bound a).mul_right
      ((Nat.factorial (2 * k + 1) : ℝ) / (2 * Real.pi) ^ (2 * k + 2)))
  intro n
  rw [show 2 * k + 2 = (2 * k + 1) + 1 by omega, ← integral_pow_mul_exp (2 * k + 1)
    (by positivity : 0 < 2 * Real.pi), ← integral_const_mul]
  apply integral_mono_ae (scaledPoleTerm_integrable k n ha).norm
    ((integrableOn_pow_mul_exp (2 * k + 1) (by positivity : 0 < 2 * Real.pi)).const_mul _)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact norm_scaledPoleTerm_le k n ha ht.le

theorem poleTerm_eq_scaled (k n : ℕ) {a : ℝ} (ha : 0 < a) (y : ℝ) :
    poleTerm k n a y = ((n + 1 : ℕ) : ℝ) *
      scaledPoleTerm k n a (((n + 1 : ℕ) : ℝ) * y) := by
  have hn : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hd : y ^ 2 + a ^ 2 ≠ 0 := by positivity
  unfold poleTerm momentTerm scaledPoleTerm
  simp only [Nat.mul_zero, Nat.add_zero, mul_pow, pow_add, pow_one]
  have he : -(2 * Real.pi * ((n + 1 : ℕ) : ℝ) * y) =
      -(2 * Real.pi * (((n + 1 : ℕ) : ℝ) * y)) := by ring
  rw [he]
  field_simp

theorem integral_poleTerm_eq_scaled (k n : ℕ) {a : ℝ} (ha : 0 < a) :
    (∫ y in Ioi (0 : ℝ), poleTerm k n a y) =
      ∫ t in Ioi (0 : ℝ), scaledPoleTerm k n a t := by
  simp_rw [poleTerm_eq_scaled k n ha]
  rw [integral_const_mul, integral_comp_mul_left_Ioi _ 0 (by positivity)]
  have hn : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  simp only [mul_zero, smul_eq_mul]
  rw [← mul_assoc, mul_inv_cancel₀ hn, one_mul]

theorem density_div_quadratic_eq_tsum (k : ℕ) (a y : ℝ) :
    density k y / (y ^ 2 + a ^ 2) =
      (2 * (2 * Real.pi) ^ (2 * k) / (Nat.factorial (2 * k) : ℝ)) *
        ∑' n, poleTerm k n a y := by
  have h := monomial_density_eq_tsum k 0 y
  simp only [Nat.mul_zero, pow_zero, one_mul] at h
  rw [h, mul_div_assoc, ← tsum_div_const]
  rfl

theorem tsum_scaledPoleTerm (k : ℕ) (a t : ℝ) :
    (∑' n, scaledPoleTerm k n a t) =
      (t ^ (2 * k + 1) * Real.exp (-(2 * Real.pi * t))) *
        ∑' n : ℕ, 1 / (t ^ 2 + (a * ((n + 1 : ℕ) : ℝ)) ^ 2) := by
  simp only [scaledPoleTerm, div_eq_mul_inv, one_mul]
  rw [tsum_mul_left]

theorem integral_density_div_quadratic (k : ℕ) {a : ℝ} (ha : 0 < a) :
    (∫ y in Ioi (0 : ℝ), density k y / (y ^ 2 + a ^ 2)) =
      (2 * (2 * Real.pi) ^ (2 * k) / (Nat.factorial (2 * k) : ℝ)) *
        ∫ t in Ioi (0 : ℝ),
          (t ^ (2 * k + 1) * Real.exp (-(2 * Real.pi * t))) *
            ∑' n : ℕ, 1 / (t ^ 2 + (a * ((n + 1 : ℕ) : ℝ)) ^ 2) := by
  simp_rw [density_div_quadratic_eq_tsum]
  rw [integral_const_mul,
    ← integral_tsum_of_summable_integral_norm (fun n => poleTerm_integrable k n ha)
      (summable_integral_norm_poleTerm k ha)]
  simp_rw [integral_poleTerm_eq_scaled k _ ha]
  rw [integral_tsum_of_summable_integral_norm (fun n => scaledPoleTerm_integrable k n ha)
    (summable_integral_norm_scaledPoleTerm k ha)]
  simp_rw [tsum_scaledPoleTerm]

end ManuscriptChain.Hyperbolic
