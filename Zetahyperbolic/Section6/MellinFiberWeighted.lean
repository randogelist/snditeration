import Zetahyperbolic.Section6.MellinFiber
import Zetahyperbolic.Section5.BeukersPolynomialIntegral

/-!
# The actual weighted Mellin fiber integral

The logarithmic geometric series is absolutely integrable. This identifies the
one-variable fiber moments with the already calibrated unit-square moments,
then proves the literal finite-polynomial integral identity by finite linearity.
-/
noncomputable section
open MeasureTheory Set
open scoped BigOperators

namespace ManuscriptChain.Beukers.Mellin

def logTail (a m : ℕ) (u : ℝ) : ℝ :=
  u^a * (-_root_.Real.log u)^m / (1-u)

private theorem logTail_series (a m : ℕ) {u : ℝ} (hu : u ∈ Ioo 0 1) :
    logTail a m u = ∑' n : ℕ, u^(a+n) * (-_root_.Real.log u)^m := by
  have hn : ‖u‖ < 1 := by simpa [_root_.Real.norm_eq_abs, abs_of_pos hu.1] using hu.2
  have h := (hasSum_geometric_of_norm_lt_one hn).mul_left
    (u^a * (-_root_.Real.log u)^m)
  have ht : (fun n : ℕ => u^(a+n) * (-_root_.Real.log u)^m) =
      (fun n : ℕ => (u^a * (-_root_.Real.log u)^m) * u^n) := by
    funext n
    rw [pow_add]
    ring
  rw [ht, h.tsum_eq]
  simp only [logTail, div_eq_mul_inv]

private theorem integral_logTail_series (a m : ℕ) (hm : 0 < m) :
    (∫ u : ℝ in Ioo 0 1, ∑' n : ℕ, u^(a+n) * (-_root_.Real.log u)^m) =
      (m.factorial : ℝ) * (Real.zeta (m+1) - (Real.harmonic (m+1) a : ℝ)) := by
  have hs : Summable (fun n : ℕ =>
      ∫ u : ℝ in Ioo 0 1, ‖u^(a+n) * (-_root_.Real.log u)^m‖) := by
    have he (n : ℕ) :
        (∫ u : ℝ in Ioo 0 1, ‖u^(a+n) * (-_root_.Real.log u)^m‖) =
          (m.factorial : ℝ) * (1 / ((a+n+1 : ℕ) : ℝ)^(m+1)) := by
      calc
        _ = ∫ u : ℝ in Ioo 0 1, u^(a+n) * (-_root_.Real.log u)^m := by
          apply integral_congr_ae
          filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
          apply _root_.Real.norm_of_nonneg
          exact mul_nonneg (pow_nonneg hu.1.le _) (pow_nonneg
            (neg_nonneg.mpr (_root_.Real.log_nonpos hu.1.le hu.2.le)) _)
        _ = _ := by
          rw [UnitLogMoments.integral_pow_log]
          push_cast
          ring
    simp_rw [he]
    exact (Real.zeta_tail_summable (by omega : 1 < m+1) a).mul_left _
  rw [← integral_tsum_of_summable_integral_norm
    (fun n => UnitLogMoments.integrable_pow_log (a+n) m) hs]
  simp_rw [UnitLogMoments.integral_pow_log]
  have ht : (fun n : ℕ => (m.factorial : ℝ) / (((a+n : ℕ) : ℝ)+1)^(m+1)) =
      (fun n : ℕ => (m.factorial : ℝ) * (1 / ((a+n+1 : ℕ) : ℝ)^(m+1))) := by
    funext n
    push_cast
    ring
  rw [ht, tsum_mul_left, Real.zeta_tail_sum (by omega : 1 < m+1) a]

theorem integral_logTail (a m : ℕ) (hm : 0 < m) :
    (∫ u : ℝ in Ioo 0 1, logTail a m u) =
      (m.factorial : ℝ) * (Real.zeta (m+1) - (Real.harmonic (m+1) a : ℝ)) := by
  rw [setIntegral_congr_fun measurableSet_Ioo (fun u hu => logTail_series a m hu)]
  exact integral_logTail_series a m hm

theorem integrable_logTail (a m : ℕ) (hm : 0 < m) :
    IntegrableOn (logTail a m) (Ioo 0 1) := by
  apply Integrable.of_integral_ne_zero
  rw [integral_logTail a m hm]
  apply ne_of_gt
  apply mul_pos (by positivity)
  rw [← Real.zeta_tail_sum (by omega : 1 < m+1) a]
  exact (Real.zeta_tail_summable (by omega : 1 < m+1) a).tsum_pos
    (fun n => by positivity) 0 (by positivity)

theorem fiber_weight_eq (r t : ℕ) {u : ℝ} (hu : u ∈ Ioo 0 1) :
    fiberMonomial r t u * mellinWeight u =
      if r = t then logTail r 6 u / 720 else
        (logTail t 5 u - logTail r 5 u) / (720 * ((r : ℝ) - (t : ℝ))) := by
  have hl : _root_.Real.log u ≠ 0 := ne_of_lt (_root_.Real.log_neg hu.1 hu.2)
  have hu1 : 1-u ≠ 0 := ne_of_gt (sub_pos.mpr hu.2)
  by_cases hrt : r = t
  · simp only [fiberMonomial, if_pos hrt, mellinWeight, logTail]
    field_simp [hu1] <;> ring
  · have hrt' : (r : ℝ) - (t : ℝ) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hrt)
    simp only [fiberMonomial, if_neg hrt, mellinWeight, logTail]
    field_simp [hl, hu1, hrt'] <;> ring

theorem integrable_fiber_weight (r t : ℕ) :
    IntegrableOn (fun u => fiberMonomial r t u * mellinWeight u) (Ioo 0 1) := by
  by_cases hrt : r = t
  · apply ((integrable_logTail r 6 (by norm_num)).div_const 720).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
    simpa only [if_pos hrt] using (fiber_weight_eq r t hu).symm
  · apply (((integrable_logTail t 5 (by norm_num)).sub
      (integrable_logTail r 5 (by norm_num))).div_const
      (720 * ((r : ℝ)-(t : ℝ)))).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
    simpa only [if_neg hrt] using (fiber_weight_eq r t hu).symm

theorem integral_fiber_weight_eq_moment (r t : ℕ) :
    (∫ u : ℝ in Ioo 0 1, fiberMonomial r t u * mellinWeight u) =
      ∫ z, z.1^r * z.2^t * density z ∂squareMeasure := by
  rw [setIntegral_congr_fun measurableSet_Ioo (fun u hu => fiber_weight_eq r t hu)]
  by_cases hrt : r = t
  · subst t
    simp only [ite_true]
    rw [integral_div, integral_logTail r 6 (by norm_num), diagonal_moment]
    norm_num [Nat.factorial]
  · simp only [if_neg hrt]
    rw [integral_div, integral_sub (integrable_logTail t 5 (by norm_num))
      (integrable_logTail r 5 (by norm_num)),
      integral_logTail t 5 (by norm_num), integral_logTail r 5 (by norm_num),
      offdiagonal_moment r t hrt]
    have hrt' : (r : ℝ) - (t : ℝ) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hrt)
    norm_num [Nat.factorial]
    field_simp [hrt'] <;> ring

def coefficientFiber {K : ℕ} (c d : Fin (K+1) → ℚ) (u : ℝ) : ℝ :=
  ∑ r : Fin (K+1), ∑ t : Fin (K+1),
    (c r : ℝ) * (d t : ℝ) * fiberMonomial r.val t.val u

theorem integrable_coefficientFiber_weight {K : ℕ} (c d : Fin (K+1) → ℚ) :
    IntegrableOn (fun u => coefficientFiber c d u * mellinWeight u) (Ioo 0 1) := by
  have he : (fun u => coefficientFiber c d u * mellinWeight u) =
      (fun u => ∑ r : Fin (K+1), ∑ t : Fin (K+1),
        ((c r : ℝ) * (d t : ℝ)) * (fiberMonomial r.val t.val u * mellinWeight u)) := by
    funext u
    simp only [coefficientFiber, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro r _
    apply Finset.sum_congr rfl
    intro t _
    ring
  rw [he]
  apply integrable_finsetSum
  intro r _
  apply integrable_finsetSum
  intro t _
  exact (integrable_fiber_weight r.val t.val).const_mul _

theorem integral_coefficientFiber_weight {K : ℕ} (c d : Fin (K+1) → ℚ) :
    (∫ u : ℝ in Ioo 0 1, coefficientFiber c d u * mellinWeight u) =
      ∫ z, coefficientPolynomialValue c z.1 * coefficientPolynomialValue d z.2 *
        density z ∂squareMeasure := by
  rw [integral_polynomial_product_eq_momentForm]
  have he : (fun u => coefficientFiber c d u * mellinWeight u) =
      (fun u => ∑ r : Fin (K+1), ∑ t : Fin (K+1),
        ((c r : ℝ) * (d t : ℝ)) * (fiberMonomial r.val t.val u * mellinWeight u)) := by
    funext u
    simp only [coefficientFiber, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro r _
    apply Finset.sum_congr rfl
    intro t _
    ring
  rw [he, integral_finsetSum]
  · unfold polynomialMomentForm
    apply Finset.sum_congr rfl
    intro r _
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro t _
      rw [integral_const_mul, integral_fiber_weight_eq_moment]
    · intro t _
      exact (integrable_fiber_weight r.val t.val).const_mul _
  · intro r _
    apply integrable_finsetSum
    intro t _
    exact (integrable_fiber_weight r.val t.val).const_mul _

/-- The weighted literal inner integral is integrable on the full open unit interval. -/
theorem integrable_fiber_polynomial_weight {K : ℕ} (c d : Fin (K+1) → ℚ) :
    IntegrableOn (fun u => fiber c d u * mellinWeight u) (Ioo 0 1) := by
  apply (integrable_coefficientFiber_weight c d).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
  change coefficientFiber c d u * mellinWeight u = fiber c d u * mellinWeight u
  rw [fiber_eq_sum c d hu]
  rfl

/-- Theorem 6.1(1): the literal double integral equals the weighted literal
fiber integral. No change-of-variables premise is supplied by the caller. -/
theorem polynomial_mellin_fiber_reduction {K : ℕ} (c d : Fin (K+1) → ℚ) :
    (∫ z, coefficientPolynomialValue c z.1 * coefficientPolynomialValue d z.2 *
      density z ∂squareMeasure) =
        ∫ u : ℝ in Ioo 0 1, fiber c d u * mellinWeight u := by
  rw [← integral_coefficientFiber_weight]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
  change coefficientFiber c d u * mellinWeight u = fiber c d u * mellinWeight u
  rw [fiber_eq_sum c d hu]
  rfl

end ManuscriptChain.Beukers.Mellin
