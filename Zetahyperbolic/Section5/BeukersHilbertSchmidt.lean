import Zetahyperbolic.Section5.BeukersMomentSeries
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Square-integrability of the actual Beukers kernel

The endpoint singularity is bounded by an explicit logarithmic polynomial.
Its square is integrable by the already proved one-variable log moments.
This discharges the analytic Hilbert–Schmidt prerequisite, without asserting
an arbitrary-L² signed-mode identity or definite-cone existence.
-/

noncomputable section
open MeasureTheory Set
open scoped BigOperators

namespace ManuscriptChain.Beukers

/-- Every natural logarithmic power of the product is integrable on the square. -/
theorem product_log_pow_integrable (n : ℕ) :
    Integrable (fun z : ℝ × ℝ => (-_root_.Real.log (z.1 * z.2)) ^ n)
      squareMeasure := by
  have hsingle (j : ℕ) :
      IntegrableOn (fun x : ℝ => (-_root_.Real.log x) ^ j) (Ioo 0 1) := by
    simpa using UnitLogMoments.integrable_pow_log 0 j
  have hsum : Integrable (fun z : ℝ × ℝ =>
      ((-_root_.Real.log z.1) + (-_root_.Real.log z.2)) ^ n) squareMeasure := by
    simp only [add_pow]
    unfold squareMeasure
    rw [← Measure.prod_restrict]
    apply integrable_finsetSum
    intro j _
    exact ((hsingle j).mul_prod (hsingle (n - j))).mul_const _
  apply hsum.congr
  filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioo)] with z hz
  rw [_root_.Real.log_mul hz.1.1.ne' hz.2.1.ne']
  congr 1
  ring

/-- Elementary domination that cancels the apparent singularity at `xy=1`. -/
theorem density_le_log_polynomial {z : ℝ × ℝ} (hz : z ∈ square) :
    0 ≤ density z ∧
      density z ≤ (-_root_.Real.log (z.1 * z.2)) ^ 5 +
        (-_root_.Real.log (z.1 * z.2)) ^ 4 := by
  let u := z.1 * z.2
  have hu0 : 0 < u := mul_pos hz.1.1 hz.2.1
  have hu1 : u < 1 := by
    have h := mul_lt_mul_of_pos_right hz.1.2 hz.2.1
    dsimp [u]
    nlinarith [hz.2.2]
  have hL : 0 ≤ -_root_.Real.log u :=
    neg_nonneg.mpr (_root_.Real.log_nonpos hu0.le hu1.le)
  have hlog := mul_le_mul_of_nonneg_left
    (_root_.Real.one_sub_inv_le_log_of_pos hu0) hu0.le
  have hcancel : u * u⁻¹ = 1 := mul_inv_cancel₀ hu0.ne'
  have hbasic : (-_root_.Real.log u) * u ≤ 1 - u := by
    nlinarith
  have hpower := mul_le_mul_of_nonneg_left hbasic (pow_nonneg hL 4)
  have hnum : (-_root_.Real.log u) ^ 5 ≤
      ((-_root_.Real.log u) ^ 5 + (-_root_.Real.log u) ^ 4) * (1 - u) := by
    nlinarith [hpower]
  have hnonneg : 0 ≤
      ((-_root_.Real.log u) ^ 5 + (-_root_.Real.log u) ^ 4) * (1 - u) := by
    positivity
  have hscaled : (-_root_.Real.log u) ^ 5 ≤
      ((-_root_.Real.log u) ^ 5 + (-_root_.Real.log u) ^ 4) * (720 * (1 - u)) := by
    nlinarith
  change 0 ≤ (-_root_.Real.log u) ^ 5 / (720 * (1-u)) ∧ _
  constructor
  · positivity
  · exact (div_le_iff₀ (by positivity : 0 < (720 : ℝ) * (1-u))).2 hscaled

/-- The actual density is measurable, including its totalized boundary values. -/
theorem density_globally_measurable : Measurable density := by
  unfold density
  fun_prop

/-- The square of the actual printed density is integrable on the actual square. -/
theorem density_sq_integrable :
    Integrable (fun z : ℝ × ℝ => density z ^ 2) squareMeasure := by
  have hmajorant : Integrable (fun z : ℝ × ℝ =>
      ((-_root_.Real.log (z.1 * z.2)) ^ 5 +
        (-_root_.Real.log (z.1 * z.2)) ^ 4) ^ 2) squareMeasure := by
    have h := ((product_log_pow_integrable 10).add
      ((product_log_pow_integrable 9).const_mul 2)).add
        (product_log_pow_integrable 8)
    have he : (fun z : ℝ × ℝ =>
        ((-_root_.Real.log (z.1 * z.2)) ^ 5 +
          (-_root_.Real.log (z.1 * z.2)) ^ 4) ^ 2) =
        (fun z => ((-_root_.Real.log (z.1 * z.2)) ^ 10 +
          2 * (-_root_.Real.log (z.1 * z.2)) ^ 9) +
          (-_root_.Real.log (z.1 * z.2)) ^ 8) := by
      funext z
      ring
    rw [he]
    exact h
  apply hmajorant.mono' (density_globally_measurable.pow_const 2).aestronglyMeasurable
  filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioo)] with z hz
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  exact pow_le_pow_left₀ (density_le_log_polynomial hz).1
    (density_le_log_polynomial hz).2 2

/-- A genuine proof of the named experimental Hilbert–Schmidt prerequisite. -/
theorem actual_density_memLp_two : MemLp density (2 : ENNReal) squareMeasure :=
  (memLp_two_iff_integrable_sq density_globally_measurable.aestronglyMeasurable).2
    density_sq_integrable

end ManuscriptChain.Beukers
