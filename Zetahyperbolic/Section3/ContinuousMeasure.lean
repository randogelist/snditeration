import Zetahyperbolic.Section3.ContinuousDensity
import Zetahyperbolic.Section3.ConcreteMomentMeasure

/-! The actual positive rational-kernel measure for real weights s > 0. -/

noncomputable section
open scoped BigOperators
open MeasureTheory Set Polynomial

namespace ManuscriptChain.ContinuousWeight
open ConcreteMoment (evalQ_D_pos evalQ_tailD_ge_one)

def weightedDensity (p : Real.Parameters) (s : ℝ) (y : ℝ) : ℝ :=
  Real.evalQ (Real.D p.N ^ (2 * p.m - 1)) (y ^ 2) /
    Real.evalQ (Real.tailD p) (y ^ 2) * ContinuousWeight.density s y

theorem weightedDensity_pos (p : Real.Parameters) (s : ℝ) (hs : 0 < s) {y : ℝ} (hy : 0 < y) :
    0 < weightedDensity p s y := by
  have hN := evalQ_D_pos p.N (show 0 < y ^ 2 by positivity)
  have hK := evalQ_tailD_ge_one p (sq_nonneg y)
  unfold weightedDensity
  rw [Real.evalQ, Real.realPolynomial, Polynomial.map_pow, Polynomial.eval_pow]
  exact mul_pos (div_pos (pow_pos hN _) (by linarith))
    (ContinuousWeight.density_pos hs hy)

theorem measurable_weightedDensity (p : Real.Parameters) (s : ℝ) :
    Measurable (weightedDensity p s) := by
  unfold weightedDensity Real.evalQ
  apply Measurable.mul _ (ContinuousWeight.measurable_density s)
  fun_prop

def weightedMeasure (p : Real.Parameters) (s : ℝ) : Measure ℝ :=
  (volume.restrict (Ioi 0)).withDensity
    (fun y => ENNReal.ofReal (weightedDensity p s y))

instance weightedMeasure_nullSingleton (p : Real.Parameters) (s : ℝ) :
    NullSingletonClass (weightedMeasure p s) := by
  unfold weightedMeasure
  infer_instance

theorem weightedMeasure_nonzero (p : Real.Parameters) (s : ℝ) (hs : 0 < s) : weightedMeasure p s ≠ 0 := by
  have hac : volume.restrict (Ioi (0 : ℝ)) ≪ weightedMeasure p s := by
    apply withDensity_absolutelyContinuous'
      (measurable_weightedDensity p s).ennreal_ofReal.aemeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (weightedDensity_pos p s hs hy))
  intro hzero
  rw [hzero] at hac
  have h := Measure.absolutelyContinuous_zero_iff.mp hac
  have hu := congrArg (fun μ : Measure ℝ => μ Set.univ) h
  simp at hu

/-- The actual moment measure in the variable `t = y^2`. -/
def momentMeasure (p : Real.Parameters) (s : ℝ) : Measure ℝ :=
  (weightedMeasure p s).map (fun y : ℝ => y ^ 2)

theorem momentMeasure_nonzero (p : Real.Parameters) (s : ℝ) (hs : 0 < s) : momentMeasure p s ≠ 0 := by
  exact (Measure.map_ne_zero_iff (by fun_prop)).2 (weightedMeasure_nonzero p s hs)

instance momentMeasure_nullSingleton (p : Real.Parameters) (s : ℝ) :
    NullSingletonClass (momentMeasure p s) := by
  constructor
  intro t
  rw [momentMeasure, Measure.map_apply (by fun_prop) (measurableSet_singleton t)]
  have hq : (X ^ 2 - C t : ℝ[X]) ≠ 0 := by
    intro h
    have hcoeff := congrArg (fun q : ℝ[X] => q.coeff 2) h
    norm_num at hcoeff
  have hz := (Polynomial.finite_setOfPred_isRoot hq).measure_zero (weightedMeasure p s)
  have hs : (fun y : ℝ => y ^ 2) ⁻¹' {t} =
      {y | Polynomial.IsRoot (X ^ 2 - C t : ℝ[X]) y} := by
    ext y
    simp [Polynomial.IsRoot, sub_eq_zero]
  rw [hs]
  exact hz

/-- The pushforward moment equals the original positive-half-line integral. -/
theorem integral_momentMeasure (p : Real.Parameters) (s : ℝ) (hs : 0 < s) (e : ℕ) :
    (∫ t, t ^ e ∂momentMeasure p s) =
      ∫ y in Ioi (0 : ℝ), y ^ (2 * e) * weightedDensity p s y := by
  rw [momentMeasure, integral_map (by fun_prop) (by fun_prop), weightedMeasure,
    integral_withDensity_eq_integral_toReal_smul
      (measurable_weightedDensity p s).ennreal_ofReal (by simp)]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  rw [ENNReal.toReal_ofReal (weightedDensity_pos p s hs hy).le]
  simp only [smul_eq_mul]
  rw [← pow_mul]
  ring

/-- Moment integrability in the two coordinates is equivalent. -/
theorem integrable_momentMeasure_iff (p : Real.Parameters) (s : ℝ) (hs : 0 < s) (e : ℕ) :
    Integrable (fun t : ℝ => t ^ e) (momentMeasure p s) ↔
      IntegrableOn (fun y : ℝ => y ^ (2 * e) * weightedDensity p s y) (Ioi 0) := by
  rw [momentMeasure, integrable_map_measure (by fun_prop) (by fun_prop),
    weightedMeasure, integrable_withDensity_iff_integrable_smul'
      (measurable_weightedDensity p s).ennreal_ofReal (by simp)]
  apply integrable_congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  rw [ENNReal.toReal_ofReal (weightedDensity_pos p s hs hy).le]
  simp only [Function.comp_def, smul_eq_mul]
  rw [← pow_mul]
  ring

/-- Every polynomial in `y^2` is integrable against the base density. -/
theorem integrableOn_polynomial_density (s : ℝ) (hs : 0 < s) (q : ℝ[X]) :
    IntegrableOn (fun y : ℝ => q.eval (y ^ 2) * ContinuousWeight.density s y) (Ioi 0) := by
  have hi := integrable_finsetSum q.support (fun e _ =>
    (ContinuousWeight.integrableOn_monomial_density hs e).const_mul (q.coeff e))
  apply hi.congr
  filter_upwards [] with y
  symm
  simp only [Polynomial.eval_eq_sum, Polynomial.sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro e _
  rw [← pow_mul]
  ring

/-- The positive tail denominator is at least one, so polynomial moments
of the base density dominate every moment of the canceled kernel. -/
theorem integrableOn_weightedDensity_moment (p : Real.Parameters) (s : ℝ) (hs : 0 < s) (e : ℕ) :
    IntegrableOn (fun y : ℝ => y ^ (2 * e) * weightedDensity p s y) (Ioi 0) := by
  let q : ℝ[X] := Real.realPolynomial (Real.D p.N ^ (2 * p.m - 1)) * X ^ e
  have heval (y : ℝ) : q.eval (y ^ 2) =
      Real.evalQ (Real.D p.N ^ (2 * p.m - 1)) (y ^ 2) * y ^ (2 * e) := by
    simp only [q, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X,
      Real.evalQ, ← pow_mul]
  have hi := integrableOn_polynomial_density s hs q
  apply hi.mono' ((measurable_id.pow_const _).mul
    (measurable_weightedDensity p s)).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  have hypos : 0 < y := hy
  rw [Real.norm_eq_abs, abs_of_nonneg (by
    exact mul_nonneg (pow_nonneg hypos.le _) (weightedDensity_pos p s hs hypos).le)]
  rw [heval]
  have hN : 0 ≤ Real.evalQ (Real.D p.N ^ (2 * p.m - 1)) (y ^ 2) := by
    have h := (evalQ_D_pos p.N (show 0 < y ^ 2 by positivity)).le
    simpa [Real.evalQ, Real.realPolynomial] using pow_nonneg h (2 * p.m - 1)
  have hratio := div_le_self hN (evalQ_tailD_ge_one p (sq_nonneg y))
  have hmul := mul_le_mul_of_nonneg_right hratio (ContinuousWeight.density_pos hs hypos).le
  have htotal := mul_le_mul_of_nonneg_left hmul (pow_nonneg hypos.le (2 * e))
  simpa [weightedDensity, mul_assoc, mul_left_comm, mul_comm] using htotal


end ManuscriptChain.ContinuousWeight
