import Zetahyperbolic.Section3.HyperbolicMomentBernoulli
import Zetahyperbolic.Section3.HyperbolicMeasure
import Zetahyperbolic.Section3.PositiveMomentRealization
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
The concrete positive measure for the rational Hankel kernel. The canceled
weight uses the exact numerator and tail denominator of Definition 2.1.
The only input to `realization` is the entry integral identity; positivity,
nondegeneracy, atomlessness and moment integrability are proved here.
-/

noncomputable section
open scoped BigOperators
open MeasureTheory Set Polynomial

namespace ManuscriptChain.ConcreteMoment

theorem evalQ_D (n : ℕ) (t : ℝ) :
    Real.evalQ (Real.D n) t =
      ∏ j ∈ Finset.range n, (t + ((j + 1 : ℕ) : ℝ) ^ 2) := by
  simp [Real.evalQ, Real.realPolynomial, Real.D, Polynomial.map_prod, Polynomial.eval_prod]

theorem evalQ_tailD (p : Real.Parameters) (t : ℝ) :
    Real.evalQ (Real.tailD p) t =
      ∏ a ∈ Finset.Icc (p.N + 1) p.K, (t + (a : ℝ) ^ 2) := by
  simp [Real.evalQ, Real.realPolynomial, Real.tailD, Polynomial.map_prod, Polynomial.eval_prod]

theorem evalQ_D_pos (n : ℕ) {t : ℝ} (ht : 0 < t) :
    0 < Real.evalQ (Real.D n) t := by
  rw [evalQ_D]
  apply Finset.prod_pos
  intro a ha
  positivity

theorem evalQ_tailD_ge_one (p : Real.Parameters) {t : ℝ} (ht : 0 ≤ t) :
    1 ≤ Real.evalQ (Real.tailD p) t := by
  rw [evalQ_tailD]
  apply Finset.one_le_prod
  intro a ha
  have haN : 1 ≤ a := by have h := (Finset.mem_Icc.mp ha).1; omega
  have haR : (1 : ℝ) ≤ a := by exact_mod_cast haN
  nlinarith

def weightedDensity (p : Real.Parameters) (y : ℝ) : ℝ :=
  Real.evalQ (Real.D p.N ^ (2 * p.m - 1)) (y ^ 2) /
    Real.evalQ (Real.tailD p) (y ^ 2) * Hyperbolic.density p.k y

theorem weightedDensity_pos (p : Real.Parameters) {y : ℝ} (hy : 0 < y) :
    0 < weightedDensity p y := by
  have hN := evalQ_D_pos p.N (show 0 < y ^ 2 by positivity)
  have hK := evalQ_tailD_ge_one p (sq_nonneg y)
  unfold weightedDensity
  rw [Real.evalQ, Real.realPolynomial, Polynomial.map_pow, Polynomial.eval_pow]
  exact mul_pos (div_pos (pow_pos hN _) (by linarith))
    (Hyperbolic.density_pos p.k hy)

theorem measurable_weightedDensity (p : Real.Parameters) :
    Measurable (weightedDensity p) := by
  unfold weightedDensity Real.evalQ
  apply Measurable.mul _ (Hyperbolic.measurable_density p.k)
  fun_prop

def weightedMeasure (p : Real.Parameters) : Measure ℝ :=
  (volume.restrict (Ioi 0)).withDensity
    (fun y => ENNReal.ofReal (weightedDensity p y))

instance weightedMeasure_nullSingleton (p : Real.Parameters) :
    NullSingletonClass (weightedMeasure p) := by
  unfold weightedMeasure
  infer_instance

theorem weightedMeasure_nonzero (p : Real.Parameters) : weightedMeasure p ≠ 0 := by
  have hac : volume.restrict (Ioi (0 : ℝ)) ≪ weightedMeasure p := by
    apply withDensity_absolutelyContinuous'
      (measurable_weightedDensity p).ennreal_ofReal.aemeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (weightedDensity_pos p hy))
  intro hzero
  rw [hzero] at hac
  have h := Measure.absolutelyContinuous_zero_iff.mp hac
  have hu := congrArg (fun μ : Measure ℝ => μ Set.univ) h
  simp at hu

/-- The actual moment measure in the variable `t = y^2`. -/
def momentMeasure (p : Real.Parameters) : Measure ℝ :=
  (weightedMeasure p).map (fun y : ℝ => y ^ 2)

theorem momentMeasure_nonzero (p : Real.Parameters) : momentMeasure p ≠ 0 := by
  exact (Measure.map_ne_zero_iff (by fun_prop)).2 (weightedMeasure_nonzero p)

instance momentMeasure_nullSingleton (p : Real.Parameters) :
    NullSingletonClass (momentMeasure p) := by
  constructor
  intro t
  rw [momentMeasure, Measure.map_apply (by fun_prop) (measurableSet_singleton t)]
  have hq : (X ^ 2 - C t : ℝ[X]) ≠ 0 := by
    intro h
    have hcoeff := congrArg (fun q : ℝ[X] => q.coeff 2) h
    norm_num at hcoeff
  have hz := (Polynomial.finite_setOfPred_isRoot hq).measure_zero (weightedMeasure p)
  have hs : (fun y : ℝ => y ^ 2) ⁻¹' {t} =
      {y | Polynomial.IsRoot (X ^ 2 - C t : ℝ[X]) y} := by
    ext y
    simp [Polynomial.IsRoot, sub_eq_zero]
  rw [hs]
  exact hz

/-- The pushforward moment equals the original positive-half-line integral. -/
theorem integral_momentMeasure (p : Real.Parameters) (e : ℕ) :
    (∫ t, t ^ e ∂momentMeasure p) =
      ∫ y in Ioi (0 : ℝ), y ^ (2 * e) * weightedDensity p y := by
  rw [momentMeasure, integral_map (by fun_prop) (by fun_prop), weightedMeasure,
    integral_withDensity_eq_integral_toReal_smul
      (measurable_weightedDensity p).ennreal_ofReal (by simp)]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  rw [ENNReal.toReal_ofReal (weightedDensity_pos p hy).le]
  simp only [smul_eq_mul]
  rw [← pow_mul]
  ring

/-- Moment integrability in the two coordinates is equivalent. -/
theorem integrable_momentMeasure_iff (p : Real.Parameters) (e : ℕ) :
    Integrable (fun t : ℝ => t ^ e) (momentMeasure p) ↔
      IntegrableOn (fun y : ℝ => y ^ (2 * e) * weightedDensity p y) (Ioi 0) := by
  rw [momentMeasure, integrable_map_measure (by fun_prop) (by fun_prop),
    weightedMeasure, integrable_withDensity_iff_integrable_smul'
      (measurable_weightedDensity p).ennreal_ofReal (by simp)]
  apply integrable_congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  rw [ENNReal.toReal_ofReal (weightedDensity_pos p hy).le]
  simp only [Function.comp_def, smul_eq_mul]
  rw [← pow_mul]
  ring

/-- Every polynomial in `y^2` is integrable against the base density. -/
theorem integrableOn_polynomial_density (k : ℕ) (q : ℝ[X]) :
    IntegrableOn (fun y : ℝ => q.eval (y ^ 2) * Hyperbolic.density k y) (Ioi 0) := by
  have hi := integrable_finsetSum q.support (fun e _ =>
    (Hyperbolic.integrableOn_monomial_density k e).const_mul (q.coeff e))
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
theorem integrableOn_weightedDensity_moment (p : Real.Parameters) (e : ℕ) :
    IntegrableOn (fun y : ℝ => y ^ (2 * e) * weightedDensity p y) (Ioi 0) := by
  let q : ℝ[X] := Real.realPolynomial (Real.D p.N ^ (2 * p.m - 1)) * X ^ e
  have heval (y : ℝ) : q.eval (y ^ 2) =
      Real.evalQ (Real.D p.N ^ (2 * p.m - 1)) (y ^ 2) * y ^ (2 * e) := by
    simp only [q, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X,
      Real.evalQ, ← pow_mul]
  have hi := integrableOn_polynomial_density p.k q
  apply hi.mono' ((measurable_id.pow_const _).mul
    (measurable_weightedDensity p)).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  have hypos : 0 < y := hy
  rw [Real.norm_eq_abs, abs_of_nonneg (by
    exact mul_nonneg (pow_nonneg hypos.le _) (weightedDensity_pos p hypos).le)]
  rw [heval]
  have hN : 0 ≤ Real.evalQ (Real.D p.N ^ (2 * p.m - 1)) (y ^ 2) := by
    have h := (evalQ_D_pos p.N (show 0 < y ^ 2 by positivity)).le
    simpa [Real.evalQ, Real.realPolynomial] using pow_nonneg h (2 * p.m - 1)
  have hratio := div_le_self hN (evalQ_tailD_ge_one p (sq_nonneg y))
  have hmul := mul_le_mul_of_nonneg_right hratio (Hyperbolic.density_pos p.k hypos).le
  have htotal := mul_le_mul_of_nonneg_left hmul (pow_nonneg hypos.le (2 * e))
  simpa [weightedDensity, mul_assoc, mul_left_comm, mul_comm] using htotal

/-- All measure nondegeneracy obligations are constructed here. This version
takes only the exact entry identities as an input. Moment integrability is proved. -/
def realization (p : Real.Parameters)
    (hentry : ∀ i j : Fin p.h,
      Real.gram p (Real.zeta p.weight) i j =
        ∫ y in Ioi (0 : ℝ), y ^ (2 * (i.val + j.val)) * weightedDensity p y) :
    Real.PositiveMomentRealization p where
  measure := momentMeasure p
  nullSingleton := inferInstance
  nonzero := momentMeasure_nonzero p
  integrable_moments := fun i j => (integrable_momentMeasure_iff p (i.val + j.val)).2
    (integrableOn_weightedDensity_moment p (i.val + j.val))
  moment_identity := fun i j => (hentry i j).trans (integral_momentMeasure p _).symm

end ManuscriptChain.ConcreteMoment
