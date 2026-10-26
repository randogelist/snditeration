import Zetahyperbolic.Section3.LaplaceMomentDerivative
import Zetahyperbolic.Section3.ChristoffelDarboux

/-! Actual Laplace deformation of the manuscript weight.
Adapted from the companion zetahyperbolic-axiom source; no verification
status is inherited. All results are rechecked in the destination project. -/
noncomputable section
open scoped BigOperators Topology
open MeasureTheory Set Filter Matrix Polynomial

namespace ManuscriptChain.LaplaceGramMeasure

open ManuscriptChain LaplaceWeightDerivative LaplaceMomentDerivative

def weightedMeasure (p : Real.Parameters) (τ : ℝ) : Measure ℝ :=
  (volume.restrict (Ioi 0)).withDensity
    (fun y => ENNReal.ofReal (weightedDensity p τ y))

def momentMeasure (p : Real.Parameters) (τ : ℝ) : Measure ℝ :=
  (weightedMeasure p τ).map (fun y : ℝ => y^2)

def gram (p : Real.Parameters) (τ : ℝ) : Matrix (Fin p.h) (Fin p.h) ℝ :=
  fun i j => moment p (i.val+j.val) τ

theorem weightedDensity_positive (p : Real.Parameters) {τ y : ℝ}
    (hτ : 0 < τ) (hy : 0 < y) : 0 < weightedDensity p τ y :=
  mul_pos (weight_positive p hy) (density_positive p.k hτ hy)

instance weightedMeasure_nullSingleton (p : Real.Parameters) (τ : ℝ) :
    NullSingletonClass (weightedMeasure p τ) := by
  unfold weightedMeasure
  infer_instance

theorem weightedMeasure_nonzero (p : Real.Parameters) {τ : ℝ} (hτ : 0 < τ) :
    weightedMeasure p τ ≠ 0 := by
  have hac : volume.restrict (Ioi (0 : ℝ)) ≪ weightedMeasure p τ := by
    apply withDensity_absolutelyContinuous'
      (measurable_weightedDensity p τ).ennreal_ofReal.aemeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (weightedDensity_positive p hτ hy))
  intro hzero
  rw [hzero] at hac
  have h := Measure.absolutelyContinuous_zero_iff.mp hac
  have hu := congrArg (fun μ : Measure ℝ => μ Set.univ) h
  simp at hu

theorem momentMeasure_nonzero (p : Real.Parameters) {τ : ℝ} (hτ : 0 < τ) :
    momentMeasure p τ ≠ 0 :=
  (Measure.map_ne_zero_iff (by fun_prop)).2 (weightedMeasure_nonzero p hτ)

instance momentMeasure_nullSingleton (p : Real.Parameters) (τ : ℝ) :
    NullSingletonClass (momentMeasure p τ) := by
  constructor
  intro t
  rw [momentMeasure, Measure.map_apply (by fun_prop) (measurableSet_singleton t)]
  have hq : (X^2-C t : ℝ[X]) ≠ 0 := by
    intro h
    have hc := congrArg (fun q : ℝ[X] => q.coeff 2) h
    norm_num at hc
  have hz := (Polynomial.finite_setOfPred_isRoot hq).measure_zero (weightedMeasure p τ)
  have hs : (fun y : ℝ => y^2) ⁻¹' {t} =
      {y | Polynomial.IsRoot (X^2-C t : ℝ[X]) y} := by
    ext y
    simp [Polynomial.IsRoot, sub_eq_zero]
  rw [hs]
  exact hz

theorem integral_momentMeasure (p : Real.Parameters) (e : ℕ) {τ : ℝ} (hτ : 0 < τ) :
    (∫ t, t^e ∂momentMeasure p τ) = moment p e τ := by
  rw [momentMeasure, integral_map (by fun_prop) (by fun_prop), weightedMeasure,
    integral_withDensity_eq_integral_toReal_smul
      (measurable_weightedDensity p τ).ennreal_ofReal (by simp)]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  rw [ENNReal.toReal_ofReal (weightedDensity_positive p hτ hy).le]
  simp only [smul_eq_mul]
  rw [← pow_mul]
  ring

theorem integrable_momentMeasure (p : Real.Parameters) (e : ℕ) {τ : ℝ} (hτ : 0 < τ) :
    Integrable (fun t : ℝ => t^e) (momentMeasure p τ) := by
  rw [momentMeasure, integrable_map_measure (by fun_prop) (by fun_prop), weightedMeasure,
    integrable_withDensity_iff_integrable_smul'
      (measurable_weightedDensity p τ).ennreal_ofReal (by simp)]
  apply (integrable_moment p e hτ).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  rw [ENNReal.toReal_ofReal (weightedDensity_positive p hτ hy).le]
  simp only [Function.comp_def, smul_eq_mul]
  rw [← pow_mul]
  ring

theorem gram_eq_momentMatrix (p : Real.Parameters) {τ : ℝ} (hτ : 0 < τ) :
    gram p τ = Moments.momentMatrix (momentMeasure p τ) p.h := by
  ext i j
  exact (integral_momentMeasure p (i.val+j.val) hτ).symm

theorem gram_positive (p : Real.Parameters) {τ : ℝ} (hτ : 0 < τ) :
    (gram p τ).PosDef := by
  rw [gram_eq_momentMatrix p hτ]
  exact Moments.momentMatrix_posDef (momentMeasure_nonzero p hτ)
    (fun i j => integrable_momentMeasure p (i.val+j.val) hτ)

theorem gram_one (p : Real.Parameters) (hp : Real.Admissible p) :
    gram p 1 = Real.gram p (Real.zeta p.weight) := by
  ext i j
  rw [Hyperbolic.gram_eq_paper_integral p hp]
  unfold gram moment
  apply setIntegral_congr_fun measurableSet_Ioi
  intro y hy
  simp [weightedDensity, weight, density_one, LaplaceDenominator.D_real]

theorem gram_entry_hasDerivAt (p : Real.Parameters) {τ : ℝ} (hτ : 0 < τ)
    (i j : Fin p.h) :
    HasDerivAt (fun z => gram p z i j) (momentDerivative p (i.val+j.val) τ) τ :=
  moment_hasDerivAt p (i.val+j.val) hτ


end ManuscriptChain.LaplaceGramMeasure
