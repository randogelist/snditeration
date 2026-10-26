import Zetahyperbolic.Section3.LaplaceWeightDerivative

/-! Actual Laplace deformation of the manuscript weight.
Adapted from the companion zetahyperbolic-axiom source; no verification
status is inherited. All results are rechecked in the destination project. -/
noncomputable section
open scoped BigOperators Topology
open MeasureTheory Set Filter Matrix Polynomial

namespace ManuscriptChain.LaplaceDenominator

def D_real (n : ℕ) (t : ℝ) : ℝ := Real.evalQ (Real.D n) t

theorem D_real_pos (n : ℕ) {t : ℝ} (ht : 0 < t) : 0 < D_real n t :=
  ConcreteMoment.evalQ_D_pos n ht

theorem D_real_ge_one (n : ℕ) {t : ℝ} (ht : 0 < t) : 1 ≤ D_real n t := by
  rw [D_real, ConcreteMoment.evalQ_D]
  apply Finset.one_le_prod
  intro j hj
  have hcast : (1 : ℝ) ≤ ((j+1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ j+1)
  nlinarith

theorem D_real_ratio_pos (N K m : ℕ) {y : ℝ} (hy : 0 < y) :
    0 < D_real N (y^2)^(2*m) / D_real K (y^2) :=
  div_pos (pow_pos (D_real_pos N (by positivity)) _) (D_real_pos K (by positivity))

end ManuscriptChain.LaplaceDenominator

namespace ManuscriptChain.LaplaceMomentDerivative

open ManuscriptChain LaplaceWeightDerivative

def weight (p : Real.Parameters) (y : ℝ) : ℝ :=
  LaplaceDenominator.D_real p.N (y^2)^(2*p.m) / LaplaceDenominator.D_real p.K (y^2)

def weightedDensity (p : Real.Parameters) (τ y : ℝ) : ℝ :=
  weight p y * density p.k τ y

def moment (p : Real.Parameters) (e : ℕ) (τ : ℝ) : ℝ :=
  ∫ y in Ioi (0 : ℝ), y^(2*e)*weightedDensity p τ y

def momentDerivative (p : Real.Parameters) (e : ℕ) (τ : ℝ) : ℝ :=
  ∫ y in Ioi (0 : ℝ), y^(2*e)*weight p y*densityDerivative p.k τ y

theorem weight_positive (p : Real.Parameters) {y : ℝ} (hy : 0 < y) :
    0 < weight p y := LaplaceDenominator.D_real_ratio_pos p.N p.K p.m hy

theorem measurable_weight (p : Real.Parameters) : Measurable (weight p) := by
  unfold weight LaplaceDenominator.D_real Real.evalQ
  fun_prop

theorem measurable_weightedDensity (p : Real.Parameters) (τ : ℝ) :
    Measurable (weightedDensity p τ) :=
  (measurable_weight p).mul (measurable_density p.k τ)

theorem integrable_polynomial_density (k : ℕ) (q : ℝ[X]) {τ : ℝ} (hτ : 0 < τ) :
    IntegrableOn (fun y : ℝ => q.eval (y^2)*density k τ y) (Ioi 0) := by
  have hi := integrable_finsetSum q.support (fun e _ =>
    (integrable_monomial_density k e hτ).const_mul (q.coeff e))
  apply hi.congr
  filter_upwards [] with y
  symm
  simp only [Polynomial.eval_eq_sum, Polynomial.sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro e _
  rw [← pow_mul]
  ring

theorem integrable_moment (p : Real.Parameters) (e : ℕ) {τ : ℝ} (hτ : 0 < τ) :
    IntegrableOn (fun y : ℝ => y^(2*e)*weightedDensity p τ y) (Ioi 0) := by
  let q : ℝ[X] :=
    (Real.realPolynomial (Real.D p.N))^(2*p.m) * X^e
  have heval (y : ℝ) : q.eval (y^2) =
      LaplaceDenominator.D_real p.N (y^2)^(2*p.m)*y^(2*e) := by
    simp [q, LaplaceDenominator.D_real, Real.evalQ, ← pow_mul]

  apply (integrable_polynomial_density p.k q hτ).mono'
    (((measurable_id.pow_const _).mul (measurable_weightedDensity p τ)).aestronglyMeasurable)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  rw [Real.norm_eq_abs, abs_of_nonneg (by
    exact mul_nonneg (pow_nonneg hy.le _) (mul_nonneg
      (weight_positive p hy).le (density_positive p.k hτ hy).le))]
  rw [heval]
  have hr := div_le_self
    (pow_nonneg (LaplaceDenominator.D_real_pos p.N (show 0 < y^2 by positivity)).le (2*p.m))
    (LaplaceDenominator.D_real_ge_one p.K (show 0 < y^2 by positivity))
  have hh := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right hr (density_positive p.k hτ hy).le)
    (pow_nonneg hy.le (2*e))
  simpa [weightedDensity, weight, mul_assoc, mul_left_comm, mul_comm] using hh

theorem integrable_momentDerivative (p : Real.Parameters) (e : ℕ) {τ : ℝ} (hτ : 0 < τ) :
    IntegrableOn (fun y : ℝ => y^(2*e)*weight p y*densityDerivative p.k τ y) (Ioi 0) := by
  let a := τ/4
  have ha : 0 < a := by dsimp [a]; positivity
  apply ((integrable_moment p e ha).const_mul a⁻¹).mono'
    ((((measurable_id.pow_const _).mul (measurable_weight p)).mul
      (measurable_densityDerivative p.k τ)).aestronglyMeasurable)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  have hc : 0 ≤ y^(2*e)*weight p y :=
    mul_nonneg (pow_nonneg hy.le _) (weight_positive p hy).le
  rw [norm_mul, Real.norm_of_nonneg hc]
  have h := mul_le_mul_of_nonneg_left
    (densityDerivative_bound p.k ha hy (show 2*a ≤ τ by dsimp [a]; linarith)) hc
  simpa only [weightedDensity, mul_assoc, mul_left_comm, mul_comm] using h

theorem moment_hasDerivAt (p : Real.Parameters) (e : ℕ) {τ : ℝ} (hτ : 0 < τ) :
    HasDerivAt (moment p e) (momentDerivative p e τ) τ := by
  let a := τ/4
  have ha : 0 < a := by dsimp [a]; positivity
  have hs : Ioi (2*a) ∈ 𝓝 τ := Ioi_mem_nhds (by dsimp [a]; linarith)
  have hh := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioi (0 : ℝ)))
    (F := fun z y => y^(2*e)*weightedDensity p z y)
    (F' := fun z y => y^(2*e)*weight p y*densityDerivative p.k z y)
    (bound := fun y => a⁻¹*(y^(2*e)*weightedDensity p a y)) hs
    (Filter.Eventually.of_forall (fun z =>
      ((measurable_id.pow_const _).mul (measurable_weightedDensity p z)).aestronglyMeasurable))
    (integrable_moment p e hτ)
    ((((measurable_id.pow_const _).mul (measurable_weight p)).mul
      (measurable_densityDerivative p.k τ)).aestronglyMeasurable)
    ?_ ((integrable_moment p e ha).const_mul a⁻¹) ?_
  · exact hh.2
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    intro z hz
    have hc : 0 ≤ y^(2*e)*weight p y :=
      mul_nonneg (pow_nonneg hy.le _) (weight_positive p hy).le
    rw [norm_mul, Real.norm_of_nonneg hc]
    have h := mul_le_mul_of_nonneg_left
      (densityDerivative_bound p.k ha hy (le_of_lt hz)) hc
    simpa only [weightedDensity, mul_assoc, mul_left_comm, mul_comm] using h
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    intro z hz
    have hzpos : 0 < z := lt_trans (by positivity : 0 < 2*a) hz
    convert (density_hasDerivAt p.k hzpos hy).const_mul (y^(2*e)*weight p y) using 1
    funext v
    simp only [weightedDensity, mul_assoc]


end ManuscriptChain.LaplaceMomentDerivative
