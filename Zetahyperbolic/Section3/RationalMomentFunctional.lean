import Zetahyperbolic.Section2.RationalFunctionals
import Zetahyperbolic.Section3.RationalIntegralBridge

/-!
# Equation (3.2) on the actual rational-function domain

The moment functional is evaluated on the subspace of actual rational functions
with finitely many simple negative-square poles. Its unique coordinates give
an integrable polynomial-plus-pole expansion. Clearing the common denominator
identifies that expansion with `RatFunc.eval` throughout the nonnegative axis.
-/

noncomputable section
open scoped BigOperators
open Polynomial MeasureTheory Set

namespace ManuscriptChain.Mu

/-- Evaluation of the unique polynomial and finite pole coefficients. -/
def dataEval (d : SimplePole.Data ℕ) (t : ℝ) : ℝ :=
  Real.evalQ d.1 t + ∑ j ∈ d.2.support,
    (d.2 j : ℝ) / (t + ((j + 1 : ℕ) : ℝ) ^ 2)

/-- The canonical real value of an element of the rational-function domain. -/
def realValue (R : RationalDomain) (t : ℝ) : ℝ :=
  dataEval ((SimplePole.coordinates squareNode squareNode_injective).symm R) t

@[simp] theorem realValue_ofData (q : ℚ[X]) (c : ℕ →₀ ℚ) (t : ℝ) :
    realValue (SimplePole.ofData squareNode (q,c)) t = dataEval (q,c) t := by
  unfold realValue
  change dataEval ((SimplePole.coordinates squareNode squareNode_injective).symm
    (SimplePole.coordinates squareNode squareNode_injective (q,c))) t = _
  rw [LinearEquiv.symm_apply_apply]

theorem rationalFunctional_ofData (k : ℕ) (q : ℚ[X]) (c : ℕ →₀ ℚ) :
    rationalFunctional k (SimplePole.ofData squareNode (q,c)) =
      C (Real.polynomialMoment k q) +
        ∑ j ∈ c.support, C (c j) * Tau.muPolePoly k (j+1) := by
  rw [rationalFunctional, SimplePole.functional_ofData]
  simp [SimplePole.generatorFunctional, Finsupp.linearCombination_apply,
    Finsupp.sum, Algebra.smul_def]

theorem integrableOn_dataEval_density (k : ℕ) (q : ℚ[X]) (c : ℕ →₀ ℚ) :
    IntegrableOn (fun y : ℝ => dataEval (q,c) (y ^ 2) * Hyperbolic.density k y)
      (Ioi 0) := by
  simp only [dataEval, add_mul, Finset.sum_mul]
  apply (Hyperbolic.integrableOn_polynomial_density k q).add
  apply integrable_finsetSum
  intro j hj
  have h := (Hyperbolic.integrableOn_pole_density k (j+1) (by omega)).const_mul (c j : ℝ)
  simpa only [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using h

theorem integral_dataEval_density (k : ℕ) (hk : 0 < k) (q : ℚ[X]) (c : ℕ →₀ ℚ) :
    (∫ y : ℝ in Ioi 0, dataEval (q,c) (y ^ 2) * Hyperbolic.density k y) =
      Real.evalQ (rationalFunctional k (SimplePole.ofData squareNode (q,c)))
        (Real.zeta (2*k+1)) := by
  have hsplit (y : ℝ) : dataEval (q,c) (y ^ 2) * Hyperbolic.density k y =
      Real.evalQ q (y ^ 2) * Hyperbolic.density k y +
        ∑ j ∈ c.support, (c j : ℝ) *
          (Hyperbolic.density k y / (y ^ 2 + ((j+1 : ℕ) : ℝ)^2)) := by
    simp only [dataEval, add_mul, Finset.sum_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hi (j : ℕ) (hj : j ∈ c.support) :
      IntegrableOn (fun y : ℝ => (c j : ℝ) *
        (Hyperbolic.density k y / (y ^ 2 + ((j+1 : ℕ) : ℝ)^2))) (Ioi 0) :=
    (Hyperbolic.integrableOn_pole_density k (j+1) (by omega)).const_mul _
  simp_rw [hsplit]
  rw [integral_add (Hyperbolic.integrableOn_polynomial_density k q)
    (integrable_finsetSum _ hi), Hyperbolic.integral_polynomial_density,
    integral_finsetSum _ hi, rationalFunctional_ofData]
  simp only [integral_const_mul]
  simp_rw [Hyperbolic.poleIntegralIdentity k hk _ (Nat.succ_pos _)]
  simp only [Real.evalQ, Real.realPolynomial, Polynomial.map_add,
    Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_C,
    Polynomial.eval_add, Polynomial.eval_finsetSum, Polynomial.eval_mul,
    Polynomial.eval_C]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [Tau.muPolePoly_eq_existing]
  simp [Polynomial.map_add, Polynomial.map_mul, add_comm]

/-- A rational fraction evaluates as written whenever its displayed
common denominator is nonzero. -/
theorem ratFunc_eval_eq_fraction (r : RatFunc ℚ) (q D : ℚ[X]) (t : ℝ)
    (hD : D.eval₂ (algebraMap ℚ ℝ) t ≠ 0)
    (hr : r = algebraMap ℚ[X] (RatFunc ℚ) q / algebraMap ℚ[X] (RatFunc ℚ) D) :
    RatFunc.eval (algebraMap ℚ ℝ) t r =
      q.eval₂ (algebraMap ℚ ℝ) t / D.eval₂ (algebraMap ℚ ℝ) t := by
  have hD0 : D ≠ 0 := by intro hz; simp [hz] at hD
  have hdiv : r.denom ∣ D := (RatFunc.denom_dvd hD0).mpr ⟨q,hr⟩
  have hd : r.denom.eval₂ (algebraMap ℚ ℝ) t ≠ 0 := by
    intro hz
    exact hD (Polynomial.eval₂_eq_zero_of_dvd_of_eval₂_eq_zero _ _ hdiv hz)
  have hpoly := (RatFunc.num_mul_eq_mul_denom_iff hD0).mpr hr
  have he := congrArg (Polynomial.eval₂ (algebraMap ℚ ℝ) t) hpoly
  simp only [Polynomial.eval₂_mul] at he
  exact (div_eq_div_iff hd hD).mpr he

/-- On the nonnegative axis no pole denominator vanishes, so canonical
coordinates agree with evaluation of the actual rational function. -/
theorem dataEval_eq_ratFunc_eval (q : ℚ[X]) (c : ℕ →₀ ℚ) {t : ℝ} (ht : 0 ≤ t) :
    dataEval (q,c) t =
      RatFunc.eval (algebraMap ℚ ℝ) t (SimplePole.realize squareNode (q,c)) := by
  let D : ℚ[X] := ∏ j ∈ c.support, (X - C (squareNode j))
  let P : ℚ[X] := q * D + ∑ j ∈ c.support,
    C (c j) * ∏ l ∈ c.support.erase j, (X - C (squareNode l))
  have hfactor (j : ℕ) : 0 < t + ((j+1 : ℕ) : ℝ)^2 := by positivity
  have hDeval : D.eval₂ (algebraMap ℚ ℝ) t =
      ∏ j ∈ c.support, (t + ((j+1 : ℕ) : ℝ)^2) := by
    simp [D, squareNode, Polynomial.eval₂_finsetProd]
  have hD : D.eval₂ (algebraMap ℚ ℝ) t ≠ 0 := by
    rw [hDeval]
    exact ne_of_gt (Finset.prod_pos (fun j hj => hfactor j))
  have hD0 : D ≠ 0 := by intro hz; simp [hz] at hD
  have hr : SimplePole.realize squareNode (q,c) =
      algebraMap ℚ[X] (RatFunc ℚ) P / algebraMap ℚ[X] (RatFunc ℚ) D := by
    apply (eq_div_iff (RatFunc.algebraMap_ne_zero hD0)).mpr
    exact SimplePole.realize_mul_denominator squareNode q c
  rw [ratFunc_eval_eq_fraction _ P D t hD hr]
  apply (eq_div_iff hD).mpr
  simp only [P, Polynomial.eval₂_add, Polynomial.eval₂_mul,
    Polynomial.eval₂_finsetSum, Polynomial.eval₂_C, dataEval,
    Hyperbolic.evalQ_eq_eval₂, add_mul, Finset.sum_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  have hprod : D.eval₂ (algebraMap ℚ ℝ) t =
      (t + ((j+1 : ℕ) : ℝ)^2) *
        ∏ l ∈ c.support.erase j, (t + ((l+1 : ℕ) : ℝ)^2) := by
    rw [hDeval]
    exact (Finset.mul_prod_erase c.support _ hj).symm
  rw [hprod]
  simp only [Polynomial.eval₂_finsetProd, Polynomial.eval₂_sub, Polynomial.eval₂_add,
    Polynomial.eval₂_pow, Polynomial.eval₂_natCast,
    Polynomial.eval₂_X, Polynomial.eval₂_C, squareNode, map_neg, map_pow,
    map_natCast, sub_neg_eq_add]
  field_simp [ne_of_gt (hfactor j)]
  simp

/-- Exact agreement with `RatFunc.eval`, including at the origin. -/
theorem realValue_eq_ratFunc_eval (R : RationalDomain) {t : ℝ} (ht : 0 ≤ t) :
    realValue R t = RatFunc.eval (algebraMap ℚ ℝ) t (R : RatFunc ℚ) := by
  let d := (SimplePole.coordinates squareNode squareNode_injective).symm R
  have hR : SimplePole.ofData squareNode d = R :=
    (SimplePole.coordinates squareNode squareNode_injective).apply_symm_apply R
  rw [← hR]
  exact (realValue_ofData d.1 d.2 t).trans (dataEval_eq_ratFunc_eval d.1 d.2 ht)

/-- Every rational function in the specified domain is integrable
against the hyperbolic density; this is proved independently of its integral. -/
theorem integrableOn_rational_density (k : ℕ) (R : RationalDomain) :
    IntegrableOn (fun y : ℝ =>
      RatFunc.eval (algebraMap ℚ ℝ) (y^2) (R : RatFunc ℚ) * Hyperbolic.density k y)
      (Ioi 0) := by
  let d := (SimplePole.coordinates squareNode squareNode_injective).symm R
  have h := integrableOn_dataEval_density k d.1 d.2
  apply h.congr
  filter_upwards [] with y
  exact congrArg (fun x => x * Hyperbolic.density k y)
    (realValue_eq_ratFunc_eval R (sq_nonneg y))

/-- Equation (3.2) for the full actual rational-function domain. -/
theorem integral_rational_density (k : ℕ) (hk : 0 < k) (R : RationalDomain) :
    (∫ y : ℝ in Ioi 0,
      RatFunc.eval (algebraMap ℚ ℝ) (y^2) (R : RatFunc ℚ) * Hyperbolic.density k y) =
      Real.evalQ (rationalFunctional k R) (Real.zeta (2*k+1)) := by
  let d := (SimplePole.coordinates squareNode squareNode_injective).symm R
  have hR : SimplePole.ofData squareNode d = R :=
    (SimplePole.coordinates squareNode squareNode_injective).apply_symm_apply R
  rw [← hR, ← integral_dataEval_density k hk d.1 d.2]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro y hy
  exact congrArg (fun x => x * Hyperbolic.density k y)
    (dataEval_eq_ratFunc_eval d.1 d.2 (sq_nonneg y)).symm

end ManuscriptChain.Mu
