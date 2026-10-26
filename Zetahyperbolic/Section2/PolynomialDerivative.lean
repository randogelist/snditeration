import Zetahyperbolic.Section2.AnalyticDerivative
import Mathlib.Analysis.Calculus.ContDiff.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-!
# The polynomial and general coordinate components of Lemma 2.3

The derivative is calculated over the actual unique polynomial-plus-simple-pole
coordinates. An origin pole must have zero residue. The separate last transport
to the rational-function eval operation is still a later compatibility proof.
-/

noncomputable section
open scoped BigOperators
open Polynomial

namespace ManuscriptChain.Tau

def polynomialReal (q : ℚ[X]) (x : ℝ) : ℝ := aeval x q

/-- The analytical higher derivative of a polynomial is its iterated algebraic derivative. -/
theorem polynomialReal_iteratedDeriv (q : ℚ[X]) (n : ℕ) :
    iteratedDeriv n (polynomialReal q) =
      (fun x : ℝ => aeval x (Polynomial.derivative^[n] q)) := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      rw [iteratedDeriv_succ, ih]
      funext x
      rw [Polynomial.deriv_aeval]
      simp only [Function.iterate_succ_apply']

theorem polynomialReal_normalized_derivative (q : ℚ[X]) (n : ℕ) :
    iteratedDeriv n (polynomialReal q) 0 / (n.factorial : ℝ) =
      (q.coeff n : ℝ) := by
  rw [polynomialReal_iteratedDeriv]
  change aeval (0 : ℝ) (Polynomial.derivative^[n] q) / (n.factorial : ℝ) = _
  rw [← Polynomial.coeff_zero_eq_aeval_zero']
  rw [Polynomial.coeff_iterate_derivative]
  simp only [zero_add, Nat.descFactorial_self, nsmul_eq_mul]
  push_cast
  have hn : (n.factorial : ℝ) ≠ 0 := by positivity
  field_simp [hn] <;> rfl

/-- Actual real function of polynomial and pole coefficients. -/
def coordinateReal (q : ℚ[X]) (c : ℤ →₀ ℚ) (x : ℝ) : ℝ :=
  polynomialReal q x + poleSpan c x

theorem coordinateReal_even_derivative
    (k : ℕ) (q : ℚ[X]) (c : ℤ →₀ ℚ) (hc : c 0 = 0) :
    iteratedDeriv (2*k) (coordinateReal q c) 0 /
        ((2*k).factorial : ℝ) =
      (q.coeff (2*k) : ℝ) +
        ∑ r ∈ c.support, (c r : ℝ) * (-(r : ℝ)^(2*k+1))⁻¹ := by
  have hpoly : ContDiffAt ℝ (2*k : ℕ) (polynomialReal q) 0 := by
    exact (Polynomial.contDiff_aeval (𝕜 := ℝ) q (2*k : WithTop ℕ∞)).contDiffAt
  have hreg (r : ℤ) (hr : r ∈ c.support) :
      ContDiffAt ℝ (2*k : ℕ)
        (fun x : ℝ => (c r : ℝ) * (x - (r : ℝ))⁻¹) 0 := by
    have hr0 : r ≠ 0 := by
      intro hz
      subst r
      exact (Finsupp.mem_support_iff.mp hr) hc
    have hreal : (0 : ℝ) - (r : ℝ) ≠ 0 := by
      have hcast : (r : ℝ) ≠ 0 := by exact_mod_cast hr0
      simpa using neg_ne_zero.mpr hcast
    exact contDiffAt_const.mul
      ((contDiffAt_id.sub contDiffAt_const).inv hreal)
  have hpole : ContDiffAt ℝ (2*k : ℕ) (poleSpan c) 0 := by
    unfold poleSpan
    exact ContDiffAt.sum hreg
  unfold coordinateReal
  rw [iteratedDeriv_fun_add hpoly hpole, add_div,
    polynomialReal_normalized_derivative, poleSpan_normalized_derivative k c hc]

/-- The unique intrinsic partial-fraction coordinate equals the analytical
coefficient of the entire regular polynomial-plus-pole real realization. -/
theorem rationalDomain_coefficient_eq_coordinate_derivative
    (k : ℕ) (q : ℚ[X]) (c : ℤ →₀ ℚ) (hc : c 0 = 0) :
    (partialFractionCoefficient (2*k)
        (SimplePole.ofData integerNode (q,c)) : ℝ) =
      iteratedDeriv (2*k) (coordinateReal q c) 0 /
        ((2*k).factorial : ℝ) := by
  rw [partialFractionCoefficient_ofData, dataCoefficient_apply,
    coordinateReal_even_derivative k q c hc]
  push_cast
  simp only [inv_neg, mul_neg, Finset.sum_neg_distrib, sub_eq_add_neg]

theorem rationalFunctional_difference_analytic_coordinates
    (k : ℕ) (hk : 1 ≤ k) (q : ℚ[X]) (c : ℤ →₀ ℚ) (hc : c 0 = 0)
    (x : ℝ) :
    (((rationalFunctional k
      (rationalDifference (SimplePole.ofData integerNode (q,c)))).map
      (algebraMap ℚ ℝ)).eval x) =
      iteratedDeriv (2*k) (coordinateReal q c) 0 /
        ((2*k).factorial : ℝ) := by
  rw [rationalFunctional_difference k hk]
  simp only [Polynomial.map_C, Polynomial.eval_C]
  exact rationalDomain_coefficient_eq_coordinate_derivative k q c hc

end ManuscriptChain.Tau
