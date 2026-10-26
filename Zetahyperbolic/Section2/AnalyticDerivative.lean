import Zetahyperbolic.Section2.RationalDifference
import Zetahyperbolic.Section2.RationalRegularity
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Tactic

/-!
# Lemma 2.3 — normalized analytic derivative on finite rational pole coordinates

No derivative identity is assumed. The analytic derivative is computed
using actual calculus, the pole at zero is excluded by regularity, and the
algebraic finite-difference theorem from Section2/RationalDifference.lean
supplies the matching rational functional value.

The polynomial component and transport to a general RatFunc evaluation
are treated separately: a zero-pole residue must not be assigned an
ordinary derivative at its pole.
-/

noncomputable section
open scoped BigOperators
open Polynomial

namespace ManuscriptChain.Tau

/-- The actual real analytic function of a finitely-supported pole expansion. -/
def poleSpan (c : ℤ →₀ ℚ) (x : ℝ) : ℝ :=
  ∑ r ∈ c.support, (c r : ℝ) * (x - (r : ℝ))⁻¹

/-- The corresponding element of the actual rational-function domain. -/
def poleElement (c : ℤ →₀ ℚ) : RationalDomain :=
  SimplePole.ofData integerNode (0,c)

/-- The even normalized derivative of a shifted reciprocal pole. -/
theorem reciprocal_even_derivative (k : ℕ) (r : ℝ) :
    iteratedDeriv (2*k) (fun x : ℝ => (x-r)⁻¹) 0 /
      ((2*k).factorial : ℝ) = -(r^(2*k+1))⁻¹ := by
  rw [iteratedDeriv_eq_iterate]
  have h := congrFun (iter_deriv_inv_linear_sub (2*k) (1 : ℝ) r) 0
  simp only [one_mul, mul_zero, zero_sub, one_pow, mul_one] at h
  have he : (-1 - ((2*k : ℕ) : ℤ)) = -((2*k+1 : ℕ) : ℤ) := by omega
  have hs : (-1 : ℝ)^(2*k) = 1 := by simp [pow_mul]
  rw [hs, one_mul, he, zpow_neg, zpow_natCast] at h
  have hn : (-r)^(2*k+1) = -(r^(2*k+1)) := by
    simp [pow_succ, pow_mul]
  rw [hn, inv_neg] at h
  rw [h]
  have hf : ((2*k).factorial : ℝ) ≠ 0 := by positivity
  field_simp [hf] <;> ring

/-- No pole in the finite expansion occurs at the derivative evaluation point. -/
theorem poleSpan_normalized_derivative (k : ℕ) (c : ℤ →₀ ℚ)
    (hzero : c 0 = 0) :
    iteratedDeriv (2*k) (poleSpan c) 0 / ((2*k).factorial : ℝ) =
      ∑ r ∈ c.support, (c r : ℝ) * (-(r : ℝ)^(2*k+1))⁻¹ := by
  have hreg (r : ℤ) (hr : r ∈ c.support) :
      ContDiffAt ℝ (2*k : ℕ)
        (fun x : ℝ => (c r : ℝ) * (x - (r : ℝ))⁻¹) 0 := by
    have hr0 : r ≠ 0 := by
      intro hz
      subst r
      exact (Finsupp.mem_support_iff.mp hr) hzero
    have hreal : (0 : ℝ) - (r : ℝ) ≠ 0 := by
      have hcast : (r : ℝ) ≠ 0 := by exact_mod_cast hr0
      simpa using neg_ne_zero.mpr hcast
    exact contDiffAt_const.mul
      ((contDiffAt_id.sub contDiffAt_const).inv hreal)
  unfold poleSpan
  rw [iteratedDeriv_fun_sum hreg, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro r hr
  rw [iteratedDeriv_const_mul_field, mul_div_assoc,
    reciprocal_even_derivative]
  ring

theorem poleElement_coefficient (k : ℕ) (c : ℤ →₀ ℚ) :
    (partialFractionCoefficient (2*k) (poleElement c) : ℝ) =
      ∑ r ∈ c.support, (c r : ℝ) * (-(r : ℝ)^(2*k+1))⁻¹ := by
  rw [poleElement, partialFractionCoefficient_ofData,
    dataCoefficient_apply]
  simp only [coeff_zero, zero_sub]
  push_cast
  simp only [Finset.sum_neg_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro r hr
  ring

/-- The normalized genuine analytic derivative equals the coefficient
in the unique coordinates of the actual rational-function domain. -/
theorem poleElement_coefficient_eq_analytic (k : ℕ) (c : ℤ →₀ ℚ)
    (hzero : c 0 = 0) :
    (partialFractionCoefficient (2*k) (poleElement c) : ℝ) =
      iteratedDeriv (2*k) (poleSpan c) 0 / ((2*k).factorial : ℝ) := by
  rw [poleSpan_normalized_derivative k c hzero]
  exact poleElement_coefficient k c

/-- The actual finite-difference tau value equals the normalized analytic
derivative on every finite nonzero-pole span. -/
theorem rationalFunctional_difference_analytic_poles
    (k : ℕ) (hk : 1 ≤ k) (c : ℤ →₀ ℚ) (hzero : c 0 = 0)
    (x : ℝ) :
    (((rationalFunctional k (rationalDifference (poleElement c))).map
        (algebraMap ℚ ℝ)).eval x) =
      iteratedDeriv (2*k) (poleSpan c) 0 / ((2*k).factorial : ℝ) := by
  rw [rationalFunctional_difference k hk]
  simp only [Polynomial.map_C, Polynomial.eval_C]
  exact poleElement_coefficient_eq_analytic k c hzero

end ManuscriptChain.Tau
