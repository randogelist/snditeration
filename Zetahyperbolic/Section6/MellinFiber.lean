import Zetahyperbolic.Section5.BeukersPolynomialIntegral
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Literal multiplicative fibers of the Beukers measure

The inner fiber integral is evaluated for every finite rational polynomial.
The exponentials below are only the proof of the literal real-power integral;
no abstract moment or unspecified change-of-variables premise is introduced.
-/
noncomputable section
open MeasureTheory Set
open scoped BigOperators

namespace ManuscriptChain.Beukers.Mellin

def fiberMonomial (r t : ℕ) (u : ℝ) : ℝ :=
  if r = t then u^r else (u^r-u^t) / (((r : ℝ)-(t : ℝ))*Real.log u)

def mellinWeight (u : ℝ) : ℝ := (-Real.log u)^6 / (720*(1-u))

def fiber {K : ℕ} (c d : Fin (K+1) → ℚ) (u : ℝ) : ℝ :=
  ∫ y : ℝ in Ioo 0 1,
    coefficientPolynomialValue c (u^y) * coefficientPolynomialValue d (u^(1-y))

lemma monomial_eq_exp (r t : ℕ) {u : ℝ} (hu : 0 < u) (y : ℝ) :
    (u^y)^r * (u^(1-y))^t =
      Real.exp ((((r : ℝ)-(t : ℝ))*Real.log u)*y + (t : ℝ)*Real.log u) := by
  rw [Real.rpow_def_of_pos hu, Real.rpow_def_of_pos hu,
    ← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add]
  congr 1
  ring

lemma monomial_fiber_integrable (r t : ℕ) {u : ℝ} (hu : 0 < u) :
    IntegrableOn (fun y : ℝ => (u^y)^r * (u^(1-y))^t) (Ioo 0 1) := by
  simp_rw [monomial_eq_exp r t hu]
  exact (show Continuous (fun y : ℝ =>
    Real.exp ((((r : ℝ)-(t : ℝ))*Real.log u)*y + (t : ℝ)*Real.log u)) by
      fun_prop).integrableOn_Icc.mono_set Ioo_subset_Icc_self

lemma integral_exp_affine {c : ℝ} (hc : c ≠ 0) (d : ℝ) :
    (∫ y : ℝ in Ioo 0 1, Real.exp (c*y+d)) =
      (Real.exp (c+d) - Real.exp d) / c := by
  have hd (y : ℝ) : HasDerivAt (fun z : ℝ => Real.exp (c*z+d)/c)
      (Real.exp (c*y+d)) y := by
    have h := ((((hasDerivAt_id y).const_mul c).add_const d).exp).div_const c
    simpa only [mul_one, mul_div_cancel_right₀ _ hc] using h
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0 : ℝ)) (b := 1) (fun y _ => hd y)
    ((show Continuous (fun y : ℝ => Real.exp (c*y+d)) by fun_prop).intervalIntegrable 0 1)
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    integral_Ioc_eq_integral_Ioo] at hi
  simpa only [mul_one, mul_zero, zero_add, sub_div] using hi

/-- The exact diagonal and off-diagonal fiber integrals from 6.1(1). -/
theorem monomial_fiber_integral (r t : ℕ) {u : ℝ} (hu : u ∈ Ioo 0 1) :
    (∫ y : ℝ in Ioo 0 1, (u^y)^r * (u^(1-y))^t) = fiberMonomial r t u := by
  simp_rw [monomial_eq_exp r t hu.1]
  by_cases hrt : r = t
  · subst t
    simp [fiberMonomial, Real.exp_nat_mul, Real.exp_log hu.1]
  · have hr : (r : ℝ) - (t : ℝ) ≠ 0 := by
      apply sub_ne_zero.mpr
      exact_mod_cast hrt
    have hl : Real.log u ≠ 0 := ne_of_lt (Real.log_neg hu.1 hu.2)
    rw [integral_exp_affine (mul_ne_zero hr hl), fiberMonomial, if_neg hrt]
    rw [show ((r : ℝ)-(t : ℝ))*Real.log u + (t : ℝ)*Real.log u =
      (r : ℝ)*Real.log u by ring]
    simp only [Real.exp_nat_mul, Real.exp_log hu.1]

lemma polynomial_fiber_expansion {K : ℕ} (c d : Fin (K+1) → ℚ) (u y : ℝ) :
    coefficientPolynomialValue c (u^y) * coefficientPolynomialValue d (u^(1-y)) =
      ∑ r : Fin (K+1), ∑ t : Fin (K+1),
        ((c r : ℝ)*(d t : ℝ))*((u^y)^r.val * (u^(1-y))^t.val) := by
  unfold coefficientPolynomialValue
  rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro t _
  ring

/-- Literal inner fiber integral equals the complete finite divided-difference sum. -/
theorem fiber_eq_sum {K : ℕ} (c d : Fin (K+1) → ℚ) {u : ℝ}
    (hu : u ∈ Ioo 0 1) :
    fiber c d u = ∑ r : Fin (K+1), ∑ t : Fin (K+1),
      (c r : ℝ)*(d t : ℝ)*fiberMonomial r.val t.val u := by
  unfold fiber
  simp_rw [polynomial_fiber_expansion]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro r _
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro t _
      rw [integral_const_mul, monomial_fiber_integral r.val t.val hu]
    · intro t _
      exact (monomial_fiber_integrable r.val t.val hu.1).const_mul _
  · intro r _
    apply integrable_finsetSum
    intro t _
    exact (monomial_fiber_integrable r.val t.val hu.1).const_mul _

end ManuscriptChain.Beukers.Mellin
