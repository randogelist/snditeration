import Zetahyperbolic.Section3.MomentGrowth
import Zetahyperbolic.Section3.MomentSquareRoot
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! A shifted factorial Stieltjes bound gives genuine exponential integrability
in square-root coordinates. The constant 1/2 is fixed, so no caller-supplied
exponential-integrability premise is hidden in the actual-measure endpoint. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal

namespace ManuscriptChain.ExponentialMoment

private theorem factorial_ratio (A n : ℕ) :
    (Nat.factorial (n + A) : ℝ) / (Nat.factorial n : ℝ) =
      ((n + A).descFactorial A : ℝ) := by
  have h := Nat.factorial_mul_descFactorial (show A ≤ n + A by omega)
  have he : (Nat.factorial n : ℝ) * ((n + A).descFactorial A : ℝ) =
      (Nat.factorial (n + A) : ℝ) := by
    exact_mod_cast (by simpa using h)
  apply (div_eq_iff (by positivity : (Nat.factorial n : ℝ) ≠ 0)).2
  simpa only [mul_comm] using he.symm

/-- Summability of the exact cosh majorant arising from shifted factorial growth. -/
theorem summable_factorial_cosh_majorant (C : ℝ) (A : ℕ) :
    Summable (fun n : ℕ =>
      (1/2 : ℝ)^(2*n) * (C * (Nat.factorial (2*n+A) : ℝ)) /
        (Nat.factorial (2*n) : ℝ)) := by
  have h := summable_descFactorial_mul_geometric_of_norm_lt_one
    (R := ℝ) A (r := (1/2 : ℝ)) (by norm_num)
  have hi : Function.Injective (fun n : ℕ => 2*n) := by
    intro a b hab
    omega
  have hs := (h.comp_injective hi).mul_left C
  convert hs using 1
  ext n
  rw [show (1/2 : ℝ)^(2*n) * (C * (Nat.factorial (2*n+A) : ℝ)) /
      (Nat.factorial (2*n) : ℝ) =
      C * ((Nat.factorial (2*n+A) : ℝ) / (Nat.factorial (2*n) : ℝ)) *
        (1/2 : ℝ)^(2*n) by ring]
  rw [factorial_ratio]
  ring

/-- Any finite positive-half-line measure satisfying the actual shifted
factorial moment bound has an integrable square-root exponential. -/
theorem integrable_exp_sqrt_of_factorial {μ : Measure ℝ} [IsFiniteMeasure μ]
    (hsupport : ∀ᵐ t ∂μ, 0 ≤ t)
    (hint : ∀ n : ℕ, Integrable (fun t : ℝ => t^n) μ)
    {C : ℝ} (hC : 0 < C) (A : ℕ)
    (hbound : ∀ n : ℕ, (∫ t : ℝ, t^n ∂μ) ≤ C * (Nat.factorial (2*n+A) : ℝ)) :
    Integrable (fun t : ℝ => Real.exp ((1/2 : ℝ) * Real.sqrt t)) μ := by
  by_cases hzero : μ = 0
  · simp [hzero]
  let F : ℕ → ℝ → ℝ := fun n t =>
    (1/2 : ℝ)^(2*n) * t^n / (Nat.factorial (2*n) : ℝ)
  have hFint (n : ℕ) : Integrable (F n) μ :=
    ((hint n).const_mul _).div_const _
  have hFnonneg (n : ℕ) : ∀ᵐ t ∂μ, 0 ≤ F n t := by
    filter_upwards [hsupport] with t ht
    dsimp [F]
    positivity
  have hFnorm (n : ℕ) : (∫ t, ‖F n t‖ ∂μ) =
      (1/2 : ℝ)^(2*n) * (∫ t : ℝ, t^n ∂μ) / (Nat.factorial (2*n) : ℝ) := by
    rw [integral_congr_ae (hFnonneg n |>.mono (fun t ht => Real.norm_of_nonneg ht))]
    exact (integral_div _ _).trans (by rw [integral_const_mul])
  have hs : Summable (fun n => ∫ t, ‖F n t‖ ∂μ) := by
    apply Summable.of_nonneg_of_le (fun n => integral_nonneg (fun t => norm_nonneg _))
      _ (summable_factorial_cosh_majorant C A)
    intro n
    rw [hFnorm]
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hbound n) (by positivity)) (by positivity)
  have hseries : (fun t => ∑' n, F n t) =ᵐ[μ]
      (fun t => Real.cosh ((1/2 : ℝ) * Real.sqrt t)) := by
    filter_upwards [hsupport] with t ht
    rw [Real.cosh_eq_tsum]
    apply tsum_congr
    intro n
    dsimp [F]
    rw [mul_pow, pow_mul, Real.sq_sqrt ht]
  have heq := integral_tsum_of_summable_integral_norm hFint hs
  rw [integral_congr_ae hseries] at heq
  have hs' : Summable (fun n => ∫ t, F n t ∂μ) :=
    hs.of_norm_bounded (fun n => norm_integral_le_integral_norm _)
  have hmass : 0 < ∫ t, F 0 t ∂μ := by
    simp only [F, Nat.mul_zero, pow_zero, Nat.factorial_zero, Nat.cast_one,
      one_mul, div_one, integral_const, smul_eq_mul, mul_one]
    exact ENNReal.toReal_pos (by simpa using hzero) (measure_ne_top μ univ)
  have hpositive : 0 < ∫ t, Real.cosh ((1/2 : ℝ) * Real.sqrt t) ∂μ := by
    rw [← heq]
    exact hmass.trans_le (hs'.le_tsum 0 (fun n _ => integral_nonneg_of_ae (hFnonneg n)))
  have hcosh : Integrable (fun t => Real.cosh ((1/2 : ℝ) * Real.sqrt t)) μ :=
    Integrable.of_integral_ne_zero hpositive.ne'
  apply (hcosh.const_mul 2).mono' (by fun_prop)
  filter_upwards with t
  rw [Real.norm_of_nonneg (Real.exp_pos _).le, Real.cosh_eq]
  have h := Real.exp_pos (-((1/2 : ℝ) * Real.sqrt t))
  linarith

end ManuscriptChain.ExponentialMoment

namespace ManuscriptChain.ConcreteMoment

/-- Actual exponential integrability in the square-root coordinate follows
from the proved manuscript moment majorant. -/
theorem actual_exp_sqrt_integrable (p : Real.Parameters) (hp : Real.Admissible p) :
    Integrable (fun t : ℝ => Real.exp ((1/2 : ℝ) * Real.sqrt t)) (momentMeasure p) := by
  obtain ⟨C, hC, A, hb⟩ := actualMomentFactorialMajorant p hp
  apply ExponentialMoment.integrable_exp_sqrt_of_factorial
    (by filter_upwards [momentMeasure_ae_pos p] with t ht; exact ht.le)
    (integrable_moment p) hC A
  intro n
  exact (le_abs_self _).trans (hb n)

end ManuscriptChain.ConcreteMoment
