import Mathlib.Analysis.Real.Pi.Leibniz
import Mathlib.Analysis.Real.Pi.Irrational
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

/-!
# The actual beta-one measure and its complete moment sequence

At k=0, the manuscript's beta series is conditionally convergent and must
be interpreted by ordered partial sums, not a real `tsum`. This module
identifies that ordered limit with the actual positive density 1/(1+x²),
and proves every even and odd moment. The odd formula uses eta(1)=log 2,
the removable value, rather than substituting s=1 into (1-2^(1-s))*zeta(s).
It does not claim the all-k or effective-transcendence assertions of 6.15.
-/

noncomputable section
open MeasureTheory Set Filter intervalIntegral
open scoped BigOperators Topology

namespace ManuscriptChain.BetaOneMoments

/-- Ordered beta-one partial sum; order is part of this definition. -/
def betaPartialSum (r : ℕ) : ℝ :=
  ∑ n ∈ Finset.range r, (-1 : ℝ)^n / (2 * (n : ℝ) + 1)

/-- Ordered eta-one partial sum, with its index starting at one. -/
def etaPartialSum (r : ℕ) : ℝ :=
  ∑ n ∈ Finset.range r, (-1 : ℝ)^n / ((n : ℝ) + 1)

/-- All moments of the literal k=0 density, with no unspecified measure. -/
def moment (m : ℕ) : ℝ := ∫ x : ℝ in (0:ℝ)..1, x^m / (1+x^2)

theorem integrand_continuous (m : ℕ) :
    Continuous (fun x : ℝ => x^m / (1+x^2)) := by
  apply Continuous.div (by fun_prop) (by fun_prop)
  intro x
  positivity

theorem moment_eq_open_integral (m : ℕ) :
    moment m = ∫ x : ℝ in Ioo 0 1, x^m / (1+x^2) := by
  rw [moment, intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1),
    integral_Ioc_eq_integral_Ioo]

theorem moment_zero : moment 0 = Real.pi / 4 := by
  simp only [moment, pow_zero]
  rw [integral_one_div_one_add_sq]
  simp [Real.arctan_one]

theorem beta_ordered_limit :
    Tendsto betaPartialSum atTop (𝓝 (moment 0)) := by
  rw [moment_zero]
  exact Real.tendsto_sum_pi_div_four

theorem beta_one_irrational : Irrational (moment 0) := by
  rw [moment_zero]
  simpa using Irrational.div_natCast Real.irrational_pi (n := 4) (by norm_num)

theorem moment_one : moment 1 = Real.log 2 / 2 := by
  have hd (x : ℝ) : HasDerivAt (fun y : ℝ => Real.log (1+y^2) / 2)
      (x / (1+x^2)) x := by
    have hd0 : HasDerivAt (fun y : ℝ => 1+y^2) (2*x) x := by
      simpa only [Pi.pow_apply, id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one,
        mul_one] using ((hasDerivAt_id x).pow 2).const_add 1
    convert (hd0.log (by positivity : (1:ℝ)+x^2 ≠ 0)).div_const 2 using 1 <;> ring
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0:ℝ)) (b := (1:ℝ)) (fun x _ => hd x)
    (by simpa only [pow_one] using (integrand_continuous 1).intervalIntegrable 0 1)
  norm_num [moment] at hi ⊢
  exact hi

/-- The integral recurrence proves all-order moments without interchanging
an alternating series at its endpoint. -/
theorem moment_add_two (m : ℕ) :
    moment (m+2) = 1 / ((m:ℝ)+1) - moment m := by
  have he (x : ℝ) : x^(m+2)/(1+x^2) = x^m - x^m/(1+x^2) := by
    have hp : (1:ℝ)+x^2 ≠ 0 := by positivity
    rw [pow_add]
    field_simp [hp]
    ring
  unfold moment
  simp_rw [he]
  have hp : IntervalIntegrable (fun x : ℝ => x^m) volume 0 1 :=
    (show Continuous (fun x : ℝ => x^m) by fun_prop).intervalIntegrable 0 1
  rw [intervalIntegral.integral_sub hp
    ((integrand_continuous m).intervalIntegrable 0 1), integral_pow]
  simp

/-- Literal even-moment formula of 6.15(2), with k=0 and every r. -/
theorem even_moment (r : ℕ) :
    moment (2*r) = (-1:ℝ)^r * (Real.pi/4 - betaPartialSum r) := by
  induction r with
  | zero => simpa [betaPartialSum] using moment_zero
  | succ r ih =>
    rw [show 2*(r+1) = 2*r+2 by omega, moment_add_two, ih]
    simp only [betaPartialSum, Finset.sum_range_succ, pow_succ, Nat.cast_mul,
      Nat.cast_ofNat]
    have hs : (-1:ℝ)^r * (-1:ℝ)^r = 1 := by
      rw [← mul_pow]
      norm_num
    have hr : (2:ℝ)*(r:ℝ)+1 ≠ 0 := by positivity
    field_simp [hr]
    nlinarith [hs]

/-- Literal odd-moment formula at k=0, with the corrected removable eta value. -/
theorem odd_moment (r : ℕ) :
    moment (2*r+1) = ((-1:ℝ)^r / 2) * (Real.log 2 - etaPartialSum r) := by
  induction r with
  | zero => simpa [etaPartialSum, div_eq_mul_inv, mul_comm] using moment_one
  | succ r ih =>
    rw [show 2*(r+1)+1 = (2*r+1)+2 by omega, moment_add_two, ih]
    simp only [etaPartialSum, Finset.sum_range_succ, pow_succ, Nat.cast_add,
      Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
    have hs : (-1:ℝ)^r * (-1:ℝ)^r = 1 := by
      rw [← mul_pow]
      norm_num
    have hr : (r:ℝ)+1 ≠ 0 := by positivity
    rw [show (2:ℝ)*(r:ℝ)+1+1 = 2*((r:ℝ)+1) by ring]
    field_simp [hr]
    nlinarith [hs]

theorem moment_pos (m : ℕ) : 0 < moment m := by
  apply intervalIntegral.integral_pos (by norm_num : (0:ℝ)<1)
    (integrand_continuous m).continuousOn
  · intro x hx
    exact div_nonneg (pow_nonneg hx.1.le _) (by positivity)
  · refine ⟨1, by norm_num, ?_⟩
    norm_num


/-- A quantitative tail bound for every moment of the actual beta-one density. -/
theorem moment_le (m : ℕ) : moment m ≤ 1 / ((m:ℝ)+1) := by
  have hp : IntervalIntegrable (fun x : ℝ => x^m) volume 0 1 :=
    (show Continuous (fun x : ℝ => x^m) by fun_prop).intervalIntegrable 0 1
  have hi : IntervalIntegrable (fun x : ℝ => x^m / (1+x^2)) volume 0 1 :=
    (integrand_continuous m).intervalIntegrable 0 1
  have h := intervalIntegral.integral_mono_on (by norm_num : (0:ℝ) ≤ 1) hi hp
    (show ∀ x ∈ Icc (0:ℝ) 1, x^m / (1+x^2) ≤ x^m from fun x hx => by
      apply (div_le_iff₀ (by positivity : (0:ℝ)<1+x^2)).2
      nlinarith [mul_nonneg (pow_nonneg hx.1 m) (sq_nonneg x)])
  simpa [moment, integral_pow] using h

/-- The normalized moment sequence really tends to zero. -/
theorem moment_tendsto_zero : Tendsto moment atTop (𝓝 0) :=
  squeeze_zero (fun m => (moment_pos m).le) moment_le
    tendsto_one_div_add_atTop_nhds_zero_nat

/-- Eta-one is the ordered alternating harmonic limit log 2. -/
theorem eta_ordered_limit : Tendsto etaPartialSum atTop (𝓝 (Real.log 2)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.2
  have hg : Tendsto (fun r : ℕ => 2*r+1) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    exact ⟨b, fun n hn => by omega⟩
  have hlim := (moment_tendsto_zero.comp hg).const_mul 2
  have he (r : ℕ) : ‖etaPartialSum r - Real.log 2‖ = 2 * moment (2*r+1) := by
    have h := congrArg abs (odd_moment r)
    have hs : |(-1:ℝ)^r / 2| = 1/2 := by simp
    rw [abs_of_pos (moment_pos _), abs_mul, hs] at h
    rw [Real.norm_eq_abs, abs_sub_comm]
    linarith
  simpa only [Function.comp_apply, mul_zero, ← he] using hlim

end ManuscriptChain.BetaOneMoments
