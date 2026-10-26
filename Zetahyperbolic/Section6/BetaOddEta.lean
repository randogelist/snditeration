import Zetahyperbolic.Section6.BetaOddMoments
import Zetahyperbolic.Section6.BetaOneMoments

/-!
# All odd moments and the ordered eta calibration

The eta value here is calibrated to the actual ordered alternating series.
At k=0 it is log 2, so no multiplication of a zero factor and zeta's pole
is used. Identification with (1-2^(1-s))*zeta(s) for s>1 is separate.
-/
noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace ManuscriptChain.BetaOddEta
open BetaOddMoments

/-- The actual alternating eta value, subsequently identified by its ordered limit. -/
def etaValue (k : ℕ) : ℝ := (2:ℝ)^(2*k+1) * moment k 1

/-- Literal odd-moment formula for all k,r, with eta interpreted by ordered convergence. -/
theorem odd_moment (k r : ℕ) :
    moment k (2*r+1) = ((-1:ℝ)^r / (2:ℝ)^(2*k+1)) *
      (etaValue k - etaPartialSum k r) := by
  have hp : (2:ℝ)^(2*k+1) ≠ 0 := by positivity
  induction r with
  | zero =>
    simp only [Nat.mul_zero, Nat.zero_add, pow_zero, etaPartialSum,
      Finset.range_zero, Finset.sum_empty, sub_zero, etaValue]
    field_simp
  | succ r ih =>
    rw [show 2*(r+1)+1 = (2*r+1)+2 by omega, moment_add_two, ih]
    simp only [etaPartialSum, Finset.sum_range_succ, Nat.cast_add,
      Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
    rw [show (2:ℝ)*(r:ℝ)+1+1 = 2*((r:ℝ)+1) by ring, mul_pow,
      pow_succ (-1:ℝ) r]
    have hs : (-1:ℝ)^r * (-1:ℝ)^r = 1 := by
      rw [← mul_pow]
      norm_num
    have hr : (r:ℝ)+1 ≠ 0 := by positivity
    field_simp [hr, hp]
    nlinarith [hs]

/-- The odd center is the actual ordered alternating eta sum, for every k. -/
theorem eta_ordered_limit (k : ℕ) :
    Tendsto (etaPartialSum k) atTop (𝓝 (etaValue k)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.2
  have hg : Tendsto (fun r : ℕ => 2*r+1) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    exact eventually_atTop.2 ⟨b, fun n hn => by omega⟩
  have hlim := ((moment_tendsto_zero k).comp hg).const_mul ((2:ℝ)^(2*k+1))
  have he (r : ℕ) : ‖etaPartialSum k r - etaValue k‖ =
      (2:ℝ)^(2*k+1) * moment k (2*r+1) := by
    have h := congrArg abs (odd_moment k r)
    have hs : |(-1:ℝ)^r / (2:ℝ)^(2*k+1)| = 1 / (2:ℝ)^(2*k+1) := by
      norm_num [abs_div, abs_pow]
    rw [abs_of_pos (moment_pos _ _), abs_mul, hs, one_div, inv_mul_eq_div] at h
    have hp : (2:ℝ)^(2*k+1) ≠ 0 := by positivity
    have ht := (eq_div_iff hp).mp h
    rw [Real.norm_eq_abs, abs_sub_comm]
    simpa only [mul_comm] using ht.symm
  simpa only [Function.comp_apply, mul_zero, ← he] using hlim

/-- The k=0 endpoint is the removable eta value log 2. -/
theorem etaValue_zero : etaValue 0 = Real.log 2 := by
  apply tendsto_nhds_unique (eta_ordered_limit 0)
  simpa only [etaPartialSum, BetaOneMoments.etaPartialSum, Nat.mul_zero,
    Nat.zero_add, pow_one] using BetaOneMoments.eta_ordered_limit

end ManuscriptChain.BetaOddEta
