import Zetahyperbolic.Section5.UnitLogMoments
import Mathlib.Tactic

/-!
# Actual positive beta-odd density, all orders, and ordered series calibration

The alternating beta series is interpreted by ordered partial sums, including
its conditionally convergent k=0 endpoint. Finite integral recurrences and
quantitative remainders prove calibration without exchanging a conditionally
convergent endpoint series and an integral. No Euler-value, arithmetic-rate,
or Padé asymptotic hypothesis is introduced.
-/
noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace ManuscriptChain.BetaOddMoments

abbrev unitMeasure : Measure ℝ := volume.restrict (Ioo 0 1)

def raw (k m : ℕ) (x : ℝ) : ℝ :=
  x^m * (-Real.log x)^(2*k) / ((2*k).factorial : ℝ)

def integrand (k m : ℕ) (x : ℝ) : ℝ := raw k m x / (1+x^2)

def moment (k m : ℕ) : ℝ := ∫ x, integrand k m x ∂unitMeasure

def betaPartialSum (k r : ℕ) : ℝ :=
  ∑ n ∈ Finset.range r, (-1:ℝ)^n / (2*(n:ℝ)+1)^(2*k+1)

def etaPartialSum (k r : ℕ) : ℝ :=
  ∑ n ∈ Finset.range r, (-1:ℝ)^n / ((n:ℝ)+1)^(2*k+1)

theorem raw_integrable (k m : ℕ) : Integrable (raw k m) unitMeasure :=
  (UnitLogMoments.integrable_pow_log m (2*k)).div_const _

theorem raw_integral (k m : ℕ) :
    (∫ x, raw k m x ∂unitMeasure) = 1 / ((m:ℝ)+1)^(2*k+1) := by
  rw [raw, integral_div, UnitLogMoments.integral_pow_log]
  have hf : ((2*k).factorial : ℝ) ≠ 0 := by positivity
  field_simp [hf]

theorem raw_nonneg (k m : ℕ) {x : ℝ} (hx : x ∈ Ioo 0 1) : 0 ≤ raw k m x := by
  unfold raw
  exact div_nonneg (mul_nonneg (pow_nonneg hx.1.le _) (by positivity)) (by positivity)

theorem integrand_bounds (k m : ℕ) {x : ℝ} (hx : x ∈ Ioo 0 1) :
    raw k m x / 2 ≤ integrand k m x ∧ integrand k m x ≤ raw k m x := by
  have hr := raw_nonneg k m hx
  have hd : (0:ℝ) < 1+x^2 := by positivity
  have hs : x^2 ≤ 1 := by nlinarith [hx.1, hx.2]
  constructor
  · unfold integrand
    apply (le_div_iff₀ hd).2
    nlinarith [mul_nonneg hr (sub_nonneg.mpr hs)]
  · exact div_le_self hr (by nlinarith [sq_nonneg x])

theorem integrand_integrable (k m : ℕ) : Integrable (integrand k m) unitMeasure := by
  apply (raw_integrable k m).mono' (by unfold integrand raw; fun_prop)
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg
    (show 0 ≤ integrand k m x from div_nonneg (raw_nonneg k m hx) (by positivity))]
  exact (integrand_bounds k m hx).2

/-- Two explicit bounds on every actual normalized density moment. -/
theorem moment_bounds (k m : ℕ) :
    (1 / ((m:ℝ)+1)^(2*k+1)) / 2 ≤ moment k m ∧
      moment k m ≤ 1 / ((m:ℝ)+1)^(2*k+1) := by
  constructor
  · have h := integral_mono_ae ((raw_integrable k m).div_const 2)
      (integrand_integrable k m)
      (show (fun x => raw k m x / 2) ≤ᵐ[unitMeasure] integrand k m from by
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
        exact (integrand_bounds k m hx).1)
    simpa [moment, integral_div, raw_integral] using h
  · have h := integral_mono_ae (integrand_integrable k m) (raw_integrable k m)
      (show integrand k m ≤ᵐ[unitMeasure] raw k m from by
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
        exact (integrand_bounds k m hx).2)
    simpa [moment, raw_integral] using h

theorem moment_pos (k m : ℕ) : 0 < moment k m :=
  lt_of_lt_of_le (by positivity) (moment_bounds k m).1

theorem moment_le (k m : ℕ) : moment k m ≤ 1 / ((m:ℝ)+1) := by
  apply (moment_bounds k m).2.trans
  apply one_div_le_one_div_of_le (by positivity)
  exact le_self_pow₀ (by have hm : (0:ℝ) ≤ m := Nat.cast_nonneg _; linarith) (by omega)

theorem moment_tendsto_zero (k : ℕ) : Tendsto (moment k) atTop (𝓝 0) :=
  squeeze_zero (fun m => (moment_pos k m).le) (moment_le k)
    tendsto_one_div_add_atTop_nhds_zero_nat

theorem moment_add_two (k m : ℕ) :
    moment k (m+2) = 1 / ((m:ℝ)+1)^(2*k+1) - moment k m := by
  have he (x : ℝ) : integrand k (m+2) x + integrand k m x = raw k m x := by
    have hd : (1:ℝ)+x^2 ≠ 0 := by positivity
    simp only [integrand, raw, pow_add]
    field_simp [hd]
    ring
  have h := integral_add (integrand_integrable k (m+2)) (integrand_integrable k m)
  simp_rw [he] at h
  rw [raw_integral] at h
  change _ = moment k (m+2) + moment k m at h
  linarith

/-- The actual even moments, uniformly in both k and r. -/
theorem even_moment (k r : ℕ) :
    moment k (2*r) = (-1:ℝ)^r * (moment k 0 - betaPartialSum k r) := by
  induction r with
  | zero => simp [betaPartialSum]
  | succ r ih =>
    rw [show 2*(r+1) = 2*r+2 by omega, moment_add_two, ih]
    simp only [betaPartialSum, Finset.sum_range_succ, pow_succ, Nat.cast_mul,
      Nat.cast_ofNat]
    have hs : (-1:ℝ)^r * (-1:ℝ)^r = 1 := by rw [← mul_pow]; norm_num
    have hr : (2:ℝ)*(r:ℝ)+1 ≠ 0 := by positivity
    field_simp [hr]
    nlinarith [hs]

/-- The ordered beta series equals the actual positive density integral. -/
theorem beta_ordered_limit (k : ℕ) :
    Tendsto (betaPartialSum k) atTop (𝓝 (moment k 0)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.2
  have hg : Tendsto (fun r : ℕ => 2*r) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    exact eventually_atTop.2 ⟨b, fun n hn => by omega⟩
  have hlim := (moment_tendsto_zero k).comp hg
  have he (r : ℕ) : ‖betaPartialSum k r - moment k 0‖ = moment k (2*r) := by
    have h := congrArg abs (even_moment k r)
    have hs : |(-1:ℝ)^r| = 1 := by norm_num [abs_pow]
    rw [abs_of_pos (moment_pos _ _), abs_mul, hs, one_mul] at h
    rw [Real.norm_eq_abs, abs_sub_comm]
    exact h.symm
  simpa only [Function.comp_apply, ← he] using hlim

end ManuscriptChain.BetaOddMoments
