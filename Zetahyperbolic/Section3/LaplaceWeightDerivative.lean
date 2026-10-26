import Zetahyperbolic.Section3.RationalIntegralBridge
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-! Actual Laplace deformation of the manuscript weight.
Adapted from the companion zetahyperbolic-axiom source; no verification
status is inherited. All results are rechecked in the destination project. -/
noncomputable section
open scoped BigOperators Topology
open MeasureTheory Set Filter Matrix Polynomial

namespace ManuscriptChain.LaplaceWeightDerivative

open ManuscriptChain

def term (j n : ℕ) (τ y : ℝ) : ℝ :=
  ((n+1 : ℕ) : ℝ)^j * Real.exp (-(2*Real.pi*((n+1 : ℕ) : ℝ)*y)*τ)

def termDerivative (j n : ℕ) (τ y : ℝ) : ℝ :=
  -((2*Real.pi*((n+1 : ℕ) : ℝ)*y) * term j n τ y)

def density (k : ℕ) (τ y : ℝ) : ℝ :=
  (2*(2*Real.pi)^(2*k)/(Nat.factorial (2*k) : ℝ)) * y^(2*k+1) *
    ∑' n, term (2*k) n τ y

def densityDerivative (k : ℕ) (τ y : ℝ) : ℝ :=
  (2*(2*Real.pi)^(2*k)/(Nat.factorial (2*k) : ℝ)) * y^(2*k+1) *
    ∑' n, termDerivative (2*k) n τ y

theorem summable_term (j : ℕ) {τ y : ℝ} (hτ : 0 < τ) (hy : 0 < y) :
    Summable (fun n => term j n τ y) := by
  have h := (summable_nat_add_iff 1).mpr
    (Real.summable_pow_mul_exp_neg_nat_mul j
      (show 0 < 2*Real.pi*y*τ by positivity))
  convert h using 1
  funext n
  unfold term
  congr 2
  ring

theorem term_hasDerivAt (j n : ℕ) (τ y : ℝ) :
    HasDerivAt (fun z => term j n z y) (termDerivative j n τ y) τ := by
  have hd := ((hasDerivAt_id τ).const_mul (-(2*Real.pi*((n+1 : ℕ) : ℝ)*y))).exp
  convert hd.const_mul (((n+1 : ℕ) : ℝ)^j) using 1 <;>
    simp only [term, termDerivative] <;> ring

theorem rate_mul_exp_bound {a λ τ : ℝ} (ha : 0 < a) (hλ : 0 ≤ λ)
    (hτ : 2*a ≤ τ) :
    λ * Real.exp (-λ*τ) ≤ a⁻¹ * Real.exp (-λ*a) := by
  have hh : (a*λ)*Real.exp (-(a*λ)) ≤ 1 :=
    (Real.mul_exp_neg_le_exp_neg_one (a*λ)).trans
      (Real.exp_le_one_iff.mpr (by norm_num))
  calc
    λ * Real.exp (-λ*τ) ≤ λ * Real.exp (-λ*(2*a)) := by
      apply mul_le_mul_of_nonneg_left _ hλ
      apply Real.exp_le_exp.mpr
      nlinarith
    _ = a⁻¹ * ((a*λ)*Real.exp (-(a*λ))) * Real.exp (-λ*a) := by
      rw [show -λ*(2*a) = -(a*λ) + (-λ*a) by ring, Real.exp_add]
      field_simp
      ring
    _ ≤ a⁻¹ * 1 * Real.exp (-λ*a) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hh (inv_nonneg.mpr ha.le)) (Real.exp_pos _).le
    _ = _ := by ring

theorem termDerivative_bound (j n : ℕ) {a τ y : ℝ}
    (ha : 0 < a) (hy : 0 < y) (hτ : 2*a ≤ τ) :
    ‖termDerivative j n τ y‖ ≤ a⁻¹ * term j n a y := by
  have hc : 0 ≤ (((n+1 : ℕ) : ℝ)^j) := by positivity
  have hλ : 0 ≤ 2*Real.pi*((n+1 : ℕ) : ℝ)*y := by positivity
  have h := mul_le_mul_of_nonneg_left (rate_mul_exp_bound ha hλ hτ) hc
  simpa only [termDerivative, term, norm_neg, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg hλ (mul_nonneg hc (Real.exp_pos _).le)),
    mul_assoc, mul_left_comm, mul_comm] using h

theorem density_hasDerivAt (k : ℕ) {τ y : ℝ} (hτ : 0 < τ) (hy : 0 < y) :
    HasDerivAt (fun z => density k z y) (densityDerivative k τ y) τ := by
  let a := τ/4
  have ha : 0 < a := by dsimp [a]; positivity
  have hmem : τ ∈ Ioi (2*a) := by dsimp [a]; linarith
  have hsum := hasDerivAt_tsum_of_isPreconnected
    ((summable_term (2*k) ha hy).mul_left a⁻¹)
    isOpen_Ioi (convex_Ioi (2*a)).isPreconnected
    (fun n z _ => term_hasDerivAt (2*k) n z y)
    (fun n z hz => termDerivative_bound (2*k) n ha hy (le_of_lt hz))
    hmem (summable_term (2*k) hτ hy) hmem
  exact hsum.const_mul _

theorem densityDerivative_bound (k : ℕ) {a τ y : ℝ}
    (ha : 0 < a) (hy : 0 < y) (hτ : 2*a ≤ τ) :
    ‖densityDerivative k τ y‖ ≤ a⁻¹ * density k a y := by
  have hsum : Summable (fun n => a⁻¹ * term (2*k) n a y) :=
    (summable_term (2*k) ha hy).mul_left _
  have hb := tsum_of_norm_bounded hsum.hasSum
    (fun n => termDerivative_bound (2*k) n ha hy hτ)
  have hc : 0 ≤ (2*(2*Real.pi)^(2*k)/(Nat.factorial (2*k) : ℝ))*y^(2*k+1) :=
    by positivity
  unfold densityDerivative density
  rw [norm_mul, Real.norm_of_nonneg hc]
  calc
    _ ≤ ((2*(2*Real.pi)^(2*k)/(Nat.factorial (2*k) : ℝ))*y^(2*k+1)) *
        ∑' n, a⁻¹ * term (2*k) n a y := mul_le_mul_of_nonneg_left hb hc
    _ = _ := by rw [tsum_mul_left]; ring

theorem density_eq_scaled (k : ℕ) {τ : ℝ} (hτ : τ ≠ 0) (y : ℝ) :
    density k τ y = Hyperbolic.density k (τ*y) / τ^(2*k+1) := by
  unfold density Hyperbolic.density
  have he : (fun n => term (2*k) n τ y) =
      (fun n => Hyperbolic.exponentialTerm k n (τ*y)) := by
    funext n
    unfold term Hyperbolic.exponentialTerm
    congr 2
    ring
  rw [he, mul_pow]
  field_simp

@[simp] theorem density_one (k : ℕ) (y : ℝ) :
    density k 1 y = Hyperbolic.density k y := by
  rw [density_eq_scaled k one_ne_zero]
  simp

theorem density_positive (k : ℕ) {τ y : ℝ} (hτ : 0 < τ) (hy : 0 < y) :
    0 < density k τ y := by
  rw [density_eq_scaled k hτ.ne']
  exact div_pos (Hyperbolic.density_pos k (mul_pos hτ hy)) (pow_pos hτ _)

theorem measurable_density (k : ℕ) (τ : ℝ) : Measurable (density k τ) := by
  unfold density
  exact (measurable_const.mul (measurable_id.pow_const _)).mul
    (Measurable.tsum (fun n => by unfold term; fun_prop))

theorem measurable_densityDerivative (k : ℕ) (τ : ℝ) :
    Measurable (densityDerivative k τ) := by
  unfold densityDerivative
  exact (measurable_const.mul (measurable_id.pow_const _)).mul
    (Measurable.tsum (fun n => by unfold termDerivative term; fun_prop))

theorem integrable_monomial_density (k e : ℕ) {τ : ℝ} (hτ : 0 < τ) :
    IntegrableOn (fun y : ℝ => y^(2*e)*density k τ y) (Ioi 0) := by
  have hi := (integrableOn_Ioi_comp_mul_left_iff
    (fun z : ℝ => z^(2*e)*Hyperbolic.density k z) 0 hτ).mpr
    (by simpa using Hyperbolic.integrableOn_monomial_density k e)
  have hc := hi.div_const (τ^(2*e+(2*k+1)))
  apply hc.congr
  filter_upwards [] with y
  rw [density_eq_scaled k hτ.ne', mul_pow, pow_add]
  field_simp


end ManuscriptChain.LaplaceWeightDerivative
