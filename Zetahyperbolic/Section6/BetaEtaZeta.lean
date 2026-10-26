import Zetahyperbolic.Section6.BetaOddEta
import Zetahyperbolic.Section2.Moments

/-!
# Exact eta-zeta identification at every positive odd weight above one

Finite parity decompositions give the eta factor without any rearrangement at
s=1. The endpoint remains the independently proved removable value log 2.
-/
noncomputable section
open Filter
open scoped BigOperators Topology

namespace ManuscriptChain.BetaEtaZeta
open BetaOddMoments BetaOddEta

private def zetaPartial (k r : ℕ) : ℝ :=
  ∑ n ∈ Finset.range r, 1 / ((n:ℝ)+1)^(2*k+1)

private theorem zetaPartial_succ (k r : ℕ) :
    zetaPartial k (r+1) = zetaPartial k r + 1 / ((r:ℝ)+1)^(2*k+1) := by
  simp only [zetaPartial, Finset.sum_range_succ]

private theorem etaPartial_succ (k r : ℕ) :
    etaPartialSum k (r+1) = etaPartialSum k r + (-1:ℝ)^r / ((r:ℝ)+1)^(2*k+1) := by
  simp only [etaPartialSum, Finset.sum_range_succ]

private theorem eta_even_partial (k r : ℕ) :
    etaPartialSum k (2*r) = zetaPartial k (2*r) -
      (2 / (2:ℝ)^(2*k+1)) * zetaPartial k r := by
  induction r with
  | zero => simp [etaPartialSum, zetaPartial]
  | succ r ih =>
    rw [show 2*(r+1) = (2*r+1)+1 by omega, etaPartial_succ,
      etaPartial_succ, ih]
    simp only [zetaPartial_succ, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
      Nat.cast_one]
    have he : (-1:ℝ)^(2*r) = 1 := by rw [pow_mul]; norm_num
    have ho : (-1:ℝ)^(2*r+1) = -1 := by rw [pow_add, he]; norm_num
    rw [he, ho, show (2:ℝ)*(r:ℝ)+1+1 = 2*((r:ℝ)+1) by ring, mul_pow]
    have h2 : (2:ℝ)^(2*k+1) ≠ 0 := by positivity
    have hr : (r:ℝ)+1 ≠ 0 := by positivity
    field_simp [h2, hr] <;> ring

/-- The literal eta-zeta factor for all k>=1; no pole endpoint is included. -/
theorem etaValue_eq_zeta (k : ℕ) (hk : 1 ≤ k) :
    etaValue k = (1 - 1 / (2:ℝ)^(2*k)) * Real.zeta (2*k+1) := by
  have hz : Tendsto (zetaPartial k) atTop (𝓝 (Real.zeta (2*k+1))) := by
    change Tendsto (fun r : ℕ => ∑ n ∈ Finset.range r,
      1 / ((n:ℝ)+1)^(2*k+1)) atTop (𝓝 (Real.zeta (2*k+1)))
    simpa only [Nat.cast_add, Nat.cast_one] using
      (Real.zeta_series_hasSum (s := 2*k+1) (by omega)).tendsto_sum_nat
  have hg : Tendsto (fun r : ℕ => 2*r) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    exact eventually_atTop.2 ⟨b, fun n hn => by omega⟩
  have h := (hz.comp hg).sub (hz.const_mul (2 / (2:ℝ)^(2*k+1)))
  have he : Tendsto (fun r : ℕ => etaPartialSum k (2*r)) atTop
      (𝓝 (Real.zeta (2*k+1) - (2 / (2:ℝ)^(2*k+1)) * Real.zeta (2*k+1))) := by
    simpa only [Function.comp_apply, ← eta_even_partial] using h
  have hl := tendsto_nhds_unique ((eta_ordered_limit k).comp hg) he
  rw [hl, pow_succ]
  field_simp <;> ring

/-- Identification with Mathlib's actual Riemann zeta, not an unspecified sequence. -/
theorem etaValue_eq_riemannZeta_re (k : ℕ) (hk : 1 ≤ k) :
    etaValue k = (1 - 1 / (2:ℝ)^(2*k)) * (riemannZeta ((2*k+1:ℕ) : ℂ)).re := by
  rw [etaValue_eq_zeta k hk, Real.zeta_eq_riemannZeta_re (by omega : 1 < 2*k+1)]

/-- Exact odd moment formula of 6.15(2) at all positive k and every r. -/
theorem odd_moment_zeta (k r : ℕ) (hk : 1 ≤ k) :
    moment k (2*r+1) = ((-1:ℝ)^r / (2:ℝ)^(2*k+1)) *
      ((1 - 1 / (2:ℝ)^(2*k)) * Real.zeta (2*k+1) - etaPartialSum k r) := by
  rw [odd_moment, etaValue_eq_zeta k hk]

end ManuscriptChain.BetaEtaZeta
