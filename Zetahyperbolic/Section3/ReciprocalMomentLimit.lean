import Zetahyperbolic.Section3.ReciprocalMoments
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-! The corrected reciprocal-moment approximation converges to the exact root radius. -/

noncomputable section
open Filter
open scoped Topology

namespace ManuscriptChain.Spectral

variable {n : ℕ}

theorem reciprocalMoment_exponent_tendsto :
    Tendsto (fun r : ℕ => -((2*r : ℕ) : ℝ)⁻¹) atTop (𝓝 0) := by
  simpa [Nat.cast_mul, mul_inv_rev, neg_mul, mul_comm] using
    (tendsto_inv_atTop_nhds_zero_nat :
      Tendsto (fun r : ℕ => (r : ℝ)⁻¹) atTop (𝓝 0)).const_mul (-(2 : ℝ)⁻¹)

theorem reciprocalRootMoment_ratio_tendsto (p : SymmetricAffinePencil n)
    (positive : p.base.PosDef) (direction_nonzero : p.direction.det ≠ 0)
    (hn : 0 < n) :
    Tendsto (fun r : ℕ =>
      reciprocalRootMoment p r ^ (-((2*r : ℕ) : ℝ)⁻¹) /
        (1 / actualOperatorNorm p)) atTop (𝓝 1) := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  have hlo : Tendsto (fun r : ℕ => (n : ℝ) ^ (-((2*r : ℕ) : ℝ)⁻¹))
      atTop (𝓝 1) := by
    simpa only [Real.rpow_zero] using
      (tendsto_const_nhds (x := (n : ℝ))).rpow reciprocalMoment_exponent_tendsto (Or.inl hn0)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo tendsto_const_nhds
  · exact (eventually_gt_atTop 0).mono fun r hr =>
      (reciprocalRootMoment_approximation_bounds p positive direction_nonzero hn r hr).1
  · exact (eventually_gt_atTop 0).mono fun r hr =>
      (reciprocalRootMoment_approximation_bounds p positive direction_nonzero hn r hr).2

theorem reciprocalRootMoment_tendsto_radius (p : SymmetricAffinePencil n)
    (positive : p.base.PosDef) (direction_nonzero : p.direction.det ≠ 0)
    (hn : 0 < n) :
    Tendsto (fun r : ℕ => reciprocalRootMoment p r ^ (-((2*r : ℕ) : ℝ)⁻¹))
      atTop (𝓝 (1 / actualOperatorNorm p)) := by
  have hd : 1 / actualOperatorNorm p ≠ 0 :=
    ne_of_gt (one_div_pos.mpr (actualOperatorNorm_pos p positive direction_nonzero hn))
  simpa only [div_mul_cancel₀ _ hd, one_mul] using
    (reciprocalRootMoment_ratio_tendsto p positive direction_nonzero hn).mul_const
      (1 / actualOperatorNorm p)

end ManuscriptChain.Spectral

namespace ManuscriptChain

theorem ACTUAL_RECIPROCAL_MOMENT_LIMIT (p : Real.Parameters) (hp : Real.Admissible p) :
    Tendsto (fun r : ℕ =>
      Spectral.reciprocalRootMoment (Real.manuscriptPencil p) r ^ (-((2*r : ℕ) : ℝ)⁻¹))
      atTop (𝓝 (1 / Spectral.actualOperatorNorm (Real.manuscriptPencil p))) :=
  Spectral.reciprocalRootMoment_tendsto_radius (Real.manuscriptPencil p) (GRAM_POSITIVE p hp)
    (General.derivative_nonsingular p) (Nat.sub_pos_of_lt hp.N_lt_K)

end ManuscriptChain
