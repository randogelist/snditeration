import Zetahyperbolic

/-!
EXPERIMENTAL PREREQUISITE LAYER — SOURCE_ONLY_UNCOMPILED.
The axioms in this file are explicit research assumptions. They are not proofs,
not part of the certified umbrella, and may not enter a production proof receipt.
No full target theorem or contradiction is admitted here.
-/
noncomputable section
open scoped BigOperators
open Polynomial MeasureTheory Set

namespace Experimental.P04_01

/-- Additional effective data; not asserted to follow from bare eventuality. -/
structure EffectiveOnsetData where
  polynomials : ℕ → ℤ[X]
  center : ℝ
  onset : ℕ
  exponent : ℕ
  degreeRate : ℚ
  decayRate : ℚ
  separationRate : ℚ
  indexRate : ℚ
  comparisonRate : ℚ
  degree_nonnegative : 0 ≤ degreeRate
  index_positive : 0 < indexRate
  comparison_positive : 0 < comparisonRate
  decay_margin : degreeRate / indexRate < decayRate
  separation_margin : separationRate < comparisonRate
  exponent_margin : comparisonRate * indexRate ≤ exponent
  degree_bound : ∀ K, onset ≤ K →
    ((polynomials K).natDegree : ℝ) ≤ (degreeRate : ℝ) * K
  evaluation_bound : ∀ K, onset ≤ K →
    ManuscriptChain.RealTransfer.evalReal (polynomials K) center ≠ 0 ∧
    |ManuscriptChain.RealTransfer.evalReal (polynomials K) center| ≤
      Real.exp (-(decayRate : ℝ) * (K : ℝ)^2)
  root_bound : ∀ K, onset ≤ K →
    ∀ r ∈ ((polynomials K).map (algebraMap ℤ ℂ)).roots,
      Real.exp (-(separationRate : ℝ) * K) ≤ ‖(center : ℂ) - r‖

/-- Existing computable threshold; no new rate or onset existence is postulated. -/
def explicitThreshold (d : EffectiveOnsetData) : ℕ :=
  ManuscriptChain.Section4EffectiveBudget.denominatorThreshold
    d.onset d.degreeRate d.decayRate d.separationRate d.indexRate d.comparisonRate

end Experimental.P04_01
