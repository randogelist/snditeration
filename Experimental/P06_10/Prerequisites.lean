import Zetahyperbolic

/-!
Experimental prerequisite interface only. SOURCE_ONLY_UNCOMPILED.
No target theorem is asserted here. Named axioms are local, explicit upstream
obligations on the concrete definitions below, not evidence of certification.
-/
noncomputable section
open scoped BigOperators Topology
open Polynomial Matrix MeasureTheory Set Filter

namespace Experimental.P06_10

-- Reuse the actual finite pencil and already present asymptotic Gram interface.
export ManuscriptChain.PotentialGap
  (manuscript_normalized_log_identity normalized_log_identity
   height_decay_ratio_gt_581 lower_decay_bound_counterexample)
export ManuscriptChain.CoefficientGramGrowth
  (realGram one_le_det det_upper normalized_log_det_tendsto_zero)

def weightFiveParameters (n : ℕ) : ManuscriptChain.Real.Parameters :=
  { k := 2, m := 3, N := 3 * (n + 1), K := 30 * (n + 1) }

/-- Raw normalization data for the actual weight-five finite family. -/
structure NormalizationInput where
  scale : ℕ → ℝ
  scale_pos : ∀ n, 0 < scale n

/-- The source's coefficient bounds and independence, not a growth conclusion. -/
structure CoefficientFamilyInput where
  h : ℕ → ℕ
  coefficients : ∀ K, Matrix (Fin (h K)) (Fin (K + 1)) ℤ
  exponent : ℕ
  size_bound : ∀ K, h K ≤ K + 1
  independent_rows : ∀ K,
    Function.Injective ((coefficients K).map (Int.castRingHom ℝ)).vecMul
  entry_bound : ∀ K i j,
    |(coefficients K i j : ℝ)| ≤ (((K + 1 : ℕ) : ℝ) ^ exponent)

end Experimental.P06_10
