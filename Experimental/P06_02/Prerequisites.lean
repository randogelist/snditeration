import Zetahyperbolic

/-!
Experimental prerequisite interface. SOURCE_ONLY_UNCOMPILED.
The named axioms below are explicit research dependencies, not accepted
proofs. This module must stay outside the verified umbrella and axiom audit.
It does not assert the target theorem or upgrade its tier.
-/
noncomputable section
open MeasureTheory Set Polynomial
open scoped BigOperators

namespace Experimental.P06_02

/-- The actual lcm denominator d_K = lcm(1,...,K). -/
def commonDenominator : ℕ → ℕ
  | 0 => 1
  | n + 1 => Nat.lcm (commonDenominator n) (n + 1)

/-- Upstream denominator clearing for a single harmonic number. -/
axiom harmonic_denominator_divides (s K r : ℕ) (hr : r ≤ K) :
  (ManuscriptChain.Real.harmonic s r).den ∣ commonDenominator K ^ s

/-- Terms obtained by expanding the extra 1/(1-x*y), on the actual measure. -/
def insertedGeometricTerm (r n : ℕ) (z : ℝ × ℝ) : ℝ :=
  (z.1 * z.2) ^ (r + n) * z.2 * ManuscriptChain.Beukers.density z

/-- Absolute integral summability needed for a justified interchange. -/
axiom inserted_geometric_integral_norm_summable (r : ℕ) :
  Summable (fun n => ∫ z, ‖insertedGeometricTerm r n z‖
    ∂ManuscriptChain.Beukers.squareMeasure)

end Experimental.P06_02
