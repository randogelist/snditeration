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

namespace Experimental.P06_05

/-- Actual finite beta harmonic numbers, with integer odd denominators. -/
def betaHarmonic (s j : ℕ) : ℚ :=
  ∑ n ∈ Finset.range j, (-1 : ℚ) ^ n / (((2 * n + 1 : ℕ) : ℚ) ^ s)

/-- Remove the unique potentially p-divisible odd denominator when j < p. -/
def betaHarmonicResidual (s p j : ℕ) : ℚ :=
  betaHarmonic s j -
    if (p - 1) / 2 < j then (-1 : ℚ) ^ ((p - 1) / 2) / (p : ℚ) ^ s else 0

/-- Elementary upstream β-harmonic residue input, not a determinant valuation. -/
axiom beta_harmonic_residual_p_integral (p s j : ℕ)
    (hp : Nat.Prime p) (hpodd : 2 < p) (hs : 0 < s) (hj : j < p) :
    ¬ p ∣ (betaHarmonicResidual s p j).den

/-- The manuscript's q-dependent parameters, without claiming a pencil calibration. -/
def multiplicity (q : ℕ) : ℕ := (q - 1) / 8
def initialLength (q : ℕ) : ℕ := 4 * multiplicity q
def cutoff (q : ℕ) : ℕ := 5 * multiplicity q

def oddDenominator (N : ℕ) : ℚ[X] :=
  ∏ j ∈ Finset.range N, (X + C (((2 * j + 1 : ℕ) : ℚ) ^ 2))

end Experimental.P06_05
