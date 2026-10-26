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

namespace Experimental.P06_06

/-- Actual finite coefficient polynomial of the manuscript, evaluated at l. -/
def coefficientPolynomial (k : ℕ) (a : ℕ → ℤ) (l : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 k,
    (-1 : ℝ) ^ (k - m) * (a m : ℝ) * (2 * Real.pi * (l : ℝ)) ^ (2 * m) /
      ((2 * m).factorial : ℝ)

def weightTerm (k : ℕ) (a : ℕ → ℤ) (y : ℝ) (n : ℕ) : ℝ :=
  coefficientPolynomial k a (n + 1) * Real.exp (-2 * Real.pi * (n + 1) * y)

def coupledWeight (k : ℕ) (a : ℕ → ℤ) (y : ℝ) : ℝ :=
  2 * y ^ (2 * k + 1) * ∑' n, weightTerm k a y n

def coupledCenter (k : ℕ) (a : ℕ → ℤ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 k, (a m : ℝ) * ManuscriptChain.Real.zeta (2 * m + 1)

/-- Upstream polynomial-times-exponential summability, not a comparison estimate. -/
axiom weight_terms_summable (k : ℕ) (a : ℕ → ℤ) (y : ℝ) (hy : 0 < y) :
  Summable (weightTerm k a y)

/-- Leading-coefficient asymptotics required before proving a uniform discrete ratio. -/
axiom normalized_coefficient_ratio_limit (k : ℕ) (hk : 0 < k) (a : ℕ → ℤ) :
  Filter.Tendsto (fun n : ℕ =>
    ((2 * k).factorial : ℝ) * coefficientPolynomial k a (n + 1) /
      (2 * Real.pi * (n + 1)) ^ (2 * k))
    Filter.atTop (nhds (a k : ℝ))

end Experimental.P06_06
