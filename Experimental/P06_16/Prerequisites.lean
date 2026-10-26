import Zetahyperbolic

/-!
Experimental prerequisite interface only. SOURCE_ONLY_UNCOMPILED.
No target theorem is asserted here. Named axioms are local, explicit upstream
obligations on the concrete definitions below, not evidence of certification.
-/
noncomputable section
open scoped BigOperators Topology
open Polynomial Matrix MeasureTheory Set Filter

namespace Experimental.P06_16

def betaTerm (s n : ℕ) : ℝ :=
  (-1 : ℝ) ^ n / (((2 * n + 1 : ℕ) : ℝ) ^ s)

def betaValue (s : ℕ) : ℝ := ∑' n : ℕ, betaTerm s n

def betaHarmonic (s n : ℕ) : ℚ :=
  ∑ j ∈ Finset.range n, (-1 : ℚ) ^ j / (((2 * j + 1 : ℕ) : ℚ) ^ s)

/-- Explicit common-pole coefficient before any functional identity is asserted. -/
def normalizedBetaPoleCoefficient (k r j : ℕ) : ℚ :=
  (j : ℚ) ^ (2 * (k + 1 - r)) * (2 * (j : ℚ)) ^ (2 * r - 2) /
    (4 : ℚ) ^ (r - 1)

/-- Source integer data, with no assumed hyperbolicity or arithmetic overhead conclusion. -/
structure CouplingInput where
  k : ℕ
  k_positive : 0 < k
  zetaCoefficients : Fin k → ℤ
  betaCoefficients : Fin k → ℤ
  topIndex : Fin k
  topIndex_eq : topIndex.val + 1 = k
  top_positive : 0 < zetaCoefficients topIndex

def combinedValue (c : CouplingInput) : ℝ :=
  (∑ i : Fin c.k, (c.zetaCoefficients i : ℝ) *
    ManuscriptChain.Real.zeta (2 * (i.val + 1) + 1)) +
  ∑ i : Fin c.k, (c.betaCoefficients i : ℝ) * betaValue (2 * (i.val + 1))

export ManuscriptChain.Hyperbolic (density density_pos)
export ManuscriptChain.Real (entryM derivativeMatrix)

end Experimental.P06_16
