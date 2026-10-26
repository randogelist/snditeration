import Zetahyperbolic

/-!
Experimental prerequisite interface only. SOURCE_ONLY_UNCOMPILED.
No target theorem is asserted here. Named axioms are local, explicit upstream
obligations on the concrete definitions below, not evidence of certification.
-/
noncomputable section
open scoped BigOperators Topology
open Polynomial Matrix MeasureTheory Set Filter

namespace Experimental.P06_18

def betaTerm (s n : ℕ) : ℝ :=
  (-1 : ℝ) ^ n / (((2 * n + 1 : ℕ) : ℝ) ^ s)

def betaValue (s : ℕ) : ℝ := ∑' n : ℕ, betaTerm s n

def betaHarmonic (s n : ℕ) : ℚ :=
  ∑ j ∈ Finset.range n, (-1 : ℚ) ^ j / (((2 * j + 1 : ℕ) : ℚ) ^ s)

def shiftedNumerator (N M k r i j : ℕ) : ℚ[X] :=
  (-X) ^ (k + 1 - r) * ManuscriptChain.Real.D N ^ (2 * M) * X ^ (i + j)

def shiftedQuotient (K N M k r i j : ℕ) : ℚ[X] :=
  shiftedNumerator N M k r i j / ManuscriptChain.Real.D K

/-- Actual degree parameters, not quotient-vanishing or integrality conclusions. -/
structure PrincipalMinorInput where
  K : ℕ
  N : ℕ
  M : ℕ
  k : ℕ
  rmin : ℕ
  minorSize : ℕ
  N_lt_K : N < K
  M_positive : 0 < M
  rmin_positive : 0 < rmin
  rmin_le_k : rmin ≤ k
  size_positive : 0 < minorSize
  threshold : 2 * M * N + 2 * minorSize - 2 + k + 1 - rmin < K

export ManuscriptChain.Real (D_eq_prod_Icc D_factorization)

end Experimental.P06_18
