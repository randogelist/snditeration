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

namespace Experimental.P04_08

/-- Exact manuscript weight-five lattice, with positive index n+1. -/
def parameters (n : ℕ) : ManuscriptChain.Real.Parameters where
  k := 2
  m := 3
  N := 3 * (n + 1)
  K := 30 * (n + 1)

def latticeK (n : ℕ) : ℕ := 30 * (n + 1)

def actualB (n : ℕ) :=
  ManuscriptChain.Spectral.whitenedMatrix
    (ManuscriptChain.Real.manuscriptPencil (parameters n))

def actualP (n : ℕ) : ℤ[X] :=
  ManuscriptChain.primitivePolynomial (parameters n)

/-- Upstream Theorem 4.4 spectral bound, kept distinct from an upper cluster bound. -/
axiom weight_five_spectral_cap_input :
  ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
    ManuscriptChain.Spectral.actualOperatorNorm
      (ManuscriptChain.Real.manuscriptPencil (parameters n)) ≤
      Real.exp ((11411 / 1000 : ℝ) * latticeK n)

/-- Upstream rational approximation consequence of Theorem 4.4 only.
This is NOT a claim that every root belongs to a small upper cluster disk. -/
axiom zeta_five_measure_input :
  ∃ b₀ : ℕ, ManuscriptChain.RealTransfer.RationalMeasure
    (ManuscriptChain.Real.zeta 5) 25687 b₀

end Experimental.P04_08
