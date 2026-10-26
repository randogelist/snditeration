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

namespace Experimental.P04_07

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

/-- Exact earlier Theorem 4.4 spectral input, not a root-count conclusion. -/
axiom weight_five_spectral_cap_input :
  ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
    ManuscriptChain.Spectral.actualOperatorNorm
      (ManuscriptChain.Real.manuscriptPencil (parameters n)) ≤
      Real.exp ((11411 / 1000 : ℝ) * latticeK n)

/-- Earlier Theorem 4.6(1) determinant lower rate in eventual-bound form. -/
axiom weight_five_determinant_lower_input :
  ∀ η : ℝ, 0 < η → ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
    (2331 / 10000 : ℝ) - η ≤
      Real.log |(actualB n).det| / (latticeK n : ℝ)^2

/-- Earlier Theorem 4.6(2) primitive-height upper input. -/
axiom weight_five_primitive_height_input :
  ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
    ManuscriptChain.Section4Resultant.naiveHeight (actualP n) ≤
      Real.exp ((1027 / 100 : ℝ) * (latticeK n : ℝ)^2)

/-- Generic integer-factor height estimate, separate from any zeta root claim. -/
axiom integer_factor_height_input (P F : ℤ[X])
    (hP : P ≠ 0) (hF : F ≠ 0) (hdiv : F ∣ P) :
    ManuscriptChain.Section4Resultant.naiveHeight F ≤
      (2 : ℝ)^P.natDegree * Real.sqrt ((P.natDegree : ℝ) + 1) *
        ManuscriptChain.Section4Resultant.naiveHeight P

end Experimental.P04_07
