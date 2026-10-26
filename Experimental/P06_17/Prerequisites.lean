import Zetahyperbolic

/-!
Experimental prerequisite interface only. SOURCE_ONLY_UNCOMPILED.
No target theorem is asserted here. Named axioms are local, explicit upstream
obligations on the concrete definitions below, not evidence of certification.
-/
noncomputable section
open scoped BigOperators Topology
open Polynomial Matrix MeasureTheory Set Filter

namespace Experimental.P06_17

def betaTerm (s n : ℕ) : ℝ :=
  (-1 : ℝ) ^ n / (((2 * n + 1 : ℕ) : ℝ) ^ s)

def betaValue (s : ℕ) : ℝ := ∑' n : ℕ, betaTerm s n

def betaHarmonic (s n : ℕ) : ℚ :=
  ∑ j ∈ Finset.range n, (-1 : ℚ) ^ j / (((2 * j + 1 : ℕ) : ℚ) ^ s)

def betaFourDensity (z : ℝ × ℝ) : ℝ :=
  (-Real.log (z.1 * z.2)) ^ 2 / (6 * (1 + z.1 ^ 2 * z.2 ^ 2))

def betaFourMoment (n l : ℕ) : ℝ :=
  ∫ z : ℝ × ℝ in (Ioo (0 : ℝ) 1) ×ˢ (Ioo (0 : ℝ) 1),
    z.1 ^ (4 * n) * z.2 ^ (4 * l) * betaFourDensity z

/-- Earlier Proposition 5.3, limited to its explicit beta-four base case. -/
axiom upstream_beta_four_diagonal_moment (n : ℕ) :
  betaFourMoment n n = betaValue 4 - (betaHarmonic 4 (2 * n) : ℝ)

axiom upstream_beta_four_offdiagonal_moment (n l : ℕ) (hne : n ≠ l) :
  betaFourMoment n l =
    ((betaHarmonic 3 (2 * n) : ℝ) - (betaHarmonic 3 (2 * l) : ℝ)) /
      (12 * ((n : ℝ) - (l : ℝ)))

export ManuscriptChain.DualSpectral
  (coefficientSlope coefficientRowsSeparate coefficientSlope_posDef)
export ManuscriptChain.Beukers
  (diagonal_moment offdiagonal_moment_eq_rat polynomialMomentForm_eq_krein)
export ManuscriptChain.CoefficientGramGrowth (normalized_log_det_tendsto_zero)

end Experimental.P06_17
