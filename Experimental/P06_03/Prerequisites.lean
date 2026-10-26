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

namespace Experimental.P06_03

/-- Actual coefficients of x^rho + x^(rho+q), with the manuscript K=2q-1. -/
def qBasisCoefficients (q : ℕ) (i : Fin q)
    (r : Fin ((2 * q - 1) + 1)) : ℚ :=
  if r.val = i.val ∨ r.val = i.val + q then 1 else 0

/-- The actual upstream dual pencil, not an abstract matrix certificate. -/
def qPencil (q : ℕ) : Matrix (Fin q) (Fin q) ℚ[X] :=
  fun i j => ManuscriptChain.Real.dualEntry 7 (qBasisCoefficients q) i j

def qDeterminant (q : ℕ) : ℚ[X] := Matrix.det (qPencil q)

def harmonicResidual (s q r : ℕ) : ℚ :=
  ManuscriptChain.Real.harmonic s r -
    if q ≤ r then 1 / (q : ℚ) ^ s else 0

/-- Lower-level arithmetic input from the 6.1 analysis, not 6.3 nonvanishing. -/
axiom upstream_harmonic_residual_p_integral (q s r : ℕ)
    (hq : Nat.Prime q) (hs : 0 < s) (hr : r < 2 * q) :
    ¬ q ∣ (harmonicResidual s q r).den

/-- Actual polynomial space used by the disputed second clause. -/
def conePolynomial (h : ℕ) (Q : ℚ[X]) : ℚ[X] :=
  X ^ (2 * h) * (1 - X) ^ h * Q

def negativeMode (m ν : ℕ) (x : ℝ) : ℝ :=
  x ^ m * ((-Real.log x) ^ ν - (-Real.log x) ^ (5 - ν))

def negativeMoment (P : ℚ[X]) (m ν : ℕ) : ℝ :=
  ∫ x : ℝ in Ioo 0 1, P.eval₂ (Rat.castHom ℝ) x * negativeMode m ν x

-- Deliberately no axiom asserting positivity, a tail bound or target valuation.
end Experimental.P06_03
