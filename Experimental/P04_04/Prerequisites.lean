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

namespace Experimental.P04_04

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

/-- The printed rational normalization S_K in equation (4.2). -/
def paperS (n : ℕ) : ℚ :=
  let p := parameters n
  ((p.K.factorial : ℚ) ^ (2 * p.h) * (4 : ℚ) ^ (p.h - 1)) /
    ((p.N.factorial : ℚ) ^ (12 * p.h) *
      ∏ i ∈ Finset.Icc 1 (p.h - 1), (((2 * i).factorial : ℚ) ^ 2))

def normalizedGramValue (n : ℕ) : ℝ :=
  (paperS n : ℝ) * ManuscriptChain.Real.evalQ
    (ManuscriptChain.Real.delta (parameters n)) (ManuscriptChain.Real.zeta 5)

/-- External Fauzan [5] prime-multiplier input, not the spectral-cap conclusion.
The multiplier remains existential; its explicit prime exponents are NOT supplied. -/
axiom fauzan_multiplier_input :
  ∃ multiplier : ℕ → ℚ,
    (∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
      0 < multiplier n ∧
      ∃ Q : ℤ[X], Q.map (Int.castRingHom ℚ) =
        C (multiplier n * paperS n) * ManuscriptChain.Real.delta (parameters n)) ∧
    (∀ η : ℝ, 0 < η → ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
      Real.log (multiplier n : ℝ) / (latticeK n : ℝ)^2 ≤
        -(232425 / 100000 : ℝ) + η)

/-- External Fauzan [5] normalized Gram-energy upper rate, separately exposed. -/
axiom fauzan_gram_energy_input :
  ∀ η : ℝ, 0 < η → ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
    Real.log (normalizedGramValue n) / (latticeK n : ℝ)^2 ≤
      (11619 / 5000 : ℝ) + η

/-- Classical finite polynomial L² evaluation input, motivated by the cited
Legendre/Laplace bound. No uniform estimate for the actual B_K is assumed. -/
def legendreRadius (a b u : ℝ) : ℝ :=
  let Y := (2 * u^2 + a + b) / (b - a)
  Y + Real.sqrt (Y^2 - 1)

axiom negative_node_polynomial_bound
    (p : ℝ[X]) (h : ℕ) (hh : 0 < h) (hp : p.natDegree < h)
    (a b u : ℝ) (ha : 0 < a) (hab : a < b) (hu : 0 ≤ u) :
    |p.eval (-(u^2))|^2 ≤
      (h : ℝ)^2 / (b - a) * (legendreRadius a b u)^(2 * (h - 1)) *
        (∫ t in Set.Icc a b, (p.eval t)^2)

end Experimental.P04_04
