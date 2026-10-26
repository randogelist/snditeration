import Zetahyperbolic

/-!
Experimental object-interface ledger for printed Theorem 5.7.
SOURCE_ONLY_UNCOMPILED. There are deliberately NO axioms: the rational
function, the displayed coefficient table, and the displayed functional
must first be identified by an actual double-pole residue calculation.
No valuation, nonvanishing, or target theorem is assumed.
-/
noncomputable section
open Polynomial
open scoped BigOperators
namespace Experimental.P05_07

def numerator (n : ℕ) : ℚ[X] :=
  C (((6 * n).factorial : ℚ) ^ 2) *
    ∏ j ∈ Finset.range n, (X - C (j : ℚ)) ^ 5

def denominator (n : ℕ) : ℚ[X] :=
  ∏ k ∈ Finset.range (6 * n + 1), (X + C (k : ℚ)) ^ 2

/-- The actual rational function displayed in equation (5.8). -/
def rationalFunction (n : ℕ) : RatFunc ℚ :=
  (numerator n : RatFunc ℚ) / (denominator n : RatFunc ℚ)

/-- The manuscript's displayed coefficient table, not yet identified with
residues of rationalFunction. -/
def displayedA (n k : ℕ) : ℚ :=
  (-1 : ℚ) ^ k * ((6 * n).choose k : ℚ) ^ 2 *
    ((n + k).choose k : ℚ) ^ 5 * (n.factorial : ℚ)

def displayedB (n k : ℕ) : ℚ :=
  displayedA n k *
    (7 * ManuscriptChain.Real.harmonic 1 k -
      2 * ManuscriptChain.Real.harmonic 1 (6 * n - k) -
      5 * ManuscriptChain.Real.harmonic 1 (n + k))

def displayedU (a b c : ℤ) (k : ℕ) : ℚ :=
  (c : ℚ) - (a : ℚ) * ManuscriptChain.Real.harmonic 5 k -
    (b : ℚ) * ManuscriptChain.Real.harmonic 6 k

def displayedV (a b : ℤ) (k : ℕ) : ℚ :=
  if k = 0 then 0 else (a : ℚ) / (k : ℚ) ^ 6 +
    (b : ℚ) / (5 * (k : ℚ) ^ 7)

/-- This is the literal displayed finite formula only. -/
def displayedFunctional (a b c : ℤ) (n : ℕ) (P : ℚ[X]) : ℚ :=
  (1 / (n.factorial : ℚ)) *
    ∑ k ∈ Finset.range (6 * n + 1),
      (displayedA n k *
        (displayedU a b c k * P.derivative.eval (-(k : ℚ)) +
          displayedV a b k * P.eval (-(k : ℚ))) +
        displayedB n k * displayedU a b c k * P.eval (-(k : ℚ)))

def displayedDeterminant (a b c : ℤ) (n : ℕ) : ℚ :=
  Matrix.det (fun i j : Fin (3 * n) =>
    displayedFunctional a b c n (X ^ (i.val + j.val)))

end Experimental.P05_07
