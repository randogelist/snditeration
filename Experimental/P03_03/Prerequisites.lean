import Zetahyperbolic

/-! SOURCE_ONLY_UNCOMPILED. Named experimental inputs only; no theorem 3.3
conclusion, mixed-minor positivity or measure uniqueness is assumed. -/
noncomputable section
open scoped BigOperators
open MeasureTheory
namespace Experimental.P03_03
open ManuscriptChain

def actualMoment (p : Real.Parameters) (r : ℕ) : ℝ :=
  ∫ t : ℝ, t ^ r ∂ConcreteMoment.momentMeasure p

/-- Upstream analytic growth estimate for the exact manuscript measure. -/
axiom actualMomentFactorialMajorant (p : Real.Parameters) (hp : Real.Admissible p) :
  ∃ C : ℝ, 0 < C ∧ ∃ A : ℕ, ∀ r : ℕ,
    |actualMoment p r| ≤ C * (Nat.factorial (2 * r + A) : ℝ)

/-- Upstream finite generalized Vandermonde sign lemma; it assumes no moment
minor, Gram determinant or determinacy conclusion. -/
axiom generalizedVandermondePositive (r : ℕ) (exponents : Fin r → ℕ)
    (nodes : Fin r → ℝ) (hexponents : StrictMono exponents)
    (hnodes : StrictMono nodes) (hpositive : ∀ i, 0 < nodes i) :
  0 < Matrix.det (fun i j : Fin r => nodes i ^ exponents j)

theorem existingActualGramInput (p : Real.Parameters) (hp : Real.Admissible p) :
    (Real.gram p (Real.zeta p.weight)).PosDef :=
  GRAM_POSITIVE p hp

end Experimental.P03_03
