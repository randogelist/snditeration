import Zetahyperbolic

/-! SOURCE_ONLY_UNCOMPILED. Cyclic Lanczos construction is an upstream input
for a separately corrected resolvent formula. No original continued fraction,
unconditional cyclicity, or root-collapse estimate is assumed. -/
noncomputable section
open scoped BigOperators
namespace Experimental.P03_05
open ManuscriptChain

def actualWhitened (p : Real.Parameters) : Matrix (Fin p.h) (Fin p.h) ℝ :=
  Spectral.whitenedMatrix (Real.manuscriptPencil p)

def krylovMatrix (p : Real.Parameters) (v : Fin p.h → ℝ) :
    Matrix (Fin p.h) (Fin p.h) ℝ :=
  fun i j => Matrix.mulVec (actualWhitened p ^ j.val) v i

def IsJacobiMatrix {n : ℕ} (T : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  (∀ i j, i.val + 1 < j.val ∨ j.val + 1 < i.val → T i j = 0) ∧
  (∀ i j, j.val = i.val + 1 → 0 < T i j)

/-- The cyclicity and normalization premises are explicit. In particular this
does not assert that the paper's chosen endpoint vector is cyclic. -/
axiom lanczosBasisOfCyclic (p : Real.Parameters) (hp : Real.Admissible p)
    (hh : 0 < p.h) (v : Fin p.h → ℝ)
    (hunit : ∑ i, v i ^ 2 = 1) (hcyclic : (krylovMatrix p v).det ≠ 0) :
  ∃ Q : Matrix (Fin p.h) (Fin p.h) ℝ,
    Q.transpose * Q = 1 ∧
    (∀ i, Q i ⟨0, hh⟩ = v i) ∧
    IsJacobiMatrix (Q.transpose * actualWhitened p * Q)

end Experimental.P03_05
