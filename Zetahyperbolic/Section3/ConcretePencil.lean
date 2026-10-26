import Zetahyperbolic.Section2.PoleDiagonalization
import Zetahyperbolic.Section3.SymmetricAffinePencil

/-!
# Manuscript Section 3: the actual rational Hankel pencil

Shows that the Section 2 rational determinant is the determinant of the
symmetric real affine pencil centered at the Dirichlet series ζ(2k+1).
The moment-integral identity and positivity of this concrete Gram matrix
are not asserted here.
-/

noncomputable section
open scoped BigOperators
open Polynomial

namespace ManuscriptChain.Real

theorem numerator_symmetric (p : Parameters) (i j : ℕ) :
    numerator p i j = numerator p j i := by
  simp only [numerator, Nat.add_comm]

theorem entryA_symmetric (p : Parameters) (i j : ℕ) :
    entryA p i j = entryA p j i := by
  simp only [entryA, quotient, residue, numerator_symmetric p i j]

theorem entryM_symmetric (p : Parameters) (i j : ℕ) :
    entryM p i j = entryM p j i := by
  simp only [entryM, residue, numerator_symmetric p i j]

@[simp] theorem evalQ_pencil (p : Parameters) (i j : Fin p.h) (x : ℝ) :
    evalQ (pencil p i j) x =
      (entryA p i.val j.val : ℝ) + (entryM p i.val j.val : ℝ) * x := by
  simp [evalQ, realPolynomial, pencil]

theorem gram_symmetric (p : Parameters) (x : ℝ) : (gram p x).IsSymm := by
  ext i j
  simp only [Matrix.transpose_apply, gram, evalQ_pencil,
    entryA_symmetric p j.val i.val, entryM_symmetric p j.val i.val]

theorem derivativeMatrix_symmetric (p : Parameters) : (derivativeMatrix p).IsSymm := by
  ext i j
  simp only [Matrix.transpose_apply, derivativeMatrix, entryM_symmetric p j.val i.val]

def manuscriptPencil (p : Parameters) : Spectral.SymmetricAffinePencil p.h where
  center := zeta p.weight
  base := gram p (zeta p.weight)
  direction := derivativeMatrix p
  base_symmetric := gram_symmetric p _
  direction_symmetric := derivativeMatrix_symmetric p

@[simp] theorem manuscriptPencil_center (p : Parameters) :
    (manuscriptPencil p).center = zeta p.weight := rfl

theorem manuscriptPencil_matrixAt (p : Parameters) (x : ℝ) :
    (manuscriptPencil p).matrixAt x = gram p x := by
  ext i j
  simp only [Spectral.SymmetricAffinePencil.matrixAt, manuscriptPencil,
    Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, gram, evalQ_pencil,
    derivativeMatrix]
  ring

theorem manuscriptPencil_polynomialMatrix (p : Parameters) :
    (manuscriptPencil p).polynomialMatrix =
      (pencil p).map (Polynomial.mapRingHom (Rat.castHom ℝ)) := by
  apply Matrix.ext
  intro i j
  simp [Spectral.SymmetricAffinePencil.polynomialMatrix, manuscriptPencil,
    gram, evalQ, realPolynomial, derivativeMatrix, pencil, Polynomial.mapRingHom]
  ring

theorem manuscriptPencil_detPolynomial (p : Parameters) :
    (manuscriptPencil p).detPolynomial = realPolynomial (delta p) := by
  unfold Spectral.SymmetricAffinePencil.detPolynomial
  rw [manuscriptPencil_polynomialMatrix]
  exact ((Polynomial.mapRingHom (Rat.castHom ℝ)).map_det (pencil p)).symm

theorem delta_eval_eq_det_gram (p : Parameters) (x : ℝ) :
    evalQ (delta p) x = Matrix.det (gram p x) := by
  rw [evalQ, ← manuscriptPencil_detPolynomial,
    Spectral.SymmetricAffinePencil.eval_detPolynomial]
  simp only [Spectral.SymmetricAffinePencil.detValue, manuscriptPencil_matrixAt]

theorem delta_nonzero_of_positive (p : Parameters)
    (h : (gram p (zeta p.weight)).PosDef) :
    evalQ (delta p) (zeta p.weight) ≠ 0 := by
  have hc := (manuscriptPencil p).center_nonvanishing_of_positive h
  simpa only [manuscriptPencil_detPolynomial, manuscriptPencil_center, evalQ] using hc

end ManuscriptChain.Real
