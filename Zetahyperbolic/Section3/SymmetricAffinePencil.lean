import Mathlib

/-!
# Symmetric affine matrix-pencil geometry

Generic finite-dimensional foundation for the manuscript's Section 3.
Positive definiteness is an explicit input, not an assumed conclusion.
-/

noncomputable section
open scoped BigOperators
open Polynomial

namespace ManuscriptChain.Spectral

structure SymmetricAffinePencil (n : ℕ) where
  center : ℝ
  base : Matrix (Fin n) (Fin n) ℝ
  direction : Matrix (Fin n) (Fin n) ℝ
  base_symmetric : base.IsSymm
  direction_symmetric : direction.IsSymm

namespace SymmetricAffinePencil

variable {n : ℕ} (p : SymmetricAffinePencil n)

def matrixAt (x : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  p.base + (x - p.center) • p.direction

def polynomialMatrix : Matrix (Fin n) (Fin n) ℝ[X] :=
  fun i j => C (p.base i j) + (X - C p.center) * C (p.direction i j)

def detPolynomial : ℝ[X] := Matrix.det p.polynomialMatrix

def detValue (x : ℝ) : ℝ := Matrix.det (p.matrixAt x)

def BasePositive : Prop := p.base.PosDef

@[simp] theorem matrixAt_center : p.matrixAt p.center = p.base := by
  simp [matrixAt]

theorem eval_detPolynomial (x : ℝ) : p.detPolynomial.eval x = p.detValue x := by
  unfold detPolynomial detValue
  change (Polynomial.evalRingHom x) (Matrix.det p.polynomialMatrix) = _
  rw [(Polynomial.evalRingHom x).map_det]
  congr 1
  ext i j
  simp [polynomialMatrix, matrixAt]

@[simp] theorem eval_detPolynomial_center :
    p.detPolynomial.eval p.center = Matrix.det p.base := by
  rw [p.eval_detPolynomial]
  simp [detValue]

theorem base_det_ne_zero_of_positive (h : p.BasePositive) : Matrix.det p.base ≠ 0 := by
  exact ((Matrix.isUnit_iff_isUnit_det p.base).mp
    (show p.base.PosDef from h).isUnit).ne_zero

theorem center_nonvanishing_of_positive (h : p.BasePositive) :
    p.detPolynomial.eval p.center ≠ 0 := by
  rw [p.eval_detPolynomial_center]
  exact p.base_det_ne_zero_of_positive h

end SymmetricAffinePencil
end ManuscriptChain.Spectral
