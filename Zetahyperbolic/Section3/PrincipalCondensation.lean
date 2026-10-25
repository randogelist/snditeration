import Zetahyperbolic.Section3.DodgsonCondensation
import Zetahyperbolic.Section3.PrincipalPencils
import Mathlib.Tactic.FinCases

/-!
# Theorem 3.4(2): the actual principal-pencil condensation law

The core may be singular at the root under consideration. Only the polynomial
core determinant must be nonzero, which follows from positive definiteness at
the zeta center. The selection formulation covers all leading principal blocks.
-/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix Polynomial

namespace ManuscriptChain.Dodgson

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Retain the core and one of the two final indices. -/
def keep (j : Fin 2) : n ⊕ Unit → n ⊕ Fin 2 := Sum.map id (fun _ => j)

/-- Delete the two final rows and columns. -/
def core {R : Type*} (M : Matrix (n ⊕ Fin 2) (n ⊕ Fin 2) R) : Matrix n n R :=
  M.submatrix Sum.inl Sum.inl

/-- Symmetric polynomial condensation for arbitrary finite order. -/
theorem polynomial_condensation
    (M : Matrix (n ⊕ Fin 2) (n ⊕ Fin 2) ℝ[X])
    (hM : M.IsSymm) (hdet : (core M).det ≠ 0) :
    M.det * (core M).det =
      (M.submatrix (keep 0) (keep 0)).det *
        (M.submatrix (keep 1) (keep 1)).det -
          (M.submatrix (keep 0) (keep 1)).det ^ 2 := by
  let A := core M
  let u : n → ℝ[X] := fun i => M (Sum.inl i) (Sum.inr 0)
  let v : n → ℝ[X] := fun i => M (Sum.inl i) (Sum.inr 1)
  let a := M (Sum.inr 0) (Sum.inr 0)
  let b := M (Sum.inr 0) (Sum.inr 1)
  let c := M (Sum.inr 1) (Sum.inr 1)
  have hA : A.IsSymm := hM.submatrix Sum.inl
  have hf : Matrix.fromBlocks A (fun i j => if j = 0 then u i else v i)
      (fun i j => if i = 0 then u j else v j) !![a, b; b, c] = M := by
    ext (i | i) (j | j)
    · rfl
    · fin_cases j <;> simp [A, u, v, Matrix.fromBlocks]
    · fin_cases i <;> simpa [A, u, v, Matrix.fromBlocks] using
        (hM.apply (Sum.inr _) (Sum.inl j))
    · fin_cases i <;> fin_cases j <;>
        simp [a, b, c, Matrix.fromBlocks, hM.apply]
  have hb (i j : Fin 2) :
      border A (fun k => M (Sum.inl k) (Sum.inr j))
        (fun k => M (Sum.inl k) (Sum.inr i)) (M (Sum.inr i) (Sum.inr j)) =
        M.submatrix (keep i) (keep j) := by
    ext (k | k) (l | l)
    · rfl
    · rfl
    · exact hM.apply _ _
    · rfl
  have h := polynomial_symmetric_block_condensation A hA hdet u v a b c
  rw [hf, hb 0 0, hb 1 1, hb 0 1] at h
  exact h

/-- At a root of the penultimate principal determinant the product is the
negative square of the off-diagonal minor. -/
theorem polynomial_condensation_at_root
    (M : Matrix (n ⊕ Fin 2) (n ⊕ Fin 2) ℝ[X])
    (hM : M.IsSymm) (hdet : (core M).det ≠ 0) (x : ℝ)
    (hx : (M.submatrix (keep 0) (keep 0)).det.eval x = 0) :
    M.det.eval x * (core M).det.eval x =
      -((M.submatrix (keep 0) (keep 1)).det.eval x)^2 := by
  have h := congrArg (Polynomial.eval x) (polynomial_condensation M hM hdet)
  simpa [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_pow, hx] using h

/-- The actual selected manuscript polynomial matrix, with real coefficients. -/
def actualMatrix (p : Real.Parameters) (choose : n ⊕ Fin 2 → Fin p.h) :
    Matrix (n ⊕ Fin 2) (n ⊕ Fin 2) ℝ[X] :=
  (Real.manuscriptPencil p).polynomialMatrix.submatrix choose choose

theorem actualMatrix_symmetric (p : Real.Parameters)
    (choose : n ⊕ Fin 2 → Fin p.h) : (actualMatrix p choose).IsSymm := by
  apply Matrix.IsSymm.submatrix
  apply Matrix.IsSymm.ext
  intro i j
  simp only [Spectral.SymmetricAffinePencil.polynomialMatrix, Matrix.add_apply,
    Matrix.map_apply, Matrix.smul_apply]
  rw [(Real.manuscriptPencil p).base_symmetric.apply,
    (Real.manuscriptPencil p).direction_symmetric.apply]

/-- Evaluation agrees with the actual principal Hankel matrix. -/
theorem actualMatrix_eval (p : Real.Parameters) (choose : n ⊕ Fin 2 → Fin p.h)
    (x : ℝ) :
    (actualMatrix p choose).map (Polynomial.evalRingHom x) =
      (Real.gram p x).submatrix choose choose := by
  ext i j
  change ((Real.manuscriptPencil p).polynomialMatrix (choose i) (choose j)).eval x = _
  change ((Real.manuscriptPencil p).base (choose i) (choose j) +
    (x - (Real.manuscriptPencil p).center) *
      (Real.manuscriptPencil p).direction (choose i) (choose j)) = _
  change ((Real.manuscriptPencil p).matrixAt x) (choose i) (choose j) = _
  rw [Real.manuscriptPencil_matrixAt]

theorem actual_core_det_ne_zero (p : Real.Parameters) (hp : Real.Admissible p)
    (choose : n ⊕ Fin 2 → Fin p.h) (hchoose : Function.Injective choose) :
    (core (actualMatrix p choose)).det ≠ 0 := by
  intro hz
  have hpos := (GRAM_POSITIVE p hp).submatrix (hchoose.comp Sum.inl_injective)
  have he := congrArg (Polynomial.eval (Real.zeta p.weight)) hz
  rw [Polynomial.eval_zero] at he
  have heq : (core (actualMatrix p choose)).det.eval (Real.zeta p.weight) =
      ((Real.gram p (Real.zeta p.weight)).submatrix
        (choose ∘ Sum.inl) (choose ∘ Sum.inl)).det := by
    rw [(Polynomial.evalRingHom _).map_det]
    congr 1
    exact congrArg (fun M => M.submatrix Sum.inl Sum.inl)
      (actualMatrix_eval p choose (Real.zeta p.weight))
  rw [heq] at he
  exact (ne_of_gt hpos.det_pos) he

/-- Arbitrary-order actual manuscript Dodgson identity, as a polynomial identity. -/
theorem actual_polynomial_condensation (p : Real.Parameters) (hp : Real.Admissible p)
    (choose : n ⊕ Fin 2 → Fin p.h) (hchoose : Function.Injective choose) :
    (actualMatrix p choose).det * (core (actualMatrix p choose)).det =
      ((actualMatrix p choose).submatrix (keep 0) (keep 0)).det *
        ((actualMatrix p choose).submatrix (keep 1) (keep 1)).det -
          ((actualMatrix p choose).submatrix (keep 0) (keep 1)).det ^ 2 :=
  polynomial_condensation _ (actualMatrix_symmetric p choose)
    (actual_core_det_ne_zero p hp choose hchoose)

/-- Theorem 3.4(2), including the asserted sign at every penultimate root. -/
theorem actual_condensation_at_root (p : Real.Parameters) (hp : Real.Admissible p)
    (choose : n ⊕ Fin 2 → Fin p.h) (hchoose : Function.Injective choose) (x : ℝ)
    (hx : ((actualMatrix p choose).submatrix (keep 0) (keep 0)).det.eval x = 0) :
    (actualMatrix p choose).det.eval x * (core (actualMatrix p choose)).det.eval x =
      -(((actualMatrix p choose).submatrix (keep 0) (keep 1)).det.eval x)^2 ∧
    (actualMatrix p choose).det.eval x * (core (actualMatrix p choose)).det.eval x ≤ 0 := by
  have h := polynomial_condensation_at_root _ (actualMatrix_symmetric p choose)
    (actual_core_det_ne_zero p hp choose hchoose) x hx
  exact ⟨h, by rw [h]; exact neg_nonpos.mpr (sq_nonneg _)⟩

end ManuscriptChain.Dodgson
