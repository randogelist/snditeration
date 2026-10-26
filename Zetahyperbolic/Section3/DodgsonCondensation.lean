import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.FieldTheory.RatFunc.Basic

/-!
# Arbitrary-order symmetric Dodgson condensation

The block identity is first proved over a field by Schur complementation. Its
polynomial version uses the rational-function field, so evaluation never requires
invertibility of the central minor at the chosen point.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section
open Matrix Polynomial
open scoped BigOperators

namespace ManuscriptChain.Dodgson

variable {𝕜 : Type*} [CommRing 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- Add one row and one column to a square matrix. -/
def border (A : Matrix n n 𝕜) (u v : n → 𝕜) (a : 𝕜) :
    Matrix (n ⊕ Unit) (n ⊕ Unit) 𝕜 :=
  Matrix.fromBlocks A (fun i _ => u i) (fun _ i => v i) (fun _ _ => a)

theorem det_border (A : Matrix n n 𝕜) [Invertible A]
    (u v : n → 𝕜) (a : 𝕜) :
    (border A u v a).det = A.det * (a - v ⬝ᵥ (⅟A *ᵥ u)) := by
  rw [border, Matrix.det_fromBlocks₁₁]
  congr 1
  rw [Matrix.det_unique, Matrix.mul_assoc]
  rfl

/-- Desnanot--Jacobi for two rows and columns bordering an invertible block. -/
theorem block_condensation (A : Matrix n n 𝕜) [Invertible A]
    (B : Matrix n (Fin 2) 𝕜) (C : Matrix (Fin 2) n 𝕜)
    (D : Matrix (Fin 2) (Fin 2) 𝕜) :
    (Matrix.fromBlocks A B C D).det * A.det =
      (border A (fun i => B i 0) (C 0) (D 0 0)).det *
        (border A (fun i => B i 1) (C 1) (D 1 1)).det -
      (border A (fun i => B i 1) (C 0) (D 0 1)).det *
        (border A (fun i => B i 0) (C 1) (D 1 0)).det := by
  rw [Matrix.det_fromBlocks₁₁, Matrix.det_fin_two]
  simp_rw [det_border]
  have h (i j : Fin 2) : (C * ⅟A * B) i j = C i ⬝ᵥ (⅟A *ᵥ fun k => B k j) := by
    rw [Matrix.mul_assoc]
    rfl
  simp only [Matrix.sub_apply, h]
  ring

/-- Symmetric form, with the two off-diagonal bordered minors equal. -/
theorem symmetric_block_condensation (A : Matrix n n 𝕜) [Invertible A]
    (hA : A.IsSymm) (u v : n → 𝕜) (a b c : 𝕜) :
    (Matrix.fromBlocks A (fun i j => if j = 0 then u i else v i)
      (fun i j => if i = 0 then u j else v j) !![a, b; b, c]).det * A.det =
      (border A u u a).det * (border A v v c).det -
        (border A v u b).det ^ 2 := by
  have heq : (border A u v b).det = (border A v u b).det := by
    rw [← Matrix.det_transpose]
    congr 1
    ext (i | i) (j | j) <;> simp [border, Matrix.transpose_apply, Matrix.fromBlocks, hA.apply]
  have h := block_condensation A (fun i j => if j = 0 then u i else v i)
    (fun i j => if i = 0 then u j else v j) !![a, b; b, c]
  norm_num at h
  simpa only [heq, pow_two] using h

/-- Mapping coefficients commutes with bordering. -/
theorem map_border {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (A : Matrix n n R) (u v : n → R) (a : R) :
    (border A u v a).map f = border (A.map f) (fun i => f (u i))
      (fun i => f (v i)) (f a) := by
  ext (i | i) (j | j) <;> rfl

/-- Polynomial Dodgson identity. The central determinant need only be a nonzero
polynomial, not nonzero at the eventual evaluation point. -/
theorem polynomial_symmetric_block_condensation
    (A : Matrix n n ℝ[X]) (hA : A.IsSymm) (hdet : A.det ≠ 0)
    (u v : n → ℝ[X]) (a b c : ℝ[X]) :
    (Matrix.fromBlocks A (fun (i : n) (j : Fin 2) => if j = 0 then u i else v i)
      (fun i j => if i = 0 then u j else v j) !![a, b; b, c]).det * A.det =
      (border A u u a).det * (border A v v c).det -
        (border A v u b).det ^ 2 := by
  let f : ℝ[X] →+* RatFunc ℝ := algebraMap ℝ[X] (RatFunc ℝ)
  have hinj : Function.Injective f := RatFunc.algebraMap_injective ℝ
  have hd : (A.map f).det ≠ 0 := by
    change (f.mapMatrix A).det ≠ 0
    rw [← f.map_det]
    exact fun h => hdet (hinj (by simpa using h))
  letI : Invertible (A.map f) := Matrix.invertibleOfIsUnitDet _
    (isUnit_iff_ne_zero.mpr hd)
  apply hinj
  simp only [map_mul, map_sub, map_pow, f.map_det]
  simp only [show ∀ (M : Matrix n n ℝ[X]) (x y : n → ℝ[X]) (d : ℝ[X]),
    f.mapMatrix (border M x y d) = border (M.map f) (fun i => f (x i))
      (fun i => f (y i)) (f d) from fun M x y d => map_border f M x y d]
  have hmap : f.mapMatrix
      (Matrix.fromBlocks A (fun (i : n) (j : Fin 2) => if j = 0 then u i else v i)
        (fun i j => if i = 0 then u j else v j) !![a, b; b, c]) =
      Matrix.fromBlocks (A.map f)
        (fun (i : n) (j : Fin 2) => if j = 0 then f (u i) else f (v i))
        (fun i j => if i = 0 then f (u j) else f (v j))
        !![f a, f b; f b, f c] := by
    ext (i | i) (j | j)
    · rfl
    · fin_cases j <;> rfl
    · fin_cases i <;> rfl
    · fin_cases i <;> fin_cases j <;> rfl
  rw [hmap]
  exact symmetric_block_condensation _ (hA.map f) _ _ _ _ _

end ManuscriptChain.Dodgson
