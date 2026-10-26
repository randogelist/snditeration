import Zetahyperbolic.Section2.PoleDiagonalization
import Mathlib.LinearAlgebra.Lagrange

/-!
# The actual interpolation basis in Theorem 2.5

Identify the coefficients of the negative-square Lagrange polynomials with
the inverse Vandermonde matrix used by the verified pencil congruence.
-/

noncomputable section
open scoped BigOperators
open Polynomial

namespace ManuscriptChain.PoleDiagonalization

def lagrangePolynomial (p : Real.Parameters) (a : Fin p.h) : ℚ[X] :=
  Lagrange.basis Finset.univ (poleNode p) a

theorem lagrangePolynomial_product (p : Real.Parameters) (a : Fin p.h) :
    lagrangePolynomial p a =
      ∏ b ∈ Finset.univ.erase a,
        C (((poleIndex p b : ℚ)^2 - (poleIndex p a : ℚ)^2)⁻¹) *
          (X + C ((poleIndex p b : ℚ)^2)) := by
  unfold lagrangePolynomial Lagrange.basis Lagrange.basisDivisor poleNode
  congr 1
  funext b
  simp only [sub_neg_eq_add, map_neg, neg_add_eq_sub]

theorem lagrangePolynomial_eval (p : Real.Parameters) (a b : Fin p.h) :
    (lagrangePolynomial p a).eval (poleNode p b) = if a = b then 1 else 0 := by
  classical
  by_cases hab : a = b
  · subst b
    simp [lagrangePolynomial, Lagrange.eval_basis_self
      (poleNode_injective p).injOn (Finset.mem_univ a)]
  · simp [lagrangePolynomial, hab, Lagrange.eval_basis_of_ne hab (Finset.mem_univ b)]

theorem lagrangePolynomial_natDegree (p : Real.Parameters) (a : Fin p.h) :
    (lagrangePolynomial p a).natDegree = p.h - 1 := by
  simpa [lagrangePolynomial] using Lagrange.natDegree_basis
    (poleNode_injective p).injOn (Finset.mem_univ a)

def lagrangeCoefficientMatrix (p : Real.Parameters) : Matrix (Fin p.h) (Fin p.h) ℚ :=
  fun a i => (lagrangePolynomial p a).coeff i.val

theorem lagrangeCoefficientMatrix_mul_vandermonde (p : Real.Parameters) :
    lagrangeCoefficientMatrix p * poleVandermonde p = 1 := by
  classical
  ext a b
  rw [Matrix.mul_apply, Matrix.one_apply]
  change (∑ i : Fin p.h, (lagrangePolynomial p a).coeff i.val *
      poleNode p b ^ i.val) = if a = b then 1 else 0
  rw [Fin.sum_univ_eq_sum_range
    (fun i : ℕ => (lagrangePolynomial p a).coeff i * poleNode p b ^ i) p.h]
  have hd : (lagrangePolynomial p a).natDegree < p.h := by
    rw [lagrangePolynomial_natDegree]
    have := a.isLt
    omega
  rw [← Polynomial.eval_eq_sum_range' hd]
  simpa [Matrix.one_apply] using lagrangePolynomial_eval p a b

theorem lagrangeCoefficientMatrix_eq_inverse (p : Real.Parameters) :
    lagrangeCoefficientMatrix p = (poleVandermonde p)⁻¹ :=
  (Matrix.inv_eq_left_inv (lagrangeCoefficientMatrix_mul_vandermonde p)).symm

theorem lagrangePolynomial_coeff (p : Real.Parameters) (a i : Fin p.h) :
    (lagrangePolynomial p a).coeff i.val = (poleVandermonde p)⁻¹ a i := by
  exact congrFun (congrFun (lagrangeCoefficientMatrix_eq_inverse p) a) i

theorem lagrange_changeBasisPencil (p : Real.Parameters) :
    BasisInvariance.changeBasisPencil (Real.pencil p)
      (lagrangeCoefficientMatrix p) (lagrangeCoefficientMatrix p) =
        poleDiagonalPencil p := by
  rw [lagrangeCoefficientMatrix_eq_inverse]
  rfl

end ManuscriptChain.PoleDiagonalization
