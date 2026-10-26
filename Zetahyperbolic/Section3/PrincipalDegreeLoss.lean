import Zetahyperbolic.Section3.PrincipalPencils

/-!
# Actual principal degree loss in Theorem 3.4

The literal statement indexes r finite roots of every r-by-r principal pencil.
That needs correction: even with admissible actual manuscript parameters the
first principal polynomial can be a nonzero constant. Eigenvalue interlacing
still makes sense, with zero slopes retained; reciprocal root statements must
exclude zero slopes or allow a point at infinity.
-/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix Polynomial
open scoped BigOperators

namespace ManuscriptChain.PrincipalDegreeLoss

def exampleParams : Real.Parameters := ⟨1, 1, 1, 5⟩

theorem example_admissible : Real.Admissible exampleParams := by
  constructor <;> decide

def first : Fin 1 → Fin exampleParams.h := fun _ => ⟨0, by decide⟩

theorem first_injective : Function.Injective first := by
  intro i j h
  exact Subsingleton.elim i j

/-- Exact rational cancellation in the actual slope moment. -/
theorem first_slope_zero : Real.entryM exampleParams 0 0 = 0 := by
  have hI : Finset.Icc 2 5 = {2, 3, 4, 5} := by decide
  norm_num [Real.entryM, Real.residue, Real.numerator, Real.D, Real.tailD,
    exampleParams, hI, Finset.prod_range_succ, Polynomial.derivative_mul]

/-- The selected actual direction has rank zero. -/
theorem principal_direction_zero :
    (Principal.manuscriptPrincipalPencil exampleParams first).direction = 0 := by
  ext i j
  change (Real.entryM exampleParams 0 0 : ℝ) = 0
  rw [first_slope_zero, Rat.cast_zero]

/-- The first actual principal determinant is the positive constant at the center. -/
theorem principal_polynomial_constant :
    (Principal.manuscriptPrincipalPencil exampleParams first).detPolynomial =
      C (Principal.manuscriptPrincipalPencil exampleParams first).base.det := by
  apply Polynomial.funext
  intro x
  rw [Spectral.SymmetricAffinePencil.eval_detPolynomial,
    Spectral.SymmetricAffinePencil.detValue,
    Spectral.SymmetricAffinePencil.matrixAt, principal_direction_zero]
  simp

/-- There are no finite roots, despite the positive one-by-one principal size. -/
theorem first_principal_has_no_complex_roots (z : ℂ) :
    Polynomial.eval₂ (algebraMap ℝ ℂ) z
      (Principal.manuscriptPrincipalPencil exampleParams first).detPolynomial ≠ 0 := by
  rw [principal_polynomial_constant, Polynomial.eval₂_C]
  exact Complex.ofReal_ne_zero.mpr (ne_of_gt
    (Principal.principal_base_posDef exampleParams example_admissible first first_injective).det_pos)

/-- Exact failure of the claim that every positive-size principal polynomial has a root. -/
theorem literal_all_principal_roots_claim_false :
    ¬ ∀ (p : Real.Parameters), Real.Admissible p →
      ∀ (choose : Fin 1 → Fin p.h), Function.Injective choose →
        ∃ z : ℂ, Polynomial.eval₂ (algebraMap ℝ ℂ) z
          (Principal.manuscriptPrincipalPencil p choose).detPolynomial = 0 := by
  intro h
  obtain ⟨z, hz⟩ := h exampleParams example_admissible first first_injective
  exact first_principal_has_no_complex_roots z hz

end ManuscriptChain.PrincipalDegreeLoss
