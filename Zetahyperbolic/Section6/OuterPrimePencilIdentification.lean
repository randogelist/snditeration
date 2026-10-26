import Zetahyperbolic.Section6.OuterPrimePadicBlock
import Zetahyperbolic.Section6.OuterPrimeRationalBlock
import Zetahyperbolic.Section5.DualAffineAlgebra

/-! The local blocks are the actual monomial affine pencil entries. In
particular the lower off-diagonal entry uses the proved symmetry of the
actual rational divided difference, not a supplied matrix assumption. -/

noncomputable section
open scoped Matrix
namespace ManuscriptChain.Beukers

theorem rationalLocalMatrix_eq_monomial_pencil (p r : ℕ) (X : ℚ) :
    rationalLocalMatrix p r X =
      fun i j : Fin 2 =>
        Real.dualConstant 7 (r+i.val*p) (r+j.val*p) +
          if i = j then X else 0 := by
  have hs := DualAlgebra.dualConstant_swap 7 (r+p) r
  have hd (n : ℕ) : Real.dualConstant 7 n n = -Real.harmonic 7 n := by
    simp [Real.dualConstant]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rationalLocalMatrix, hs, hd] <;> ring

theorem padicLocalMatrix_eq_monomial_pencil (p r : ℕ) [Fact p.Prime]
    (X : ℚ_[p]) :
    padicLocalMatrix p r X =
      fun i j : Fin 2 =>
        (Real.dualConstant 7 (r+i.val*p) (r+j.val*p) : ℚ_[p]) +
          if i = j then X else 0 := by
  have hs := DualAlgebra.dualConstant_swap 7 (r+p) r
  have hd (n : ℕ) : Real.dualConstant 7 n n = -Real.harmonic 7 n := by
    simp [Real.dualConstant]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [padicLocalMatrix, hs, hd] <;> push_cast <;> ring

end ManuscriptChain.Beukers
