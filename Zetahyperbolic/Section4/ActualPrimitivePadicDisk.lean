import Zetahyperbolic.Section3.PrimitivePolynomial
import Zetahyperbolic.Section4.ComplexPadicDisk

/-!
# Proposition 4.3: actual manuscript polynomial

The exact ℂ_p disk theorem is proved below for arbitrary integer polynomials,
then specialized to the primitive Hankel polynomial of Definition (2.9).

There is no assertion that the selected p-adic center is a p-adic zeta value,
or that its evaluation is nonzero for every original parameter family.
Such arithmetic center estimates are separate mathematical obligations.
-/

noncomputable section
open Polynomial

namespace ManuscriptChain

/-- Printed Proposition 4.3, with the exact norm statement over ℂ_p. -/
theorem proposition_4_3_complex_padic_disk
    {q : ℕ} [Fact q.Prime]
    (Q : ℤ[X]) (ξ : ℤ_[q]) (α : ℂ_[q])
    (hQ : (Q.map (Int.castRingHom (ℤ_[q]))).eval ξ ≠ 0)
    (hα : ‖α - ((ξ : ℚ_[q]) : ℂ_[q])‖ <
      ‖(((Q.map (Int.castRingHom (ℤ_[q]))).eval ξ : ℤ_[q]) : ℚ_[q])‖) :
    ‖(((Q.map (Int.castRingHom (ℤ_[q]))).map
      (PadicInt.Coe.ringHom)).map
      (algebraMap ℚ_[q] ℂ_[q])).eval α‖ =
      ‖(((Q.map (Int.castRingHom (ℤ_[q]))).eval ξ : ℤ_[q]) : ℚ_[q])‖ ∧
    (((Q.map (Int.castRingHom (ℤ_[q]))).map
      (PadicInt.Coe.ringHom)).map
      (algebraMap ℚ_[q] ℂ_[q])).eval α ≠ 0 :=
  PaperAdvances.Proposition4_3_ComplexPadicDisk.PROPOSITION_4_3_INTEGER_COMPLEX_PADIC
    Q ξ α hQ hα

/-- The actual primitive manuscript polynomial inherits the disk theorem.
The exact center nonvanishing is deliberately an explicit hypothesis. -/
theorem primitivePolynomial_complex_padic_disk
    (params : Real.Parameters) {q : ℕ} [Fact q.Prime]
    (ξ : ℤ_[q]) (α : ℂ_[q])
    (hQ : ((primitivePolynomial params).map (Int.castRingHom (ℤ_[q]))).eval ξ ≠ 0)
    (hα : ‖α - ((ξ : ℚ_[q]) : ℂ_[q])‖ <
      ‖((((primitivePolynomial params).map (Int.castRingHom (ℤ_[q]))).eval ξ :
        ℤ_[q]) : ℚ_[q])‖) :
    ‖((((primitivePolynomial params).map (Int.castRingHom (ℤ_[q]))).map
      (PadicInt.Coe.ringHom)).map (algebraMap ℚ_[q] ℂ_[q])).eval α‖ =
      ‖((((primitivePolynomial params).map (Int.castRingHom (ℤ_[q]))).eval ξ :
        ℤ_[q]) : ℚ_[q])‖ ∧
    ((((primitivePolynomial params).map (Int.castRingHom (ℤ_[q]))).map
      (PadicInt.Coe.ringHom)).map (algebraMap ℚ_[q] ℂ_[q])).eval α ≠ 0 :=
  proposition_4_3_complex_padic_disk (primitivePolynomial params) ξ α hQ hα

end ManuscriptChain
