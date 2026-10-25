import Zetahyperbolic.Section3.Unconditional

/-!
Transport the exact-degree and real-root conclusions from the rational
determinant to the manuscript's primitive integer polynomial (2.9).
-/

noncomputable section
open Polynomial

namespace ManuscriptChain

def primitive (p : Real.Parameters) :
    BasisInvariance.PrimitiveNormalization (Real.delta p) :=
  BasisInvariance.primitiveNormalization (Real.delta p)
    (PoleDiagonalization.delta_ne_zero p)

def primitivePolynomial (p : Real.Parameters) : ℤ[X] := (primitive p).polynomial

theorem primitivePolynomial_isPrimitive (p : Real.Parameters) :
    (primitivePolynomial p).IsPrimitive := (primitive p).primitive

theorem primitivePolynomial_natDegree (p : Real.Parameters) :
    (primitivePolynomial p).natDegree = p.h := by
  have hd := congrArg Polynomial.natDegree (primitive p).identity
  rw [Polynomial.natDegree_map_eq_of_injective Int.cast_injective,
    Polynomial.natDegree_C_mul (ne_of_gt (primitive p).scale_pos),
    PoleDiagonalization.delta_natDegree] at hd
  exact hd

theorem primitivePolynomial_complex_eval (p : Real.Parameters) (z : ℂ) :
    (primitivePolynomial p).eval₂ (Int.castRingHom ℂ) z =
      ((primitive p).scale : ℂ) * (Real.delta p).eval₂ (Rat.castHom ℂ) z := by
  have he := congrArg (Polynomial.eval₂ (Rat.castHom ℂ) z) (primitive p).identity
  have hc : (Rat.castHom ℂ).comp (Int.castRingHom ℚ) = Int.castRingHom ℂ := by
    ext
    simp
  simpa only [Polynomial.eval₂_map, Polynomial.eval₂_mul, Polynomial.eval₂_C,
    hc] using he

theorem primitivePolynomial_root_iff (p : Real.Parameters) (z : ℂ) :
    (primitivePolynomial p).eval₂ (Int.castRingHom ℂ) z = 0 ↔
      General.ComplexRoot p z := by
  rw [primitivePolynomial_complex_eval]
  have hs : ((primitive p).scale : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (primitive p).scale_pos)
  simp only [mul_eq_zero, hs, false_or]
  rfl

theorem primitivePolynomial_roots_real (p : Real.Parameters) (hp : Real.Admissible p)
    (z : ℂ) (hz : (primitivePolynomial p).eval₂ (Int.castRingHom ℂ) z = 0) :
    z.im = 0 :=
  ROOTS_REAL p hp z ((primitivePolynomial_root_iff p z).mp hz)

theorem primitivePolynomial_exact_zero_free_disk
    (p : Real.Parameters) (hp : Real.Admissible p) :
    ∃ radius : ℝ, 0 < radius ∧
      (∀ z : ℂ, ‖z - (Real.zeta p.weight : ℂ)‖ < radius →
        (primitivePolynomial p).eval₂ (Int.castRingHom ℂ) z ≠ 0) ∧
      (∃ z : ℂ, (primitivePolynomial p).eval₂ (Int.castRingHom ℂ) z = 0 ∧
        ‖z - (Real.zeta p.weight : ℂ)‖ = radius) := by
  obtain ⟨radius, hr, hfree, z, hz, hboundary⟩ := EXACT_ZERO_FREE_DISK p hp
  refine ⟨radius, hr, ?_, z, (primitivePolynomial_root_iff p z).mpr hz, hboundary⟩
  intro w hw hroot
  exact hfree w hw ((primitivePolynomial_root_iff p w).mp hroot)

end ManuscriptChain
