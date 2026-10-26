import Zetahyperbolic.Section6.MellinFiberPolynomial
import Zetahyperbolic.Section6.MellinJacobian
import Zetahyperbolic.Section6.OuterPrimePadicReduction

noncomputable section
namespace ManuscriptChain.Beukers

/-- The corrected local clause of 6.1. The entrywise congruence is for the
actual affine block; all p-integral evaluations and primitive vectors are
quantified. The printed nonzero-vector version is separately refuted. -/
theorem theorem_6_1_corrected_local (p K r : ℕ) [Fact p.Prime]
    (hp11 : 11 ≤ p) (_hK : K < 2*p) (hr : r < p) (_hrK : r+p ≤ K)
    (X : ℚ_[p]) (hX : ‖X‖ ≤ 1) :
    (∀ i j, ‖(p : ℚ_[p])^7 * padicLocalMatrix p r X i j -
      padicLeadingMatrix p i j‖ < 1) ∧
    (localLeadingMatrix p).det ≠ 0 ∧
    ‖X - (Real.harmonic 7 (r+p) : ℚ_[p])‖ = (p : ℝ)^7 ∧
    ‖(Real.dualConstant 7 r (r+p) : ℚ_[p])‖ = (p : ℝ)^7 ∧
    ‖(padicLocalMatrix p r X).det‖ = (p : ℝ)^14 ∧
    (∀ c : Fin 2 → ℚ_[p], (∀ i, ‖c i‖ ≤ 1) → (∃ i, ‖c i‖ = 1) →
      ∃ i, ‖(padicLocalMatrix p r X).mulVec c i‖ = (p : ℝ)^7) := by
  exact ⟨padicLocalMatrix_scaled_reduction p r hp11 hr X hX,
    localLeadingMatrix_det_ne_zero p hp11,
    padicLocalMatrix_high_norm p r hr X hX,
    padicLocalMatrix_offdiagonal_norm p r hp11 hr,
    padicLocalMatrix_det_norm p r hp11 hr X hX,
    fun c hc hp => padicLocalMatrix_primitive_pole p r hp11 hr X hX c hc hp⟩

end ManuscriptChain.Beukers
