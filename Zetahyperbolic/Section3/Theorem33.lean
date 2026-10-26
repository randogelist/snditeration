import Zetahyperbolic.Section3.ActualMixedMinors
import Zetahyperbolic.Section3.SymmetricSquareRoot
import Zetahyperbolic.Section3.SpectralInertia
import Zetahyperbolic.Section3.PoleSigns

/-! Exact assembly of the three clauses of manuscript Theorem 3.3.
The determinacy clause refers to the printed measure, not a surrogate moment
sequence. The minor indices are arbitrary increasing row and column selections.
The growth proof even removes the printed auxiliary condition 2mN ≤ K. -/
noncomputable section
open MeasureTheory

namespace ManuscriptChain

theorem theorem_3_3_total_positivity_determinacy_signature
    (p : Real.Parameters) (hp : Real.Admissible p) :
    (∀ ν : Measure ℝ, (∀ᵐ t ∂ν, 0 ≤ t) →
      (∀ n : ℕ, Integrable (fun t : ℝ => t^n) ν) →
      (∀ n : ℕ, (∫ t : ℝ, t^n ∂PrintedMomentMeasure.printedMeasure p 1) =
        ∫ t : ℝ, t^n ∂ν) → PrintedMomentMeasure.printedMeasure p 1 = ν) ∧
    (∀ (n : ℕ) (rows cols : Fin n → Fin p.h),
      StrictMono rows → StrictMono cols →
      0 < Matrix.det ((Real.gram p (Real.zeta p.weight)).submatrix rows cols)) ∧
    ({i | 0 < Spectral.actualEigenvalues (Real.manuscriptPencil p) i}.ncard =
      (if Even p.N then (p.h + 1) / 2 else p.h / 2) ∧
     {i | Spectral.actualEigenvalues (Real.manuscriptPencil p) i < 0}.ncard =
      (if Even p.N then p.h / 2 else (p.h + 1) / 2)) := by
  refine ⟨?_, ?_, SpectralInertia.actual_inertia_formula p hp⟩
  · intro ν hν iν hm
    exact PrintedMomentMeasure.printed_stieltjes_measure_unique p hp ν hν iν hm
  · intro n rows cols hr hc
    exact GRAM_ARBITRARY_MIXED_MINOR_POSITIVE p hp rows cols hr hc

theorem theorem_3_3_weight_five_leading_sign (n : ℕ) :
    sign (BasisInvariance.primitiveNormalization
      (Real.delta (PoleDiagonalization.weightFiveParameters n))
      (PoleDiagonalization.delta_ne_zero _)).polynomial.leadingCoeff =
      (-1 : SignType) ^ (n * (n - 1) / 2) :=
  BasisInvariance.weightFive_primitive_leadingCoeff_sign n

end ManuscriptChain
