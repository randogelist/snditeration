import Zetahyperbolic.Section3.MomentPositivity

/-!
# Positive moment realization of the actual odd-zeta pencil

Any nonzero atomless measure that realizes each entry of the actual
rational pencil as an integrable monomial moment supplies its Gram
positivity. The measure and identities are explicit inputs here.
-/

noncomputable section
open MeasureTheory Matrix Polynomial

namespace ManuscriptChain.Real

structure PositiveMomentRealization (p : Parameters) where
  measure : Measure ℝ
  nullSingleton : NullSingletonClass measure
  nonzero : measure ≠ 0
  integrable_moments : ∀ i j : Fin p.h,
    Integrable (fun x : ℝ => x ^ (i.val + j.val)) measure
  moment_identity : ∀ i j : Fin p.h,
    gram p (zeta p.weight) i j = ∫ x, x ^ (i.val + j.val) ∂measure

theorem PositiveMomentRealization.gram_posDef {p : Parameters}
    (r : PositiveMomentRealization p) : (gram p (zeta p.weight)).PosDef := by
  let : NullSingletonClass r.measure := r.nullSingleton
  have hmatrix : gram p (zeta p.weight) = Moments.momentMatrix r.measure p.h := by
    ext i j
    exact r.moment_identity i j
  rw [hmatrix]
  exact Moments.momentMatrix_posDef r.nonzero r.integrable_moments

end ManuscriptChain.Real
