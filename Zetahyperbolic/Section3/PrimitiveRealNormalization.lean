import Zetahyperbolic.Section3.PrimitivePolynomial
import Zetahyperbolic.Section4.Transfer

/-! Identify the destination's actual primitive normalization on real inputs.
This is the same normalization used in the certified integer-polynomial transport,
not a second abstract polynomial or a supplied factorization hypothesis. -/

noncomputable section
open Polynomial

namespace ManuscriptChain

theorem primitivePolynomial_real_eval (p : Real.Parameters) (x : ℝ) :
    RealTransfer.evalReal (primitivePolynomial p) x =
      ((primitive p).scale : ℝ) * Real.evalQ (Real.delta p) x := by
  have he := congrArg (Polynomial.eval₂ (Rat.castHom ℝ) x) (primitive p).identity
  have hc : (Rat.castHom ℝ).comp (Int.castRingHom ℚ) = Int.castRingHom ℝ := by
    ext z
    simp
  simpa [Polynomial.eval₂_map, hc, primitivePolynomial,
    RealTransfer.evalReal, Real.evalQ, Real.realPolynomial,
    Polynomial.eval_map] using he

end ManuscriptChain

#print axioms ManuscriptChain.primitivePolynomial_real_eval
