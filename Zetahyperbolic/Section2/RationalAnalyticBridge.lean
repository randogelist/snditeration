import Zetahyperbolic.Section2.PolynomialDerivative

/-!
# Lemma 2.3 on the actual full rational-function domain

The real analytic realization is defined from the unique polynomial-plus-pole
coordinates of an actual RatFunc domain element. Its normalized even derivative
is the same intrinsic coefficient that appears in the existing rational
finite-difference theorem.

The direct rewrite to Mathlib's totalized RatFunc.eval at every real point
is an independent compatibility lemma and is NOT silently assumed here.
-/

noncomputable section
open Polynomial

namespace ManuscriptChain.Tau

/-- Canonical real analytic evaluation of the unique rational-function
coordinates. For zero regular residue, it is analytic at the origin. -/
def analyticRealization (f : RationalDomain) (x : ℝ) : ℝ :=
  let d := (SimplePole.coordinates integerNode integerNode_injective).symm f
  coordinateReal d.1 d.2 x

/-- The exact regularity condition on unique simple-pole coordinates.
There is no pole at the origin. -/
def RegularAtOrigin (f : RationalDomain) : Prop :=
  ((SimplePole.coordinates integerNode integerNode_injective).symm f).2 0 = 0

/-- The canonical coefficient of every regular rational-domain element equals
the normalized actual analytic derivative at zero. -/
theorem normalized_derivative_rationalDomain
    (k : ℕ) (f : RationalDomain) (hf : RegularAtOrigin f) :
    (partialFractionCoefficient (2*k) f : ℝ) =
      iteratedDeriv (2*k) (analyticRealization f) 0 /
        ((2*k).factorial : ℝ) := by
  let E := SimplePole.coordinates integerNode integerNode_injective
  let d := E.symm f
  have hd : d.2 0 = 0 := hf
  have h := rationalDomain_coefficient_eq_coordinate_derivative k d.1 d.2 hd
  have he : SimplePole.ofData integerNode d = f := by
    exact E.apply_symm_apply f
  rw [he] at h
  exact h

/-- Actual τ finite difference of every regular rational-domain element,
expressed through its normalized analytic derivative at the origin. -/
theorem rationalFunctional_difference_analytic
    (k : ℕ) (hk : 1 ≤ k) (f : RationalDomain)
    (hf : RegularAtOrigin f) (x : ℝ) :
    (((rationalFunctional k (rationalDifference f)).map
      (algebraMap ℚ ℝ)).eval x) =
      iteratedDeriv (2*k) (analyticRealization f) 0 /
        ((2*k).factorial : ℝ) := by
  rw [rationalFunctional_difference k hk]
  simp only [Polynomial.map_C, Polynomial.eval_C]
  exact normalized_derivative_rationalDomain k f hf

end ManuscriptChain.Tau
