import Zetahyperbolic.Section2.RationalPullback

/-!
# Lemma 2.2 on the full simple-square-pole rational-function domain

The finite coordinate map is identified with the actual rational substitution,
then the polynomial and pole generator identities extend by linearity.
-/

noncomputable section
open scoped BigOperators
open Polynomial

namespace ManuscriptChain.Pullback

def polynomialPullback (k : ℕ) : ℚ[X] →ₗ[ℚ] ℚ[X] :=
  (LinearMap.mulLeft ℚ (X^(2*k+1))).comp substitutionPolynomial.toLinearMap

@[simp] theorem polynomialPullback_apply (k : ℕ) (q : ℚ[X]) :
    polynomialPullback k q = X^(2*k+1) * q.comp (-X^2) := rfl

def dataPullback (k : ℕ) : SimplePole.Data ℕ →ₗ[ℚ] SimplePole.Data ℤ :=
  (LinearMap.inl ℚ ℚ[X] (ℤ →₀ ℚ)).comp ((polynomialPullback k).comp
    (LinearMap.fst ℚ ℚ[X] (ℕ →₀ ℚ))) +
  (Finsupp.linearCombination ℚ (poleData k)).comp
    (LinearMap.snd ℚ ℚ[X] (ℕ →₀ ℚ))

@[simp] lemma dataPullback_polynomial (k : ℕ) (q : ℚ[X]) :
    dataPullback k (q,0) = (polynomialPullback k q,0) := by
  simp [dataPullback]

@[simp] lemma dataPullback_pole (k j : ℕ) :
    dataPullback k (0,Finsupp.single j 1) = poleData k j := by
  simp [dataPullback]

def scaledSubstitution (k : ℕ) : RatFunc ℚ →ₗ[ℚ] RatFunc ℚ :=
  (LinearMap.mulLeft ℚ ((RatFunc.X : RatFunc ℚ)^(2*k+1))).comp substitution.toLinearMap

@[simp] lemma scaledSubstitution_apply (k : ℕ) (f : RatFunc ℚ) :
    scaledSubstitution k f = RatFunc.X^(2*k+1) * substitution f := rfl

lemma dataPullback_realization (k : ℕ) :
    (SimplePole.realize Tau.integerNode).comp (dataPullback k) =
      (scaledSubstitution k).comp (SimplePole.realize Mu.squareNode) := by
  apply LinearMap.prod_ext
  · apply LinearMap.ext
    intro q
    change SimplePole.realize Tau.integerNode (dataPullback k (q,0)) =
      scaledSubstitution k (SimplePole.realize Mu.squareNode (q,0))
    rw [dataPullback_polynomial]
    simp [SimplePole.realize_apply, scaledSubstitution, polynomialPullback_apply,
      substitution_algebraMap]
  · apply Finsupp.lhom_ext
    intro j c
    have hc : Finsupp.single j c = c • Finsupp.single j (1:ℚ) := by simp
    rw [hc, LinearMap.map_smul, LinearMap.map_smul]
    congr 1
    change SimplePole.realize Tau.integerNode (dataPullback k (0,Finsupp.single j 1)) =
      scaledSubstitution k (SimplePole.realize Mu.squareNode (0,Finsupp.single j 1))
    rw [dataPullback_pole, poleData_realization]
    simp [SimplePole.realize_apply, scaledSubstitution_apply, Mu.squareNode,
      sub_eq_add_neg, div_eq_mul_inv, add_comm]

lemma dataPullback_functional (k : ℕ) (hk : 1 ≤ k) :
    (Tau.rationalFunctional k).comp
        ((SimplePole.realize Tau.integerNode).rangeRestrict.comp (dataPullback k)) =
      (Mu.rationalFunctional k).comp (SimplePole.realize Mu.squareNode).rangeRestrict := by
  apply LinearMap.prod_ext
  · apply LinearMap.ext
    intro q
    change Tau.rationalFunctional k (SimplePole.ofData Tau.integerNode (dataPullback k (q,0))) =
      Mu.rationalFunctional k (SimplePole.ofData Mu.squareNode (q,0))
    rw [dataPullback_polynomial, Tau.rationalFunctional_polynomial,
      Mu.rationalFunctional_polynomial, polynomialPullback_apply,
      Tau.pullback_identity_polynomial k hk]
  · apply Finsupp.lhom_ext
    intro j c
    have hc : Finsupp.single j c = c • Finsupp.single j (1:ℚ) := by simp
    rw [hc, LinearMap.map_smul, LinearMap.map_smul]
    congr 1
    change Tau.rationalFunctional k
        (SimplePole.ofData Tau.integerNode (dataPullback k (0,Finsupp.single j 1))) =
      Mu.rationalFunctional k (SimplePole.ofData Mu.squareNode (0,Finsupp.single j 1))
    rw [dataPullback_pole, tau_poleData k j hk, Mu.rationalFunctional_pole,
      Tau.muPolePoly_eq_existing]

def rationalPullback (k : ℕ) : Mu.RationalDomain →ₗ[ℚ] Tau.RationalDomain :=
  ((SimplePole.realize Tau.integerNode).rangeRestrict.comp (dataPullback k)).comp
    (SimplePole.coordinates Mu.squareNode Mu.squareNode_injective).symm.toLinearMap

/-- The output is precisely `X^(2k+1) R(-X²)` as an actual rational function. -/
theorem rationalPullback_coe (k : ℕ) (f : Mu.RationalDomain) :
    (rationalPullback k f : RatFunc ℚ) =
      RatFunc.X^(2*k+1) * substitution (f : RatFunc ℚ) := by
  let d := (SimplePole.coordinates Mu.squareNode Mu.squareNode_injective).symm f
  have hd : SimplePole.realize Mu.squareNode d = (f : RatFunc ℚ) := by
    exact LinearEquiv.ofInjective_symm_apply _ _
  have h := DFunLike.congr_fun (dataPullback_realization k) d
  change SimplePole.realize Tau.integerNode (dataPullback k d) = _
  simpa only [LinearMap.comp_apply, scaledSubstitution_apply, hd] using h

/-- Manuscript Lemma 2.2 for every rational function in Definition 2.1's domain. -/
theorem pullback_identity (k : ℕ) (hk : 1 ≤ k) (f : Mu.RationalDomain) :
    Tau.rationalFunctional k (rationalPullback k f) = Mu.rationalFunctional k f := by
  let d := (SimplePole.coordinates Mu.squareNode Mu.squareNode_injective).symm f
  have hd : SimplePole.ofData Mu.squareNode d = f := by
    exact (SimplePole.coordinates Mu.squareNode Mu.squareNode_injective).apply_symm_apply f
  have h := DFunLike.congr_fun (dataPullback_functional k hk) d
  change Tau.rationalFunctional k (SimplePole.ofData Tau.integerNode (dataPullback k d)) = _
  change Tau.rationalFunctional k (SimplePole.ofData Tau.integerNode (dataPullback k d)) =
    Mu.rationalFunctional k (SimplePole.ofData Mu.squareNode d) at h
  simpa only [hd] using h

end ManuscriptChain.Pullback
