import Zetahyperbolic.Section2.RationalReflection
import Zetahyperbolic.Section2.TauPolynomialDifference

/-!
# Finite differences on the actual integer-pole rational domain

Translation is the actual substitution `X ↦ X+1`. Its tau value is identified
with the coefficient supplied by the unique partial-fraction decomposition.
The separate analytic identification with a normalized derivative at zero
requires regularity at zero and is not asserted here.
-/

noncomputable section
open scoped BigOperators nonZeroDivisors
open Polynomial

namespace ManuscriptChain.Tau

def translationPolynomial : ℚ[X] →ₐ[ℚ] ℚ[X] := aeval (X+1 : ℚ[X])

lemma translationPolynomial_apply (q : ℚ[X]) :
    translationPolynomial q = q.comp (X+1) := rfl

lemma translationPolynomial_preserves_nonzero :
    (ℚ[X])⁰ ≤ ((ℚ[X])⁰).comap translationPolynomial := by
  intro q hq
  change translationPolynomial q ∈ (ℚ[X])⁰
  rw [mem_nonZeroDivisors_iff_ne_zero] at hq ⊢
  rw [translationPolynomial_apply]
  intro h
  rcases comp_eq_zero_iff.mp h with hzero | ⟨_, hconst⟩
  · exact hq hzero
  · have hc := congrArg (fun p : ℚ[X] => p.coeff 1) hconst
    norm_num [Polynomial.coeff_one] at hc

def translation : RatFunc ℚ →ₐ[ℚ] RatFunc ℚ :=
  (RatFunc.mapRingHom translationPolynomial translationPolynomial_preserves_nonzero).toRatAlgHom

lemma translation_algebraMap (q : ℚ[X]) :
    translation (algebraMap ℚ[X] (RatFunc ℚ) q) =
      algebraMap ℚ[X] (RatFunc ℚ) (q.comp (X+1)) := by
  change RatFunc.map translationPolynomial translationPolynomial_preserves_nonzero
    (algebraMap ℚ[X] (RatFunc ℚ) q) = _
  simpa only [map_one, div_one, translationPolynomial_apply] using
    RatFunc.map_apply_div translationPolynomial translationPolynomial_preserves_nonzero q 1

@[simp] theorem translation_X : translation (RatFunc.X : RatFunc ℚ) = RatFunc.X+1 := by
  rw [← RatFunc.algebraMap_X, translation_algebraMap]
  simp

@[simp] theorem translation_C (a : ℚ) : translation (RatFunc.C a) = RatFunc.C a := by
  rw [← RatFunc.algebraMap_C, translation_algebraMap]
  simp

def translateIndex (r : ℤ) : ℤ := r-1

theorem translation_integerPole (r : ℤ) :
    translation (integerPole r) = integerPole (translateIndex r) := by
  unfold integerPole
  rw [map_inv₀, translation_algebraMap]
  have hp : (X-C (r:ℚ)).comp (X+1) = X-C ((translateIndex r:ℤ):ℚ) := by
    simp only [Polynomial.sub_comp, Polynomial.X_comp, Polynomial.C_comp,
      translateIndex, Int.cast_sub, Int.cast_one, map_sub, map_one]
    ring
  rw [hp]

def translateData : SimplePole.Data ℤ →ₗ[ℚ] SimplePole.Data ℤ :=
  translationPolynomial.toLinearMap.prodMap (Finsupp.lmapDomain ℚ ℚ translateIndex)

lemma translateData_apply (q : ℚ[X]) (c : ℤ →₀ ℚ) :
    translateData (q,c) = (q.comp (X+1), Finsupp.mapDomain translateIndex c) := rfl

lemma translation_linearCombination (c : ℤ →₀ ℚ) :
    translation (Finsupp.linearCombination ℚ integerPole c) =
      Finsupp.linearCombination ℚ integerPole (Finsupp.mapDomain translateIndex c) := by
  rw [Finsupp.linearCombination_mapDomain]
  simp only [Finsupp.linearCombination_apply, Finsupp.sum, Algebra.smul_def,
    map_sum, map_mul, AlgHom.commutes, translation_integerPole, Function.comp_apply]

theorem realize_translateData (d : SimplePole.Data ℤ) :
    SimplePole.realize integerNode (translateData d) =
      translation (SimplePole.realize integerNode d) := by
  rcases d with ⟨q,c⟩
  rw [translateData_apply]
  change algebraMap ℚ[X] (RatFunc ℚ) (q.comp (X+1)) +
      Finsupp.linearCombination ℚ integerPole (Finsupp.mapDomain translateIndex c) =
    translation (algebraMap ℚ[X] (RatFunc ℚ) q + Finsupp.linearCombination ℚ integerPole c)
  rw [map_add, translation_algebraMap, translation_linearCombination]

def differenceData : SimplePole.Data ℤ →ₗ[ℚ] SimplePole.Data ℤ :=
  translateData - LinearMap.id

def rationalDifference : RationalDomain →ₗ[ℚ] RationalDomain :=
  ((SimplePole.realize integerNode).rangeRestrict.comp differenceData).comp
    (SimplePole.coordinates integerNode integerNode_injective).symm.toLinearMap

/-- The difference is literally `R(X+1)-R(X)` as an actual rational function. -/
theorem rationalDifference_coe (f : RationalDomain) :
    (rationalDifference f : RatFunc ℚ) = translation (f : RatFunc ℚ) - (f : RatFunc ℚ) := by
  let d := (SimplePole.coordinates integerNode integerNode_injective).symm f
  have hd : SimplePole.realize integerNode d = (f : RatFunc ℚ) := by
    exact LinearEquiv.ofInjective_symm_apply _ _
  change SimplePole.realize integerNode (differenceData d) = _
  rw [differenceData, LinearMap.sub_apply, LinearMap.id_apply, map_sub,
    realize_translateData, hd]

/-- Coefficient read from the unique polynomial and simple-pole coordinates.
For nonzero poles this is the usual Taylor coefficient; the pole at zero has
zero contribution to every nonnegative Laurent coefficient. -/
def dataCoefficient (n : ℕ) : SimplePole.Data ℤ →ₗ[ℚ] ℚ :=
  (Polynomial.lcoeff ℚ n).comp (LinearMap.fst ℚ ℚ[X] (ℤ →₀ ℚ)) -
    (Finsupp.linearCombination ℚ (fun r : ℤ => ((r:ℚ)^(n+1))⁻¹)).comp
      (LinearMap.snd ℚ ℚ[X] (ℤ →₀ ℚ))

def partialFractionCoefficient (n : ℕ) : RationalDomain →ₗ[ℚ] ℚ :=
  (dataCoefficient n).comp
    (SimplePole.coordinates integerNode integerNode_injective).symm.toLinearMap

@[simp] theorem partialFractionCoefficient_ofData (n : ℕ) (d : SimplePole.Data ℤ) :
    partialFractionCoefficient n (SimplePole.ofData integerNode d) = dataCoefficient n d := by
  change dataCoefficient n ((SimplePole.coordinates integerNode integerNode_injective).symm
    (SimplePole.coordinates integerNode integerNode_injective d)) = _
  rw [LinearEquiv.symm_apply_apply]

theorem dataCoefficient_apply (n : ℕ) (q : ℚ[X]) (c : ℤ →₀ ℚ) :
    dataCoefficient n (q,c) = q.coeff n -
      ∑ r ∈ c.support, c r * ((r:ℚ)^(n+1))⁻¹ := by
  simp [dataCoefficient, Finsupp.linearCombination_apply, Finsupp.sum]

lemma tau_difference_pole_all (k : ℕ) (r : ℤ) :
    tauPolePoly k (r-1) - tauPolePoly k r = C (-((r:ℚ)^(2*k+1))⁻¹) := by
  by_cases hr : r = 0
  · subst r
    simp [tauPolePoly, dIndex, Real.harmonic]
  · exact tau_difference_pole k r hr

lemma differenceData_functional (k : ℕ) (hk : 1 ≤ k) :
    (rationalFunctional k).comp
        ((SimplePole.realize integerNode).rangeRestrict.comp differenceData) =
      (Algebra.linearMap ℚ ℚ[X]).comp (dataCoefficient (2*k)) := by
  apply LinearMap.prod_ext
  · apply LinearMap.ext
    intro q
    change rationalFunctional k (SimplePole.ofData integerNode (differenceData (q,0))) = _
    have hd : differenceData (q,0) = (q.comp (X+1)-q,0) := by
      simp [differenceData, translateData_apply]
    rw [hd, rationalFunctional_polynomial, tauPolynomial_difference k hk]
    simp [dataCoefficient]
  · apply Finsupp.lhom_ext
    intro r c
    have hc : Finsupp.single r c = c • Finsupp.single r (1:ℚ) := by simp
    rw [hc, LinearMap.map_smul, LinearMap.map_smul]
    congr 1
    change rationalFunctional k (SimplePole.ofData integerNode
      (differenceData (0,Finsupp.single r 1))) = _
    have hd : differenceData (0,Finsupp.single r 1) =
        (0,Finsupp.single (r-1) 1) - (0,Finsupp.single r 1) := by
      simp [differenceData, translateData_apply, translateIndex]
    rw [hd]
    change rationalFunctional k ((SimplePole.realize integerNode).rangeRestrict
      ((0,Finsupp.single (r-1) 1) - (0,Finsupp.single r 1))) = _
    rw [map_sub, map_sub]
    change rationalFunctional k (SimplePole.ofData integerNode (0,Finsupp.single (r-1) 1)) -
      rationalFunctional k (SimplePole.ofData integerNode (0,Finsupp.single r 1)) = _
    rw [rationalFunctional_pole, rationalFunctional_pole]
    change tauPolePoly k (r-1) - tauPolePoly k r = _
    rw [tau_difference_pole_all]
    simp [dataCoefficient]

/-- The full rational finite-difference formula with an explicit, intrinsic
partial-fraction coefficient. No derivative regularity is assumed or asserted. -/
theorem rationalFunctional_difference (k : ℕ) (hk : 1 ≤ k) (f : RationalDomain) :
    rationalFunctional k (rationalDifference f) = C (partialFractionCoefficient (2*k) f) := by
  let d := (SimplePole.coordinates integerNode integerNode_injective).symm f
  have h := DFunLike.congr_fun (differenceData_functional k hk) d
  exact h

end ManuscriptChain.Tau
