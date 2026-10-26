import Zetahyperbolic.Section2.RationalFunctionals
import Mathlib.Algebra.Algebra.Hom.Rat

/-!
# Lemma 2.3: reflection on the actual rational-function domain

Reflection is the rational substitution `X ↦ -1-X`. It maps the subspace
of simple integer poles to itself. The tau identity is proved for every
element of that subspace using its unique polynomial/pole coordinates.
-/

noncomputable section
open scoped BigOperators nonZeroDivisors
open Polynomial

namespace ManuscriptChain.Tau

def reflectionPolynomial : ℚ[X] →ₐ[ℚ] ℚ[X] := aeval (-1-X : ℚ[X])

lemma reflectionPolynomial_apply (q : ℚ[X]) :
    reflectionPolynomial q = q.comp (-1-X) := rfl

lemma reflectionPolynomial_preserves_nonzero :
    (ℚ[X])⁰ ≤ ((ℚ[X])⁰).comap reflectionPolynomial := by
  intro q hq
  change reflectionPolynomial q ∈ (ℚ[X])⁰
  rw [mem_nonZeroDivisors_iff_ne_zero] at hq ⊢
  rw [reflectionPolynomial_apply]
  intro h
  rcases comp_eq_zero_iff.mp h with hzero | ⟨_, hconst⟩
  · exact hq hzero
  · have hc := congrArg (fun p : ℚ[X] => p.coeff 1) hconst
    norm_num [Polynomial.coeff_one] at hc

def reflection : RatFunc ℚ →ₐ[ℚ] RatFunc ℚ :=
  (RatFunc.mapRingHom reflectionPolynomial reflectionPolynomial_preserves_nonzero).toRatAlgHom

lemma reflection_algebraMap (q : ℚ[X]) :
    reflection (algebraMap ℚ[X] (RatFunc ℚ) q) =
      algebraMap ℚ[X] (RatFunc ℚ) (q.comp (-1-X)) := by
  change RatFunc.map reflectionPolynomial reflectionPolynomial_preserves_nonzero
    (algebraMap ℚ[X] (RatFunc ℚ) q) = _
  simpa only [map_one, div_one, reflectionPolynomial_apply] using
    RatFunc.map_apply_div reflectionPolynomial reflectionPolynomial_preserves_nonzero q 1

@[simp] theorem reflection_X : reflection (RatFunc.X : RatFunc ℚ) = -1-RatFunc.X := by
  rw [← RatFunc.algebraMap_X, reflection_algebraMap]
  simp

@[simp] theorem reflection_C (a : ℚ) : reflection (RatFunc.C a) = RatFunc.C a := by
  rw [← RatFunc.algebraMap_C, reflection_algebraMap]
  simp

def reflectIndex (r : ℤ) : ℤ := -1-r

def integerPole (r : ℤ) : RatFunc ℚ :=
  (algebraMap ℚ[X] (RatFunc ℚ) (X-C (r:ℚ)))⁻¹

theorem reflection_integerPole (r : ℤ) :
    reflection (integerPole r) = -integerPole (reflectIndex r) := by
  unfold integerPole
  rw [map_inv₀, reflection_algebraMap]
  have hp : (X-C (r:ℚ)).comp (-1-X) = -(X-C ((reflectIndex r:ℤ):ℚ)) := by
    simp only [Polynomial.sub_comp, Polynomial.X_comp, Polynomial.C_comp,
      reflectIndex, Int.cast_sub, Int.cast_neg, Int.cast_one, map_sub, map_neg, map_one]
    ring
  rw [hp, map_neg, inv_neg]

def reflectData : SimplePole.Data ℤ →ₗ[ℚ] SimplePole.Data ℤ :=
  reflectionPolynomial.toLinearMap.prodMap (-(Finsupp.lmapDomain ℚ ℚ reflectIndex))

lemma reflectData_apply (q : ℚ[X]) (c : ℤ →₀ ℚ) :
    reflectData (q,c) = (q.comp (-1-X), -Finsupp.mapDomain reflectIndex c) := rfl

lemma reflection_linearCombination (c : ℤ →₀ ℚ) :
    reflection (Finsupp.linearCombination ℚ integerPole c) =
      -(Finsupp.linearCombination ℚ integerPole (Finsupp.mapDomain reflectIndex c)) := by
  rw [Finsupp.linearCombination_mapDomain]
  simp only [Finsupp.linearCombination_apply, Finsupp.sum, Algebra.smul_def,
    map_sum, map_mul, AlgHom.commutes, reflection_integerPole, mul_neg,
    Finset.sum_neg_distrib, Function.comp_apply]

theorem realize_reflectData (d : SimplePole.Data ℤ) :
    SimplePole.realize integerNode (reflectData d) =
      reflection (SimplePole.realize integerNode d) := by
  rcases d with ⟨q,c⟩
  rw [reflectData_apply]
  change algebraMap ℚ[X] (RatFunc ℚ) (q.comp (-1-X)) +
      Finsupp.linearCombination ℚ integerPole (-Finsupp.mapDomain reflectIndex c) =
    reflection (algebraMap ℚ[X] (RatFunc ℚ) q + Finsupp.linearCombination ℚ integerPole c)
  rw [map_add, reflection_algebraMap, reflection_linearCombination, map_neg]

/-- Reflection closes the actual integer-pole rational subspace. -/
def rationalReflection (f : RationalDomain) : RationalDomain :=
  SimplePole.ofData integerNode
    (reflectData ((SimplePole.coordinates integerNode integerNode_injective).symm f))

/-- The constructed domain map is literal rational substitution, not a
symbolic replacement chosen to satisfy the functional identity. -/
theorem rationalReflection_coe (f : RationalDomain) :
    (rationalReflection f : RatFunc ℚ) = reflection (f : RatFunc ℚ) := by
  rw [rationalReflection, SimplePole.ofData_coe, realize_reflectData]
  congr 1
  exact congrArg Subtype.val
    ((SimplePole.coordinates integerNode integerNode_injective).apply_symm_apply f)

lemma functional_reflectData (k : ℕ) (hk : 1 ≤ k) (d : SimplePole.Data ℤ) :
    SimplePole.generatorFunctional
        ((Algebra.linearMap ℚ ℚ[X]).comp (tauPolynomial k)) (tauPolePoly k)
        (reflectData d) =
      -SimplePole.generatorFunctional
        ((Algebra.linearMap ℚ ℚ[X]).comp (tauPolynomial k)) (tauPolePoly k) d := by
  rcases d with ⟨q,c⟩
  rw [reflectData_apply]
  simp only [SimplePole.generatorFunctional, LinearMap.add_apply, LinearMap.comp_apply,
    LinearMap.fst_apply, LinearMap.snd_apply, tauPolynomial_reflection k hk,
    map_neg, Finsupp.linearCombination_mapDomain]
  have hp : tauPolePoly k ∘ reflectIndex = tauPolePoly k := by
    funext r
    exact tauPolePoly_reflect k r
  rw [hp]
  abel

/-- Lemma 2.3(1), now on the full actual rational-function domain. -/
theorem rationalFunctional_reflection (k : ℕ) (hk : 1 ≤ k) (f : RationalDomain) :
    rationalFunctional k (rationalReflection f) = -rationalFunctional k f := by
  rw [rationalReflection, rationalFunctional, SimplePole.functional_ofData]
  rw [functional_reflectData k hk]
  rfl

end ManuscriptChain.Tau
