import Zetahyperbolic.Section2.RationalFunctionals
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Algebra.Algebra.Hom.Rat

/-!
# The rational substitution behind Lemma 2.2

The substitution is the actual rational-function algebra homomorphism
`R(X) ↦ R(-X²)`. Polynomial division and the two simple poles give its
finite-coordinate pullback after multiplication by `X^(2k+1)`.
-/

noncomputable section
open scoped BigOperators nonZeroDivisors
open Polynomial

namespace ManuscriptChain.Pullback

def substitutionPolynomial : ℚ[X] →ₐ[ℚ] ℚ[X] := aeval (-X^2 : ℚ[X])

lemma substitutionPolynomial_apply (q : ℚ[X]) :
    substitutionPolynomial q = q.comp (-X^2) := by
  rfl

lemma substitutionPolynomial_preserves_nonzero :
    (ℚ[X])⁰ ≤ ((ℚ[X])⁰).comap substitutionPolynomial := by
  intro q hq
  change substitutionPolynomial q ∈ (ℚ[X])⁰
  rw [mem_nonZeroDivisors_iff_ne_zero] at hq ⊢
  rw [substitutionPolynomial_apply]
  intro h
  rcases comp_eq_zero_iff.mp h with hzero | ⟨_, hconst⟩
  · exact hq hzero
  · have hc := congrArg (fun p : ℚ[X] => p.coeff 2) hconst
    norm_num at hc

def substitution : RatFunc ℚ →ₐ[ℚ] RatFunc ℚ :=
  (RatFunc.mapRingHom substitutionPolynomial substitutionPolynomial_preserves_nonzero).toRatAlgHom

lemma substitution_algebraMap (q : ℚ[X]) :
    substitution (algebraMap ℚ[X] (RatFunc ℚ) q) =
      algebraMap ℚ[X] (RatFunc ℚ) (q.comp (-X^2)) := by
  change RatFunc.map substitutionPolynomial substitutionPolynomial_preserves_nonzero
    (algebraMap ℚ[X] (RatFunc ℚ) q) = _
  simpa only [map_one, div_one, substitutionPolynomial_apply] using
    RatFunc.map_apply_div substitutionPolynomial substitutionPolynomial_preserves_nonzero q 1

@[simp] lemma substitution_X : substitution (RatFunc.X : RatFunc ℚ) = -RatFunc.X^2 := by
  rw [← RatFunc.algebraMap_X, substitution_algebraMap]
  simp

@[simp] lemma substitution_C (a : ℚ) : substitution (RatFunc.C a) = RatFunc.C a := by
  rw [← RatFunc.algebraMap_C, substitution_algebraMap]
  simp

/-- Polynomial part of `X^(2k+1)/(a²-X²)`. -/
def polePolynomial (k : ℕ) (a : ℚ) : ℚ[X] :=
  -∑ e ∈ Finset.range k, monomial (2*e+1) (a^(2*(k-1-e)))

lemma tau_polePolynomial (k : ℕ) (hk : 1 ≤ k) (a : ℚ) :
    Tau.tauPolynomial k (polePolynomial k a) = -Tau.tauMonomial k (2*k-1) := by
  unfold polePolynomial
  rw [map_neg, map_sum]
  congr 1
  have hsum : (∑ e ∈ Finset.range k,
      Tau.tauPolynomial k (monomial (2*e+1) (a^(2*(k-1-e))))) =
      Tau.tauMonomial k (2*k-1) := by
    rw [Finset.sum_eq_single (k-1)]
    · rw [Tau.tauPolynomial_monomial]
      simp only [Nat.sub_self, mul_zero, pow_zero, one_mul]
      congr 1
      omega
    · intro e he hne
      rw [Tau.tauPolynomial_monomial]
      have he' : e < k := Finset.mem_range.mp he
      have hcut : ¬ 2*k-1 ≤ 2*e+1 := by omega
      simp [Tau.tauMonomial, hcut]
    · intro hnot
      exact (hnot (Finset.mem_range.mpr (by omega))).elim
  exact hsum

lemma polePolynomial_eq_geometric (k : ℕ) (a : ℚ) :
    polePolynomial k a =
      -X * ∑ e ∈ Finset.range k, (X^2)^e * (C a^2)^(k-1-e) := by
  unfold polePolynomial
  rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro e he
  have hC : C (a^(2*(k-1-e))) = (C a^2)^(k-1-e) := by
    rw [pow_mul, Polynomial.C_pow, Polynomial.C_pow]
  rw [← C_mul_X_pow_eq_monomial, hC, pow_succ X (2*e), pow_mul X 2 e]
  ring

lemma pole_division_identity {K : Type*} [Field K] [CharZero K]
    (k : ℕ) (x a : K) (hminus : x-a ≠ 0) (hplus : x+a ≠ 0) :
    x^(2*k+1) / (a^2-x^2) =
      -x * (∑ e ∈ Finset.range k, (x^2)^e * (a^2)^(k-1-e)) -
        (a^(2*k)/2) * ((x-a)⁻¹ + (x+a)⁻¹) := by
  have hd : a^2-x^2 ≠ 0 := by
    have : a^2-x^2 = -(x-a)*(x+a) := by ring
    rw [this]
    exact mul_ne_zero (neg_ne_zero.mpr hminus) hplus
  have hg := (Commute.all (x^2) (a^2)).mul_geom_sum₂ k
  have hpoly : -x * (∑ e ∈ Finset.range k, (x^2)^e * (a^2)^(k-1-e)) *
      (a^2-x^2) = x^(2*k+1) - a^(2*k)*x := by
    calc
      _ = x * ((x^2-a^2) * ∑ e ∈ Finset.range k, (x^2)^e * (a^2)^(k-1-e)) := by ring
      _ = x * ((x^2)^k-(a^2)^k) := by rw [hg]
      _ = _ := by rw [← pow_mul, ← pow_mul, pow_succ]; ring
  apply (div_eq_iff hd).2
  have hpole : (a^(2*k)/2) * ((x-a)⁻¹ + (x+a)⁻¹) * (a^2-x^2) =
      -(a^(2*k)*x) := by
    field_simp
    ring
  rw [sub_mul, hpoly, hpole]
  ring

lemma rational_X_sub_ne_zero (a : ℚ) : (RatFunc.X : RatFunc ℚ) - RatFunc.C a ≠ 0 := by
  rw [← RatFunc.algebraMap_X, ← RatFunc.algebraMap_C, ← map_sub]
  exact RatFunc.algebraMap_ne_zero (X_sub_C_ne_zero a)

lemma rational_X_add_ne_zero (a : ℚ) : (RatFunc.X : RatFunc ℚ) + RatFunc.C a ≠ 0 := by
  simpa only [map_neg, sub_neg_eq_add] using rational_X_sub_ne_zero (-a)

lemma C_eq_cast (a : ℚ) : RatFunc.C a = (a : RatFunc ℚ) := by
  exact map_ratCast RatFunc.C a

lemma algebraMap_eq_cast (a : ℚ) :
    algebraMap ℚ (RatFunc ℚ) a = (a : RatFunc ℚ) := by
  exact map_ratCast (algebraMap ℚ (RatFunc ℚ)) a

def poleData (k j : ℕ) : SimplePole.Data ℤ :=
  (polePolynomial k ((j+1 : ℕ) : ℚ),
    Finsupp.single ((j+1 : ℕ) : ℤ) (-((j+1 : ℕ) : ℚ)^(2*k)/2) +
    Finsupp.single (-((j+1 : ℕ) : ℤ)) (-((j+1 : ℕ) : ℚ)^(2*k)/2))

lemma poleData_realization (k j : ℕ) :
    SimplePole.realize Tau.integerNode (poleData k j) =
      (RatFunc.X : RatFunc ℚ)^(2*k+1) /
        (RatFunc.C (((j+1 : ℕ) : ℚ)^2) - RatFunc.X^2) := by
  have he := pole_division_identity k (RatFunc.X : RatFunc ℚ)
    (RatFunc.C ((j+1 : ℕ) : ℚ))
    (rational_X_sub_ne_zero _) (rational_X_add_ne_zero _)
  rw [← map_pow] at he
  rw [he]
  simp only [SimplePole.realize, LinearMap.add_apply, LinearMap.comp_apply,
    LinearMap.fst_apply, LinearMap.snd_apply, poleData, map_add,
    Finsupp.linearCombination_single, SimplePole.polynomialEmbedding,
    AlgHom.toLinearMap_apply, IsScalarTower.toAlgHom_apply]
  rw [polePolynomial_eq_geometric]
  simp only [map_mul, map_neg, map_sum, map_pow, RatFunc.algebraMap_X,
    RatFunc.algebraMap_C, map_sub, Tau.integerNode, Int.cast_natCast,
    Int.cast_neg, sub_neg_eq_add]
  simp only [C_eq_cast, Algebra.smul_def, algebraMap_eq_cast, map_add,
    RatFunc.algebraMap_X, RatFunc.algebraMap_C, C_eq_cast, Rat.cast_neg,
    Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat, Rat.cast_natCast]
  ring

lemma tau_poleData (k j : ℕ) (hk : 1 ≤ k) :
    Tau.rationalFunctional k (SimplePole.ofData Tau.integerNode (poleData k j)) =
      Tau.muPolePoly k (j+1) := by
  rw [Tau.rationalFunctional, SimplePole.functional_ofData]
  simp only [SimplePole.generatorFunctional, LinearMap.add_apply, LinearMap.comp_apply,
    LinearMap.fst_apply, LinearMap.snd_apply, poleData, map_add,
    Finsupp.linearCombination_single]
  rw [tau_polePolynomial k hk]
  rw [Tau.pullback_identity_pole k (j+1) hk (by omega)]
  simp only [Algebra.linearMap_apply, Polynomial.algebraMap_eq,
    Polynomial.smul_eq_C_mul, neg_div, map_neg]
  ring

end ManuscriptChain.Pullback
