import Zetahyperbolic.Section2.RationalDifference
import Zetahyperbolic.Section2.RationalRegularity
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Analysis.Calculus.ContDiff.Polynomial

/-!
# Analytic Taylor coefficients of the actual simple-pole rational functions

The canonical partial-fraction coefficient equals the normalized analytic
iterated derivative at the origin, provided the actual rational function is
regular there. The finite-difference formula therefore has the precise
analytic interpretation in Lemma 2.3.
-/

noncomputable section
open scoped BigOperators
open Polynomial Filter Topology

namespace ManuscriptChain.SimplePole

variable {ι : Type*} [DecidableEq ι]

/-- Evaluation using the unique partial-fraction data. -/
def realEval (node : ι → ℚ) (d : Data ι) (x : ℝ) : ℝ :=
  d.1.eval₂ (algebraMap ℚ ℝ) x +
    ∑ a ∈ d.2.support, (d.2 a : ℝ) / (x - (node a : ℝ))

lemma ratFunc_eval_fraction (r : RatFunc ℚ) (q D : ℚ[X]) (x : ℝ)
    (hD : D.eval₂ (algebraMap ℚ ℝ) x ≠ 0)
    (hr : r = algebraMap ℚ[X] (RatFunc ℚ) q / algebraMap ℚ[X] (RatFunc ℚ) D) :
    RatFunc.eval (algebraMap ℚ ℝ) x r =
      q.eval₂ (algebraMap ℚ ℝ) x / D.eval₂ (algebraMap ℚ ℝ) x := by
  have hD0 : D ≠ 0 := by intro hz; simp [hz] at hD
  have hdiv : r.denom ∣ D := (RatFunc.denom_dvd hD0).mpr ⟨q,hr⟩
  have hd : r.denom.eval₂ (algebraMap ℚ ℝ) x ≠ 0 := by
    intro hz
    exact hD (Polynomial.eval₂_eq_zero_of_dvd_of_eval₂_eq_zero _ _ hdiv hz)
  have hpoly := (RatFunc.num_mul_eq_mul_denom_iff hD0).mpr hr
  have he := congrArg (Polynomial.eval₂ (algebraMap ℚ ℝ) x) hpoly
  simp only [Polynomial.eval₂_mul] at he
  exact (div_eq_div_iff hd hD).mpr he

/-- Away from the displayed pole support, this is actual `RatFunc.eval`. -/
theorem realEval_eq_eval (node : ι → ℚ) (q : ℚ[X]) (c : ι →₀ ℚ) (x : ℝ)
    (hx : ∀ a ∈ c.support, x ≠ (node a : ℝ)) :
    realEval node (q,c) x =
      RatFunc.eval (algebraMap ℚ ℝ) x (realize node (q,c)) := by
  let D : ℚ[X] := ∏ a ∈ c.support, (X - C (node a))
  let P : ℚ[X] := q * D + ∑ a ∈ c.support,
    C (c a) * ∏ b ∈ c.support.erase a, (X - C (node b))
  have hDeval : D.eval₂ (algebraMap ℚ ℝ) x =
      ∏ a ∈ c.support, (x - (node a : ℝ)) := by
    simp [D, Polynomial.eval₂_finsetProd]
  have hD : D.eval₂ (algebraMap ℚ ℝ) x ≠ 0 := by
    rw [hDeval]
    exact Finset.prod_ne_zero_iff.mpr (fun a ha => sub_ne_zero.mpr (hx a ha))
  have hD0 : D ≠ 0 := by intro hz; simp [hz] at hD
  have hr : realize node (q,c) =
      algebraMap ℚ[X] (RatFunc ℚ) P / algebraMap ℚ[X] (RatFunc ℚ) D := by
    apply (eq_div_iff (RatFunc.algebraMap_ne_zero hD0)).mpr
    exact realize_mul_denominator node q c
  rw [ratFunc_eval_fraction _ P D x hD hr]
  apply (eq_div_iff hD).mpr
  simp only [P, Polynomial.eval₂_add, Polynomial.eval₂_mul,
    Polynomial.eval₂_finsetSum, Polynomial.eval₂_C, realEval, add_mul, Finset.sum_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro a ha
  have hp : D.eval₂ (algebraMap ℚ ℝ) x = (x-(node a : ℝ)) *
      ∏ b ∈ c.support.erase a, (x-(node b : ℝ)) := by
    rw [hDeval]
    exact (Finset.mul_prod_erase c.support _ ha).symm
  rw [hp]
  simp only [Polynomial.eval₂_finsetProd, Polynomial.eval₂_sub,
    Polynomial.eval₂_X, Polynomial.eval₂_C]
  field_simp [sub_ne_zero.mpr (hx a ha)]
  simp

lemma polynomial_iteratedDeriv_zero (n : ℕ) (q : ℚ[X]) :
    iteratedDeriv n (fun x : ℝ => q.eval₂ (algebraMap ℚ ℝ) x) 0 =
      (n.factorial : ℝ) * (q.coeff n : ℝ) := by
  induction q using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [Polynomial.eval₂_add]
    rw [iteratedDeriv_fun_add, hp, hq]
    · simp [mul_add]
    · simpa only [aeval_def] using (contDiff_aeval p n).contDiffAt
    · simpa only [aeval_def] using (contDiff_aeval q n).contDiffAt
  | monomial m a =>
    simp only [Polynomial.eval₂_monomial, iteratedDeriv_const_mul_field,
      iteratedDeriv_fun_pow_zero, Polynomial.coeff_monomial]
    split_ifs with h <;> simp_all [mul_comm]

lemma pole_iteratedDeriv_zero (n : ℕ) (r : ℝ) :
    iteratedDeriv n (fun x : ℝ => (x-r)⁻¹) 0 =
      -(n.factorial : ℝ) * (r^(n+1))⁻¹ := by
  rw [iteratedDeriv_eq_iterate]
  have h := congrFun (iter_deriv_inv_linear_sub n (1:ℝ) r) 0
  simp only [one_mul, one_pow, mul_one, zero_sub] at h
  rw [h]
  rw [show (-1-(n:ℤ)) = -((n+1:ℕ):ℤ) by omega, zpow_neg, zpow_natCast,
    neg_pow, pow_succ]
  by_cases hr : r = 0
  · subst r
    simp
  · have hrp : r ^ n ≠ 0 := pow_ne_zero n hr
    have hsgn : (-1:ℝ)^n ≠ 0 := pow_ne_zero n (by norm_num)
    field_simp [hr, hrp, hsgn]
    ring

/-- A nonzero supported residue forces a genuine pole: no cancelled pole is
hidden in the canonical simple-pole representation. -/
theorem supported_pole_denom_zero (node : ι → ℚ) (hn : Function.Injective node)
    (q : ℚ[X]) (c : ι →₀ ℚ) (a : ι) (ha : a ∈ c.support) :
    (realize node (q,c)).denom.eval (node a) = 0 := by
  let D : ℚ[X] := ∏ i ∈ c.support, (X-C (node i))
  let P : ℚ[X] := q*D + ∑ i ∈ c.support,
    C (c i) * ∏ j ∈ c.support.erase i, (X-C (node j))
  have hD0 : D ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    exact X_sub_C_ne_zero _
  have hr : realize node (q,c) = algebraMap ℚ[X] (RatFunc ℚ) P /
      algebraMap ℚ[X] (RatFunc ℚ) D := by
    apply (eq_div_iff (RatFunc.algebraMap_ne_zero hD0)).2
    exact realize_mul_denominator node q c
  have hD : D.eval (node a) = 0 := by
    rw [Polynomial.eval_prod]
    apply Finset.prod_eq_zero ha
    simp
  have hP : P.eval (node a) =
      c a * ∏ b ∈ c.support.erase a, (node a - node b) := by
    simp only [P, eval_add, eval_mul, hD, mul_zero, zero_add, eval_finsetSum]
    rw [Finset.sum_eq_single a]
    · simp only [eval_mul, eval_C, eval_prod, eval_sub, eval_X]
    · intro b hb hba
      have hp : (∏ d ∈ c.support.erase b, (X-C (node d))).eval (node a) = 0 := by
        rw [eval_prod]
        apply Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨Ne.symm hba, ha⟩)
        simp
      rw [hp, mul_zero]
    · intro hnot
      exact (hnot ha).elim
  have hP0 : P.eval (node a) ≠ 0 := by
    rw [hP]
    apply mul_ne_zero (Finsupp.mem_support_iff.mp ha)
    apply Finset.prod_ne_zero_iff.mpr
    intro b hb
    exact sub_ne_zero.mpr (fun h => (Finset.mem_erase.mp hb).1 (hn h).symm)
  have he := congrArg (Polynomial.eval (node a))
    ((RatFunc.num_mul_eq_mul_denom_iff hD0).mpr hr)
  simp only [eval_mul, hD, mul_zero] at he
  exact (mul_eq_zero.mp he.symm).resolve_left hP0

theorem realEval_iteratedDeriv_zero (n : ℕ) (node : ι → ℚ)
    (q : ℚ[X]) (c : ι →₀ ℚ) (hc : ∀ a ∈ c.support, node a ≠ 0) :
    iteratedDeriv n (realEval node (q,c)) 0 = (n.factorial : ℝ) *
      ((q.coeff n : ℝ) - ∑ a ∈ c.support, (c a : ℝ) * ((node a : ℝ)^(n+1))⁻¹) := by
  have hp (a : ι) (ha : a ∈ c.support) :
      ContDiffAt ℝ n (fun x : ℝ => (c a : ℝ) / (x-(node a : ℝ))) 0 := by
    apply contDiffAt_const.div (contDiffAt_id.sub contDiffAt_const)
    simpa using (show (node a : ℝ) ≠ 0 by exact_mod_cast hc a ha)
  unfold realEval
  rw [iteratedDeriv_fun_add]
  · rw [polynomial_iteratedDeriv_zero, iteratedDeriv_fun_sum hp]
    simp only [div_eq_mul_inv, iteratedDeriv_const_mul_field, pole_iteratedDeriv_zero]
    rw [mul_sub, Finset.mul_sum]
    congr 1
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro a ha
    ring
  · simpa only [aeval_def] using (contDiff_aeval q n).contDiffAt
  · exact ContDiffAt.sum hp

/-- The canonical expansion and actual rational evaluation have the same germ. -/
theorem realEval_eventuallyEq_eval (node : ι → ℚ) (q : ℚ[X]) (c : ι →₀ ℚ)
    (hc : ∀ a ∈ c.support, node a ≠ 0) :
    realEval node (q,c) =ᶠ[𝓝 (0:ℝ)]
      (fun x => RatFunc.eval (algebraMap ℚ ℝ) x (realize node (q,c))) := by
  have hs : ∀ᶠ x in 𝓝 (0:ℝ), ∀ a ∈ c.support, x ≠ (node a : ℝ) := by
    rw [eventually_all_finset]
    intro a ha
    apply eventually_ne_nhds
    exact Ne.symm (by exact_mod_cast hc a ha)
  filter_upwards [hs] with x hx
  exact realEval_eq_eval node q c x hx

end ManuscriptChain.SimplePole

namespace ManuscriptChain.Tau

/-- Regularity at zero is equivalent to vanishing of the canonical zero residue. -/
theorem regular_at_zero_iff (q : ℚ[X]) (c : ℤ →₀ ℚ) :
    (SimplePole.realize integerNode (q,c)).denom.eval 0 ≠ 0 ↔ c 0 = 0 := by
  constructor
  · intro hd
    by_contra hc
    exact hd (SimplePole.supported_pole_denom_zero integerNode integerNode_injective
      q c 0 (Finsupp.mem_support_iff.mpr hc))
  · exact eval_denom_zero_ne_zero q c

/-- Every nonnegative Taylor coefficient is the normalized analytic derivative. -/
theorem dataCoefficient_eq_iteratedDeriv (n : ℕ) (q : ℚ[X]) (c : ℤ →₀ ℚ)
    (hc : c 0 = 0) :
    (dataCoefficient n (q,c) : ℝ) =
      iteratedDeriv n (fun x : ℝ =>
        RatFunc.eval (algebraMap ℚ ℝ) x (SimplePole.realize integerNode (q,c))) 0 /
          (n.factorial : ℝ) := by
  have hs (r : ℤ) (hr : r ∈ c.support) : integerNode r ≠ 0 := by
    intro h
    have hr0 : r = 0 := by
      dsimp [integerNode] at h
      exact_mod_cast h
    subst r
    exact (Finsupp.mem_support_iff.mp hr) hc
  rw [← (SimplePole.realEval_eventuallyEq_eval integerNode q c hs).iteratedDeriv_eq n,
    SimplePole.realEval_iteratedDeriv_zero n integerNode q c hs, dataCoefficient_apply]
  push_cast
  have hf : (n.factorial : ℝ) ≠ 0 := by positivity
  field_simp [hf]

/-- Intrinsic analytic Taylor coefficient for any element of the actual domain
whose reduced denominator does not vanish at the origin. -/
theorem partialFractionCoefficient_eq_iteratedDeriv (n : ℕ) (f : RationalDomain)
    (hf : (RatFunc.denom (f : RatFunc ℚ)).eval 0 ≠ 0) :
    (partialFractionCoefficient n f : ℝ) =
      iteratedDeriv n (fun x : ℝ => RatFunc.eval (algebraMap ℚ ℝ) x (f : RatFunc ℚ)) 0 /
        (n.factorial : ℝ) := by
  let d := (SimplePole.coordinates integerNode integerNode_injective).symm f
  have hd : SimplePole.ofData integerNode d = f :=
    (SimplePole.coordinates integerNode integerNode_injective).apply_symm_apply f
  rw [← hd, SimplePole.ofData_coe] at hf
  rw [← hd, partialFractionCoefficient_ofData]
  exact dataCoefficient_eq_iteratedDeriv n d.1 d.2 ((regular_at_zero_iff d.1 d.2).mp hf)

/-- Lemma 2.3 with the actual normalized analytic derivative at zero.
Evaluation at any parameter gives the same scalar derivative. -/
theorem rationalFunctional_difference_analytic (k : ℕ) (hk : 1 ≤ k)
    (f : RationalDomain) (hf : (RatFunc.denom (f : RatFunc ℚ)).eval 0 ≠ 0)
    (z : ℝ) :
    (rationalFunctional k (rationalDifference f)).eval₂ (algebraMap ℚ ℝ) z =
      iteratedDeriv (2*k)
        (fun x : ℝ => RatFunc.eval (algebraMap ℚ ℝ) x (f : RatFunc ℚ)) 0 /
          ((2*k).factorial : ℝ) := by
  rw [rationalFunctional_difference k hk, Polynomial.eval₂_C]
  exact partialFractionCoefficient_eq_iteratedDeriv (2*k) f hf

end ManuscriptChain.Tau
