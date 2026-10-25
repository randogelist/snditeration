import Zetahyperbolic.Section3.HyperbolicMomentBernoulli
import Zetahyperbolic.Section3.PoleIntegralIdentity
import Zetahyperbolic.Section3.PartialFractionsResidues
import Zetahyperbolic.Section3.ConcreteMomentMeasure
import Zetahyperbolic.Section2.DenominatorFactorization

/-!
# Actual rational Hankel entries as positive-half-line integrals

The finite polynomial-plus-poles decomposition is transported through the
proved monomial and simple-pole integral identities.
-/

noncomputable section
open scoped BigOperators
open MeasureTheory Set Polynomial

namespace ManuscriptChain.Hyperbolic

theorem evalQ_sq_eq_sum (q : ℚ[X]) (y : ℝ) :
    Real.evalQ q (y ^ 2) = ∑ e ∈ q.support, (q.coeff e : ℝ) * y ^ (2 * e) := by
  rw [Real.evalQ, Real.realPolynomial, Polynomial.eval_map]
  change Polynomial.eval₂ (Rat.castHom ℝ) (y ^ 2) q = _
  rw [Polynomial.eval₂_eq_sum]
  simp only [Polynomial.sum, pow_mul]
  rfl

theorem integrableOn_polynomial_density (k : ℕ) (q : ℚ[X]) :
    IntegrableOn (fun y => Real.evalQ q (y ^ 2) * density k y) (Ioi 0) := by
  simp_rw [evalQ_sq_eq_sum, Finset.sum_mul, mul_assoc]
  apply integrable_finsetSum
  intro e he
  exact (integrableOn_monomial_density k e).const_mul _

theorem integral_polynomial_density (k : ℕ) (q : ℚ[X]) :
    (∫ y : ℝ in Ioi 0, Real.evalQ q (y ^ 2) * density k y) =
      (Real.polynomialMoment k q : ℝ) := by
  simp_rw [evalQ_sq_eq_sum, Finset.sum_mul, mul_assoc]
  rw [integral_finsetSum _ (fun e _ =>
    (integrableOn_monomial_density k e).const_mul (q.coeff e : ℝ))]
  simp_rw [integral_const_mul, integral_monomial_density_eq_monomialMoment]
  simp [Real.polynomialMoment]

theorem integrableOn_pole_density (k a : ℕ) (ha : 0 < a) :
    IntegrableOn (fun y => density k y / (y ^ 2 + (a : ℝ) ^ 2)) (Ioi 0) := by
  have hw : IntegrableOn (density k) (Ioi 0) := by
    simpa using integrableOn_monomial_density k 0
  apply (hw.div_const ((a : ℝ) ^ 2)).mono'
  · exact ((measurable_density k).div
      ((measurable_id.pow_const 2).add measurable_const)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    have hw0 := (density_pos k hy).le
    have ha0 : (0 : ℝ) < a := by exact_mod_cast ha
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hw0 (by positivity))]
    exact div_le_div_of_nonneg_left hw0 (by positivity) (by nlinarith [sq_nonneg y])

/-- The finite partial-fraction expression defining an actual Gram entry. -/
def resolvedKernel (p : Real.Parameters) (i j : ℕ) (y : ℝ) : ℝ :=
  Real.evalQ (Real.quotient p i j) (y ^ 2) +
    ∑ a ∈ Finset.Icc (p.N + 1) p.K,
      (Real.residue p i j a : ℝ) / (y ^ 2 + (a : ℝ) ^ 2)

theorem integrableOn_resolvedKernel_density (p : Real.Parameters) (i j : ℕ) :
    IntegrableOn (fun y => resolvedKernel p i j y * density p.k y) (Ioi 0) := by
  unfold resolvedKernel
  simp_rw [add_mul, Finset.sum_mul]
  apply (integrableOn_polynomial_density p.k _).add
  apply integrable_finsetSum
  intro a ha
  have hapos : 0 < a := by have h := (Finset.mem_Icc.mp ha).1; omega
  have h := (integrableOn_pole_density p.k a hapos).const_mul
    (Real.residue p i j a : ℝ)
  simpa only [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using h

theorem gram_eq_resolvedKernel_integral (p : Real.Parameters)
    (hpole : PoleIntegralIdentity p.k) (i j : Fin p.h) :
    Real.gram p (Real.zeta p.weight) i j =
      ∫ y : ℝ in Ioi 0, resolvedKernel p i.val j.val y * density p.k y := by
  have hsplit (y : ℝ) : resolvedKernel p i.val j.val y * density p.k y =
      Real.evalQ (Real.quotient p i.val j.val) (y ^ 2) * density p.k y +
        ∑ a ∈ Finset.Icc (p.N + 1) p.K,
          (Real.residue p i.val j.val a : ℝ) *
            (density p.k y / (y ^ 2 + (a : ℝ) ^ 2)) := by
    unfold resolvedKernel
    rw [add_mul, Finset.sum_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro a ha
    ring
  have hi (a : ℕ) (ha : a ∈ Finset.Icc (p.N + 1) p.K) :
      IntegrableOn (fun y => (Real.residue p i.val j.val a : ℝ) *
        (density p.k y / (y ^ 2 + (a : ℝ) ^ 2))) (Ioi 0) := by
    apply (integrableOn_pole_density p.k a _).const_mul
    have h := (Finset.mem_Icc.mp ha).1
    omega
  simp_rw [hsplit]
  rw [integral_add (integrableOn_polynomial_density p.k _) (integrable_finsetSum _ hi),
    integral_polynomial_density, integral_finsetSum _ hi]
  simp_rw [integral_const_mul]
  have he (a : ℕ) (ha : a ∈ Finset.Icc (p.N + 1) p.K) :=
    hpole a (by have h := (Finset.mem_Icc.mp ha).1; omega)
  simp only [Real.gram, Real.pencil, Real.evalQ, Real.realPolynomial,
    Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
  change (Real.entryA p i.val j.val : ℝ) +
    (Real.entryM p i.val j.val : ℝ) * Real.zeta p.weight = _
  unfold Real.entryA Real.entryM
  push_cast
  rw [Finset.sum_mul]
  rw [add_assoc, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro a ha
  rw [he a ha]
  dsimp [Real.Parameters.weight]
  ring


theorem evalQ_eq_eval₂ (q : ℚ[X]) (x : ℝ) :
    Real.evalQ q x = q.eval₂ (algebraMap ℚ ℝ) x := by
  simp only [Real.evalQ, Real.realPolynomial, Polynomial.eval_map]
  rfl

/-- The partial-fraction expression is the actual rational kernel at `y²`. -/
theorem resolvedKernel_eq_fraction (p : Real.Parameters) (i j : ℕ) {y : ℝ}
    (hy : 0 < y) :
    resolvedKernel p i j y =
      Real.evalQ (Real.numerator p i j) (y ^ 2) /
        Real.evalQ (Real.tailD p) (y ^ 2) := by
  let s := Finset.Icc (p.N + 1) p.K
  let T : ℝ := ∏ a ∈ s, (y ^ 2 + (a : ℝ) ^ 2)
  have hT : T ≠ 0 := by
    apply ne_of_gt
    apply Finset.prod_pos
    intro a ha
    positivity
  have hev : Real.evalQ (Real.tailD p) (y ^ 2) = T := by
    rw [evalQ_eq_eval₂]
    simp only [Real.tailD, Polynomial.eval₂_finsetProd, Polynomial.eval₂_add,
      Polynomial.eval₂_X, Polynomial.eval₂_pow,
      Polynomial.eval₂_natCast, map_pow, map_natCast]
    rfl
  rw [hev]
  apply (eq_div_iff hT).2
  have hf := congrArg (fun q : ℚ[X] => q.eval₂ (algebraMap ℚ ℝ) (y ^ 2))
    (PartialFractions.rational_kernel_decomposition p i j)
  simp only [Polynomial.eval₂_add, Polynomial.eval₂_mul,
    Polynomial.eval₂_finsetSum, Polynomial.eval₂_finsetProd, Polynomial.eval₂_C,
    Polynomial.eval₂_X, Polynomial.eval₂_pow, Polynomial.eval₂_natCast,
    map_pow, map_natCast] at hf
  rw [← evalQ_eq_eval₂, ← evalQ_eq_eval₂, ← evalQ_eq_eval₂, hev] at hf
  rw [hf]
  unfold resolvedKernel
  rw [add_mul, Finset.sum_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro a ha
  have ha' : a ∈ s := ha
  have hd : y ^ 2 + (a : ℝ) ^ 2 ≠ 0 := by positivity
  change (↑(Real.residue p i j a) / (y ^ 2 + (a : ℝ) ^ 2)) * T =
    ↑(Real.residue p i j a) * ∏ b ∈ s.erase a, (y ^ 2 + (b : ℝ) ^ 2)
  rw [show T = (y ^ 2 + (a : ℝ) ^ 2) *
      ∏ b ∈ s.erase a, (y ^ 2 + (b : ℝ) ^ 2) from
    (Finset.mul_prod_erase s _ ha').symm]
  field_simp


/-- Cancellation-free form of the positive weighted rational kernel. -/
theorem resolvedKernel_eq_weighted (p : Real.Parameters) (i j : ℕ) {y : ℝ}
    (hy : 0 < y) :
    resolvedKernel p i j y * density p.k y =
      y ^ (2 * (i + j)) * ConcreteMoment.weightedDensity p y := by
  rw [resolvedKernel_eq_fraction p i j hy]
  unfold ConcreteMoment.weightedDensity
  simp only [Real.numerator, Real.evalQ, Real.realPolynomial, Polynomial.map_mul,
    Polynomial.map_pow, Polynomial.map_X, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_X, ← pow_mul]
  ring

/-- Equation (3.2) for the actual pencil, with the pole integral discharged. -/
theorem gram_eq_weighted_integral (p : Real.Parameters) (hp : Real.Admissible p)
    (i j : Fin p.h) :
    Real.gram p (Real.zeta p.weight) i j =
      ∫ y : ℝ in Ioi 0, y ^ (2 * (i.val + j.val)) *
        ConcreteMoment.weightedDensity p y := by
  rw [gram_eq_resolvedKernel_integral p (poleIntegralIdentity p.k hp.k_pos) i j]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro y hy
  exact resolvedKernel_eq_weighted p i.val j.val hy


/-- The constructed measure has exactly the uncanceled weight of (3.2). -/
theorem weightedDensity_eq_paper (p : Real.Parameters) (hp : Real.Admissible p)
    {y : ℝ} (hy : 0 < y) :
    ConcreteMoment.weightedDensity p y =
      Real.evalQ (Real.D p.N) (y ^ 2) ^ (2 * p.m) /
        Real.evalQ (Real.D p.K) (y ^ 2) * density p.k y := by
  have hN : Real.evalQ (Real.D p.N) (y ^ 2) ≠ 0 :=
    ne_of_gt (ConcreteMoment.evalQ_D_pos p.N (by positivity))
  have hT : Real.evalQ (Real.tailD p) (y ^ 2) ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le zero_lt_one
      (ConcreteMoment.evalQ_tailD_ge_one p (sq_nonneg y)))
  have hfac : Real.evalQ (Real.D p.K) (y ^ 2) =
      Real.evalQ (Real.D p.N) (y ^ 2) * Real.evalQ (Real.tailD p) (y ^ 2) := by
    rw [Real.D_factorization p hp.N_lt_K.le]
    simp [Real.evalQ, Real.realPolynomial]
  have hexp : 2 * p.m = (2 * p.m - 1) + 1 := by have h := hp.m_pos; omega
  unfold ConcreteMoment.weightedDensity
  rw [hfac]
  simp only [Real.evalQ, Real.realPolynomial, Polynomial.map_pow, Polynomial.eval_pow]
  conv_rhs => rw [hexp, pow_succ]
  change Real.evalQ (Real.D p.N) (y ^ 2) ^ (2 * p.m - 1) /
      Real.evalQ (Real.tailD p) (y ^ 2) * density p.k y =
    (Real.evalQ (Real.D p.N) (y ^ 2) ^ (2 * p.m - 1) *
      Real.evalQ (Real.D p.N) (y ^ 2)) /
      (Real.evalQ (Real.D p.N) (y ^ 2) * Real.evalQ (Real.tailD p) (y ^ 2)) * density p.k y
  field_simp

/-- Equation (3.2) in its original, uncanceled `D_N^(2m)/D_K` form. -/
theorem gram_eq_paper_integral (p : Real.Parameters) (hp : Real.Admissible p)
    (i j : Fin p.h) :
    Real.gram p (Real.zeta p.weight) i j =
      ∫ y : ℝ in Ioi 0, y ^ (2 * (i.val + j.val)) *
        (Real.evalQ (Real.D p.N) (y ^ 2) ^ (2 * p.m) /
          Real.evalQ (Real.D p.K) (y ^ 2) * density p.k y) := by
  rw [gram_eq_weighted_integral p hp i j]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro y hy
  dsimp only
  rw [weightedDensity_eq_paper p hp hy]

end ManuscriptChain.Hyperbolic
