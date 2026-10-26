import Mathlib

/-!
# Complete real-rooted Turán and normalized Newton hierarchy

Adapted from the companion zetahyperbolic-axiom branch's general proofs in
HigherDerivativeTuran, NormalizedNewton, ConsecutiveDerivativeZeros,
DerivativeDistinctRoots, StrictCenteredLaguerre, StrictLaguerreGeneral,
and StrictNormalizedNewton. Every theorem is rechecked in this project.
This module has no project-specific spectral assumptions: its hypotheses
are real splitting and, for strict Newton, two distinct roots.
-/
noncomputable section
open Polynomial Filter
open scoped BigOperators Topology

namespace ManuscriptChain.NewtonTuran.Core



/-- The actual first-derivative Turan/Laguerre expression of a real polynomial. -/
def turan (P : ℝ[X]) (x : ℝ) : ℝ :=
  ((Polynomial.derivative P).eval x) ^ 2 -
    P.eval x * ((Polynomial.derivative (Polynomial.derivative P)).eval x)

/-- Exact affine multiplication identity, valid for ALL real polynomials. -/
theorem turan_mul_linear (P L : ℝ[X]) (a x : ℝ)
    (hL : Polynomial.derivative L = Polynomial.C a) :
    turan (L * P) x =
      (L.eval x) ^ 2 * turan P x + a ^ 2 * (P.eval x) ^ 2 := by
  have hfirst : Polynomial.derivative (L * P) =
      Polynomial.C a * P + L * Polynomial.derivative P := by
    rw [Polynomial.derivative_mul, hL]
  have hsecond :
      Polynomial.derivative (Polynomial.derivative (L * P)) =
        (2 : ℝ[X]) * Polynomial.C a * Polynomial.derivative P +
          L * Polynomial.derivative (Polynomial.derivative P) := by
    rw [hfirst]
    simp only [Polynomial.derivative_add, Polynomial.derivative_mul,
      Polynomial.derivative_C, hL, zero_mul, zero_add]
    ring
  unfold turan
  rw [hsecond, hfirst]
  simp [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C] <;> ring

/-- The affine X-factor has constant formal derivative. -/
theorem affine_derivative (a b : ℝ) :
    Polynomial.derivative
      (Polynomial.C a * (Polynomial.X : ℝ[X]) + Polynomial.C b) =
        Polynomial.C a := by
  rw [Polynomial.derivative_add, Polynomial.derivative_C_mul_X,
    Polynomial.derivative_C, add_zero]

/-- Universal exact recurrence for products of linear real factors. -/
theorem turan_mul_affine (P : ℝ[X]) (a b x : ℝ) :
    turan ((Polynomial.C a * (Polynomial.X : ℝ[X]) + Polynomial.C b) * P) x =
      (a * x + b) ^ 2 * turan P x + a ^ 2 * (P.eval x) ^ 2 := by
  rw [turan_mul_linear P _ a x (affine_derivative a b)]
  simp only [Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X] <;> ring

/-- Real scalar multiplication preserves the Turan inequality, even for
negative or vanishing scale. -/
theorem turan_const_mul (P : ℝ[X]) (c x : ℝ) :
    turan (Polynomial.C c * P) x = c ^ 2 * turan P x := by
  simpa using (turan_mul_linear P (Polynomial.C c) 0 x (by simp))


theorem turan_eq_zero_iff_multiple_zero (P : ℝ[X]) (x : ℝ)
    (hstrict : P.eval x ≠ 0 → 0 < turan P x) :
    turan P x = 0 ↔ P.eval x = 0 ∧ (Polynomial.derivative P).eval x = 0 := by
  constructor
  · intro hz
    have hp : P.eval x = 0 := by
      by_contra hne
      exact (ne_of_gt (hstrict hne)) hz
    have hs : ((Polynomial.derivative P).eval x) ^ 2 = 0 := by
      simpa only [turan, hp, zero_mul, sub_zero] using hz
    exact ⟨hp, eq_zero_of_pow_eq_zero hs⟩
  · rintro ⟨hp, hd⟩
    simp [turan, hp, hd]



end ManuscriptChain.NewtonTuran.Core


namespace ManuscriptChain.NewtonTuran.HigherDerivativeTuran


open ManuscriptChain.NewtonTuran.Core
open ManuscriptChain.NewtonTuran.Core

/-- Rolle's multiplicity count proves derivative closure over the real field. -/
theorem real_splits_derivative {P : ℝ[X]} (hP : P.Splits) : P.derivative.Splits := by
  by_cases hd : P.natDegree = 0
  · rw [Polynomial.derivative_of_natDegree_zero hd]
    exact Polynomial.Splits.zero
  · apply Polynomial.splits_iff_card_roots.mpr
    have hroots := Polynomial.card_roots_le_derivative P
    have hupper := Polynomial.card_roots' P.derivative
    have hcount := hP.natDegree_eq_card_roots
    have hdegree := Polynomial.natDegree_derivative P
    omega

/-- Every formal derivative, including the eventual zero polynomial, splits. -/
theorem real_splits_iterated_derivative {P : ℝ[X]} (hP : P.Splits) (k : ℕ) :
    (Polynomial.derivative^[k] P).Splits := by
  induction k with
  | zero => simpa using hP
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact real_splits_derivative ih

/-- The exact degree law for iterated derivatives in characteristic zero. -/
theorem iterated_derivative_natDegree (P : ℝ[X]) (k : ℕ) :
    (Polynomial.derivative^[k] P).natDegree = P.natDegree - k := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply', Polynomial.natDegree_derivative, ih]
      omega

private def rootProduct (r : Multiset ℝ) : ℝ[X] :=
  (r.map (fun a => (X : ℝ[X]) - C a)).prod

private theorem rootProduct_cons (a : ℝ) (r : Multiset ℝ) :
    rootProduct (a ::ₘ r) = (X - C a) * rootProduct r := by
  simp [rootProduct]

private theorem rootProduct_turan_cons (a : ℝ) (r : Multiset ℝ) (x : ℝ) :
    turan (rootProduct (a ::ₘ r)) x =
      (x - a) ^ 2 * turan (rootProduct r) x + ((rootProduct r).eval x) ^ 2 := by
  rw [rootProduct_cons,
    turan_mul_linear (rootProduct r) (X - C a) 1 x (by simp)]
  simp

private theorem rootProduct_turan_nonnegative (r : Multiset ℝ) (x : ℝ) :
    0 ≤ turan (rootProduct r) x := by
  induction r using Multiset.induction_on with
  | empty => simp [rootProduct, turan]
  | cons a r ih =>
      rw [rootProduct_turan_cons]
      exact add_nonneg (mul_nonneg (sq_nonneg _) ih) (sq_nonneg _)

private theorem rootProduct_turan_strict (r : Multiset ℝ) (hr : r ≠ 0)
    (x : ℝ) (hx : (rootProduct r).eval x ≠ 0) :
    0 < turan (rootProduct r) x := by
  induction r using Multiset.induction_on with
  | empty => exact (hr rfl).elim
  | cons a r ih =>
      have hvalue : (rootProduct r).eval x ≠ 0 := by
        rw [rootProduct_cons, Polynomial.eval_mul] at hx
        exact (mul_ne_zero_iff.mp hx).2
      rw [rootProduct_turan_cons]
      exact add_pos_of_nonneg_of_pos
        (mul_nonneg (sq_nonneg _) (rootProduct_turan_nonnegative r x))
        (sq_pos_of_ne_zero hvalue)

/-- Every real-split polynomial satisfies the global first Turan inequality. -/
theorem turan_nonnegative_of_real_splits {P : ℝ[X]} (hP : P.Splits) (x : ℝ) :
    0 ≤ turan P x := by
  rw [hP.eq_prod_roots, turan_const_mul]
  exact mul_nonneg (sq_nonneg _) (rootProduct_turan_nonnegative P.roots x)

/-- Positive degree gives strictness wherever a real-split polynomial is nonzero. -/
theorem turan_strict_of_real_splits {P : ℝ[X]} (hP : P.Splits)
    (hd : 0 < P.natDegree) (x : ℝ) (hx : P.eval x ≠ 0) :
    0 < turan P x := by
  have hp0 : P ≠ 0 := by
    intro hz
    simp [hz] at hd
  have hc : P.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hp0
  have hr : P.roots ≠ 0 := hP.roots_ne_zero (Nat.ne_of_gt hd)
  have hprod : (rootProduct P.roots).eval x ≠ 0 := by
    rw [hP.eq_prod_roots, Polynomial.eval_mul, Polynomial.eval_C] at hx
    exact (mul_ne_zero_iff.mp hx).2
  rw [hP.eq_prod_roots, turan_const_mul]
  exact mul_pos (sq_pos_of_ne_zero hc) (rootProduct_turan_strict P.roots hr x hprod)

/-- All derivative orders satisfy Turan, with no degree or nonvanishing input. -/
theorem iterated_turan_nonnegative {P : ℝ[X]} (hP : P.Splits) (k : ℕ) (x : ℝ) :
    0 ≤ turan (Polynomial.derivative^[k] P) x :=
  turan_nonnegative_of_real_splits (real_splits_iterated_derivative hP k) x

/-- Strictness through the last nonconstant derivative, at every non-root. -/
theorem iterated_turan_strict {P : ℝ[X]} (hP : P.Splits) (k : ℕ)
    (hk : k < P.natDegree) (x : ℝ)
    (hx : (Polynomial.derivative^[k] P).eval x ≠ 0) :
    0 < turan (Polynomial.derivative^[k] P) x := by
  apply turan_strict_of_real_splits (real_splits_iterated_derivative hP k) _ x hx
  rw [iterated_derivative_natDegree]
  exact Nat.sub_pos_of_lt hk

/-- At each nonconstant derivative, equality means a multiple real zero. -/
theorem iterated_turan_eq_zero_iff {P : ℝ[X]} (hP : P.Splits)
    (k : ℕ) (hk : k < P.natDegree) (x : ℝ) :
    turan (Polynomial.derivative^[k] P) x = 0 ↔
      (Polynomial.derivative^[k] P).eval x = 0 ∧
      (Polynomial.derivative (Polynomial.derivative^[k] P)).eval x = 0 :=
  turan_eq_zero_iff_multiple_zero _ x (iterated_turan_strict hP k hk x)


end ManuscriptChain.NewtonTuran.HigherDerivativeTuran


namespace ManuscriptChain.NewtonTuran.NormalizedNewton


open HigherDerivativeTuran

/-- The degree-normalized Laguerre expression. Its parameter is the
degree, not a freely chosen upper bound. -/
def laguerre (n : ℕ) (P : ℝ[X]) (x : ℝ) : ℝ :=
  ((n : ℝ) - 1) * (P.derivative.eval x) ^ 2 -
    (n : ℝ) * P.eval x * (P.derivative.derivative.eval x)

private theorem laguerre_const_mul (n : ℕ) (P : ℝ[X]) (c x : ℝ) :
    laguerre n (C c * P) x = c ^ 2 * laguerre n P x := by
  simp only [laguerre, Polynomial.derivative_C_mul, Polynomial.eval_mul,
    Polynomial.eval_C]
  ring

/-- A sum-of-squares recurrence for adjoining one real root. -/
theorem laguerre_mul_root_identity (m : ℕ) (P : ℝ[X]) (a x : ℝ) :
    (m : ℝ) * laguerre (m + 1) ((X - C a) * P) x =
      ((m : ℝ) + 1) * (x - a) ^ 2 * laguerre m P x +
        ((x - a) * P.derivative.eval x - (m : ℝ) * P.eval x) ^ 2 := by
  have hfirst : (((X - C a) * P) : ℝ[X]).derivative =
      P + (X - C a) * P.derivative := by simp
  have hsecond : (((X - C a) * P) : ℝ[X]).derivative.derivative =
      2 * P.derivative + (X - C a) * P.derivative.derivative := by
    rw [hfirst]
    simp only [Polynomial.derivative_add, Polynomial.derivative_mul,
      Polynomial.derivative_sub, Polynomial.derivative_X,
      Polynomial.derivative_C, sub_zero, one_mul]
    ring
  unfold laguerre
  rw [hsecond, hfirst]
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_sub,
    Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_ofNat, Nat.cast_add,
    Nat.cast_one]
  ring

private def rootsProduct (r : Multiset ℝ) : ℝ[X] :=
  (r.map (fun a => (X : ℝ[X]) - C a)).prod

private theorem rootsProduct_cons (a : ℝ) (r : Multiset ℝ) :
    rootsProduct (a ::ₘ r) = (X - C a) * rootsProduct r := by
  simp [rootsProduct]

private theorem laguerre_roots_nonnegative (r : Multiset ℝ) (x : ℝ) :
    0 ≤ laguerre r.card (rootsProduct r) x := by
  induction r using Multiset.induction_on with
  | empty => simp [rootsProduct, laguerre]
  | cons a r ih =>
      by_cases hr : r = 0
      · subst r
        simp [rootsProduct, laguerre]
      · have hm : 0 < (r.card : ℝ) := by
          exact_mod_cast (Multiset.card_pos.mpr hr)
        have hid := laguerre_mul_root_identity r.card (rootsProduct r) a x
        have hnonneg : 0 ≤ (r.card : ℝ) *
            laguerre (r.card + 1) ((X - C a) * rootsProduct r) x := by
          rw [hid]
          exact add_nonneg (mul_nonneg (mul_nonneg (by positivity) (sq_nonneg _)) ih)
            (sq_nonneg _)
        have hresult := nonneg_of_mul_nonneg_right hnonneg hm
        simpa only [Multiset.card_cons, rootsProduct_cons] using hresult

/-- The sharpened global Laguerre inequality for every real-rooted polynomial. -/
theorem laguerre_nonnegative_of_real_splits {P : ℝ[X]} (hP : P.Splits) (x : ℝ) :
    0 ≤ laguerre P.natDegree P x := by
  have heq : laguerre P.natDegree P x =
      P.leadingCoeff ^ 2 * laguerre P.roots.card (rootsProduct P.roots) x := by
    conv_lhs => arg 2; rw [hP.eq_prod_roots]
    rw [laguerre_const_mul, hP.natDegree_eq_card_roots]
    rfl
  rw [heq]
  exact mul_nonneg (sq_nonneg _) (laguerre_roots_nonnegative P.roots x)

/-- Formal-derivative value divided by the falling factorial of the degree.
At zero this is the ordinary coefficient divided by its binomial weight. -/
def normalizedJet (P : ℝ[X]) (n k : ℕ) (x : ℝ) : ℝ :=
  (Polynomial.derivative^[k] P).eval x / (n.descFactorial k : ℝ)

private theorem normalize_laguerre (A B C d f : ℝ) (hd : 1 < d) (hf : 0 < f)
    (h : 0 ≤ (d - 1) * B ^ 2 - d * A * C) :
    A / f * (C / ((d - 1) * d * f)) ≤ (B / (d * f)) ^ 2 := by
  have hd0 : d ≠ 0 := ne_of_gt (lt_trans zero_lt_one hd)
  have hd1 : d - 1 ≠ 0 := ne_of_gt (sub_pos.mpr hd)
  have hf0 : f ≠ 0 := ne_of_gt hf
  have heq : (B / (d * f)) ^ 2 - A / f * (C / ((d - 1) * d * f)) =
      ((d - 1) * B ^ 2 - d * A * C) / ((d - 1) * d ^ 2 * f ^ 2) := by
    field_simp [hd0, hd1, hf0]
  have hquot : 0 ≤ ((d - 1) * B ^ 2 - d * A * C) /
      ((d - 1) * d ^ 2 * f ^ 2) := div_nonneg h (by positivity)
  rw [← heq] at hquot
  linarith

/-- Full degree-normalized derivative Newton hierarchy, at every real point. -/
theorem normalizedJet_newton {P : ℝ[X]} (hP : P.Splits) (k : ℕ)
    (hk : k + 2 ≤ P.natDegree) (x : ℝ) :
    normalizedJet P P.natDegree k x * normalizedJet P P.natDegree (k + 2) x ≤
      normalizedJet P P.natDegree (k + 1) x ^ 2 := by
  let n := P.natDegree
  have hkn : k ≤ n := by dsimp [n]; omega
  have hdn : 2 ≤ n - k := by dsimp [n]; omega
  have hd : 1 < ((n - k : ℕ) : ℝ) := by
    exact_mod_cast (show 1 < n - k by omega)
  have hf : 0 < (n.descFactorial k : ℝ) := by
    exact_mod_cast (Nat.descFactorial_pos.mpr hkn)
  have hdsub : ((n - (k + 1) : ℕ) : ℝ) = ((n - k : ℕ) : ℝ) - 1 := by
    have heq : n - (k + 1) + 1 = n - k := by omega
    have heqr : ((n - (k + 1) : ℕ) : ℝ) + 1 = ((n - k : ℕ) : ℝ) := by
      exact_mod_cast heq
    linarith
  have hfac1 : (n.descFactorial (k + 1) : ℝ) =
      ((n - k : ℕ) : ℝ) * (n.descFactorial k : ℝ) := by
    simp only [Nat.descFactorial_succ, Nat.cast_mul]
  have hfac2 : (n.descFactorial (k + 2) : ℝ) =
      (((n - k : ℕ) : ℝ) - 1) * ((n - k : ℕ) : ℝ) *
        (n.descFactorial k : ℝ) := by
    rw [show k + 2 = (k + 1) + 1 by omega, Nat.descFactorial_succ, Nat.cast_mul,
      hfac1, hdsub]
    ring
  have hlag := laguerre_nonnegative_of_real_splits
    (real_splits_iterated_derivative hP k) x
  rw [laguerre, iterated_derivative_natDegree] at hlag
  have h := normalize_laguerre
    ((Polynomial.derivative^[k] P).eval x)
    ((Polynomial.derivative^[k + 1] P).eval x)
    ((Polynomial.derivative^[k + 2] P).eval x)
    ((n - k : ℕ) : ℝ) (n.descFactorial k : ℝ) hd hf
    (by simpa only [Function.iterate_succ_apply'] using hlag)
  change normalizedJet P n k x * normalizedJet P n (k + 2) x ≤
    normalizedJet P n (k + 1) x ^ 2
  simpa only [normalizedJet, hfac1, hfac2] using h

theorem normalizedJet_zero (P : ℝ[X]) (n k : ℕ) (hk : k ≤ n) :
    normalizedJet P n k 0 = P.coeff k / (n.choose k : ℝ) := by
  unfold normalizedJet
  rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_iterate_derivative]
  simp only [zero_add, Nat.descFactorial_self, nsmul_eq_mul]
  rw [Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul]
  have hf : (k.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
  have hc : (n.choose k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.choose_ne_zero hk)
  field_simp [hf, hc]

/-- The complete binomial-normalized coefficient inequalities. This remains
valid for mixed-sign coefficients; it does not assert strictness. -/
theorem coefficient_newton {P : ℝ[X]} (hP : P.Splits) (k : ℕ)
    (hk : k + 2 ≤ P.natDegree) :
    (P.coeff k / (P.natDegree.choose k : ℝ)) *
      (P.coeff (k + 2) / (P.natDegree.choose (k + 2) : ℝ)) ≤
        (P.coeff (k + 1) / (P.natDegree.choose (k + 1) : ℝ)) ^ 2 := by
  have h := normalizedJet_newton hP k hk 0
  rw [normalizedJet_zero P P.natDegree k (by omega),
    normalizedJet_zero P P.natDegree (k + 1) (by omega),
    normalizedJet_zero P P.natDegree (k + 2) hk] at h
  exact h

/-- The same normalized Newton hierarchy after every real translation. -/
theorem shifted_coefficient_newton {P : ℝ[X]} (hP : P.Splits) (a : ℝ) (k : ℕ)
    (hk : k + 2 ≤ P.natDegree) :
    ((P.taylor a).coeff k / (P.natDegree.choose k : ℝ)) *
      ((P.taylor a).coeff (k + 2) / (P.natDegree.choose (k + 2) : ℝ)) ≤
        ((P.taylor a).coeff (k + 1) / (P.natDegree.choose (k + 1) : ℝ)) ^ 2 := by
  have hs : (P.taylor a).Splits := hP.comp_X_add_C a
  simpa only [Polynomial.natDegree_taylor] using
    coefficient_newton hs k (by simpa only [Polynomial.natDegree_taylor] using hk)

/-- Newton is homogeneous of degree two, so division of every shifted
coefficient by the polynomial's center value preserves the inequality. -/
theorem normalized_shifted_newton {P : ℝ[X]} (hP : P.Splits) (a : ℝ) (k : ℕ)
    (hk : k + 2 ≤ P.natDegree) :
    (((P.taylor a).coeff k / P.eval a) / (P.natDegree.choose k : ℝ)) *
      (((P.taylor a).coeff (k + 2) / P.eval a) /
        (P.natDegree.choose (k + 2) : ℝ)) ≤
      (((P.taylor a).coeff (k + 1) / P.eval a) /
        (P.natDegree.choose (k + 1) : ℝ)) ^ 2 := by
  have h := mul_le_mul_of_nonneg_left (shifted_coefficient_newton hP a k hk)
    (sq_nonneg ((P.eval a)⁻¹))
  simpa only [div_eq_mul_inv, pow_two, mul_assoc, mul_left_comm, mul_comm] using h


end ManuscriptChain.NewtonTuran.NormalizedNewton


namespace ManuscriptChain.NewtonTuran.ConsecutiveDerivativeZeros


open ManuscriptChain.NewtonTuran.HigherDerivativeTuran
open ManuscriptChain.NewtonTuran.Core

theorem consecutive_derivative_zeros_force_root {P : ℝ[X]} (hP : P.Splits)
    (k : ℕ) (hk : k < P.natDegree) (x : ℝ)
    (hzero : (Polynomial.derivative^[k] P).eval x = 0)
    (hnext : (Polynomial.derivative^[k + 1] P).eval x = 0) : P.eval x = 0 := by
  induction k with
  | zero => simpa only [Function.iterate_zero, id_eq] using hzero
  | succ k ih =>
      have hk' : k < P.natDegree := by omega
      have htur : turan (Polynomial.derivative^[k] P) x = 0 := by
        have h1 : (Polynomial.derivative (Polynomial.derivative^[k] P)).eval x = 0 := by
          simpa only [Function.iterate_succ_apply'] using hzero
        have h2 : (Polynomial.derivative (Polynomial.derivative
            (Polynomial.derivative^[k] P))).eval x = 0 := by
          simpa only [Function.iterate_succ_apply'] using hnext
        simp only [turan, h1, h2, zero_pow (by decide : 2 ≠ 0), mul_zero, sub_zero]
      have hprev := ((iterated_turan_eq_zero_iff hP k hk' x).mp htur).1
      exact ih hk' hprev hzero

theorem consecutive_derivative_nonvanishing {P : ℝ[X]} (hP : P.Splits)
    (k : ℕ) (hk : k < P.natDegree) (x : ℝ) (hx : P.eval x ≠ 0) :
    (Polynomial.derivative^[k] P).eval x ≠ 0 ∨
      (Polynomial.derivative^[k + 1] P).eval x ≠ 0 := by
  by_contra hh
  push Not at hh
  exact hx (consecutive_derivative_zeros_force_root hP k hk x hh.1 hh.2)

/-- At every non-root, consecutive Taylor coefficients cannot both vanish. -/
theorem consecutive_taylor_nonvanishing {P : ℝ[X]} (hP : P.Splits)
    (k : ℕ) (hk : k < P.natDegree) (x : ℝ) (hx : P.eval x ≠ 0) :
    (P.taylor x).coeff k ≠ 0 ∨ (P.taylor x).coeff (k + 1) ≠ 0 := by
  have hs : (P.taylor x).Splits := hP.comp_X_add_C x
  have hh := consecutive_derivative_nonvanishing hs k
    (by simpa only [Polynomial.natDegree_taylor] using hk) 0
    (by simpa [Polynomial.taylor_apply, Polynomial.eval_comp] using hx)
  have hv (j : ℕ) : (Polynomial.derivative^[j] (P.taylor x)).eval 0 =
      (j.factorial : ℝ) * (P.taylor x).coeff j := by
    rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_iterate_derivative]
    simp only [zero_add, Nat.descFactorial_self, nsmul_eq_mul]
  rcases hh with hh | hh
  · exact Or.inl (fun heq => hh (by rw [hv k, heq, mul_zero]))
  · exact Or.inr (fun heq => hh (by rw [hv (k + 1), heq, mul_zero]))


end ManuscriptChain.NewtonTuran.ConsecutiveDerivativeZeros


namespace ManuscriptChain.NewtonTuran.ConsecutiveDerivativeZeros
theorem distinct_nonzero_roots_allow_zero_coefficient :
    ∃ P : ℝ[X], P.Splits ∧ P.eval 0 ≠ 0 ∧
      P.eval 1 = 0 ∧ P.eval (-1) = 0 ∧ (1 : ℝ) ≠ -1 ∧ P.coeff 1 = 0 := by
  refine ⟨(X - C 1) * (X - C (-1)),
    (Polynomial.Splits.X_sub_C 1).mul (Polynomial.Splits.X_sub_C (-1)), ?_⟩
  have heq : ((X - C 1) * (X - C (-1)) : ℝ[X]) = X ^ 2 - 1 := by
    simp only [C_neg, C_1]
    ring
  rw [heq]
  norm_num [Polynomial.coeff_sub, Polynomial.coeff_one]


end ManuscriptChain.NewtonTuran.ConsecutiveDerivativeZeros


namespace ManuscriptChain.NewtonTuran.DerivativeDistinctRoots


open ManuscriptChain.NewtonTuran.HigherDerivativeTuran
open ManuscriptChain.NewtonTuran.ConsecutiveDerivativeZeros

def HasDistinctRoots (P : ℝ[X]) : Prop :=
  ∃ a b : ℝ, P.IsRoot a ∧ P.IsRoot b ∧ a ≠ b

theorem derivative_hasDistinctRoots {P : ℝ[X]} (hP : P.Splits)
    (hd : 3 ≤ P.natDegree) (hdist : HasDistinctRoots P) :
    HasDistinctRoots P.derivative := by
  classical
  by_contra hnot
  have hone : ∀ a b : ℝ, P.derivative.IsRoot a → P.derivative.IsRoot b → a = b := by
    intro a b ha hb
    by_contra hab
    exact hnot ⟨a, b, ha, hb, hab⟩
  have hs := real_splits_derivative hP
  have hddeg : 2 ≤ P.derivative.natDegree := by
    rw [Polynomial.natDegree_derivative]
    omega
  have hdne : P.derivative ≠ 0 := by
    intro hz
    simp [hz] at hddeg
  have hpne : P ≠ 0 := by
    intro hz
    simp [hz] at hd
  obtain ⟨a, ha⟩ := Multiset.exists_mem_of_ne_zero
    (hs.roots_ne_zero (by omega))
  have haroot : P.derivative.IsRoot a := (Polynomial.mem_roots hdne).mp ha
  have hcount : P.derivative.roots.count a = P.derivative.roots.card :=
    Multiset.count_eq_card.mpr (fun b hb => hone a b haroot ((Polynomial.mem_roots hdne).mp hb))
  have hmult : P.derivative.rootMultiplicity a = P.derivative.natDegree := by
    simpa only [Polynomial.count_roots, ← hs.natDegree_eq_card_roots] using hcount
  have hdouble : P.derivative.derivative.IsRoot a := by
    have hm : 1 < P.derivative.rootMultiplicity a := by omega
    simpa only [Function.iterate_one] using
      (Polynomial.isRoot_iterate_derivative_of_lt_rootMultiplicity (n := 1) hm)
  have hpa : P.IsRoot a := by
    apply consecutive_derivative_zeros_force_root hP 1 (by omega) a
    · simpa only [Function.iterate_one, Polynomial.IsRoot.def] using haroot
    · simpa only [Function.iterate_succ_apply', Function.iterate_zero, id_eq, Polynomial.IsRoot.def] using hdouble
  have hpmult : P.rootMultiplicity a = P.natDegree := by
    rw [Polynomial.derivative_rootMultiplicity_of_root hpa,
      Polynomial.natDegree_derivative] at hmult
    omega
  have hall : ∀ b ∈ P.roots, a = b := by
    apply Multiset.count_eq_card.mp
    rw [Polynomial.count_roots, hpmult, hP.natDegree_eq_card_roots]
  obtain ⟨b, c, hb, hc, hbc⟩ := hdist
  exact hbc ((hall b ((Polynomial.mem_roots hpne).mpr hb)).symm.trans
    (hall c ((Polynomial.mem_roots hpne).mpr hc)))

/-- Every iterated derivative still of degree at least two has distinct roots. -/
theorem iterated_derivative_hasDistinctRoots {P : ℝ[X]} (hP : P.Splits)
    (hdist : HasDistinctRoots P) (k : ℕ) (hk : k + 2 ≤ P.natDegree) :
    HasDistinctRoots (Polynomial.derivative^[k] P) := by
  induction k with
  | zero => simpa only [Function.iterate_zero, id_eq] using hdist
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      apply derivative_hasDistinctRoots (real_splits_iterated_derivative hP k)
      · rw [iterated_derivative_natDegree]
        omega
      · exact ih (by omega)


end ManuscriptChain.NewtonTuran.DerivativeDistinctRoots


namespace ManuscriptChain.NewtonTuran.Dispersion


def dispersion {n : ℕ} (v : Fin n → ℝ) : ℝ :=
  (n : ℝ) * (∑ i, v i ^ 2) - (∑ i, v i) ^ 2

theorem pairwise_square_identity {n : ℕ} (v : Fin n → ℝ) :
    (∑ i, ∑ j, (v i - v j) ^ 2) = 2 * dispersion v := by
  simp only [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_const, Finset.sum_mul, Finset.mul_sum]
  simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  simp only [← Finset.mul_sum, ← Finset.sum_mul]
  unfold dispersion
  ring

theorem dispersion_nonnegative {n : ℕ} (v : Fin n → ℝ) :
    0 ≤ dispersion v := by
  have h : 0 ≤ ∑ i, ∑ j, (v i - v j) ^ 2 :=
    Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => sq_nonneg _))
  rw [pairwise_square_identity] at h
  linarith

theorem dispersion_positive_of_distinct {n : ℕ} (v : Fin n → ℝ)
    (i j : Fin n) (hij : v i ≠ v j) : 0 < dispersion v := by
  have hsq : 0 < (v i - v j) ^ 2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hij)
  have hrow : (v i - v j) ^ 2 ≤ ∑ k, (v i - v k) ^ 2 :=
    Finset.single_le_sum (fun k _ => sq_nonneg (v i - v k)) (Finset.mem_univ j)
  have htotal : (∑ k, (v i - v k) ^ 2) ≤ ∑ l, ∑ k, (v l - v k) ^ 2 :=
    Finset.single_le_sum
      (fun l _ => Finset.sum_nonneg (fun k _ => sq_nonneg (v l - v k)))
      (Finset.mem_univ i)
  have h := lt_of_lt_of_le hsq (le_trans hrow htotal)
  rw [pairwise_square_identity] at h
  linarith

theorem dispersion_eq_zero_iff {n : ℕ} (v : Fin n → ℝ) :
    dispersion v = 0 ↔ ∀ i j, v i = v j := by
  constructor
  · intro hz i j
    by_contra hij
    have h := dispersion_positive_of_distinct v i j hij
    linarith
  · intro heq
    have h : (∑ i, ∑ j, (v i - v j) ^ 2) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      apply Finset.sum_eq_zero
      intro j _
      rw [heq i j, sub_self, zero_pow (by decide)]
    rw [pairwise_square_identity] at h
    linarith


end ManuscriptChain.NewtonTuran.Dispersion


namespace ManuscriptChain.NewtonTuran.StrictLaguerreGeneral


open ManuscriptChain.NewtonTuran.NormalizedNewton ManuscriptChain.NewtonTuran.Dispersion
open ManuscriptChain.NewtonTuran.DerivativeDistinctRoots

theorem factorized_logDeriv {n : ℕ} (P : ℝ[X]) (c : ℝ) (r : Fin n → ℝ)
    (hfac : P = C c * ∏ i, (X - C (r i))) (hc : c ≠ 0) (x : ℝ)
    (hx : P.eval x ≠ 0) :
    logDeriv (fun y : ℝ => P.eval y) x = ∑ i, (x - r i)⁻¹ := by
  have hvalue : (fun y : ℝ => P.eval y) =
      (fun y : ℝ => c * ∏ i, (y - r i)) := by
    funext y
    simp [hfac, Polynomial.eval_prod]
  have hprod : (∏ i, (x - r i)) ≠ 0 := by
    have hh := hx
    change (fun y : ℝ => P.eval y) x ≠ 0 at hh
    rw [hvalue] at hh
    exact (mul_ne_zero_iff.mp hh).2
  have hgap (i : Fin n) : x - r i ≠ 0 :=
    (Finset.prod_ne_zero_iff.mp hprod) i (Finset.mem_univ i)
  have hd (i : Fin n) : HasDerivAt (fun y : ℝ => y - r i) 1 x :=
    (hasDerivAt_id x).sub_const (r i)
  rw [hvalue, logDeriv_const_mul x _ hc,
    logDeriv_prod (fun i _ => hgap i) (fun i _ => (hd i).differentiableAt)]
  apply Finset.sum_congr rfl
  intro i _
  rw [logDeriv_apply, (hd i).deriv, one_div]

theorem real_logDeriv_hasDerivAt (P : ℝ[X]) (x : ℝ) (hx : P.eval x ≠ 0) :
    HasDerivAt (logDeriv (fun y : ℝ => P.eval y))
      ((P.derivative.derivative.eval x * P.eval x - P.derivative.eval x ^ 2) /
        P.eval x ^ 2) x := by
  have heq : logDeriv (fun y : ℝ => P.eval y) =
      (fun y : ℝ => P.derivative.eval y / P.eval y) := by
    funext y
    rw [logDeriv_apply, Polynomial.deriv]
  rw [heq]
  simpa only [pow_two] using
    (P.derivative.hasDerivAt x).fun_div (P.hasDerivAt x) hx

theorem factorized_laguerre_dispersion {n : ℕ} (P : ℝ[X]) (c : ℝ) (r : Fin n → ℝ)
    (hfac : P = C c * ∏ i, (X - C (r i))) (hc : c ≠ 0) (x : ℝ)
    (hx : P.eval x ≠ 0) :
    laguerre n P x = P.eval x ^ 2 * dispersion (fun i => (x - r i)⁻¹) := by
  have hgap (i : Fin n) : x - r i ≠ 0 := by
    intro hz
    apply hx
    have hprod : (∏ j, (x - r j)) = 0 := Finset.prod_eq_zero (Finset.mem_univ i) hz
    simpa [hfac, Polynomial.eval_prod] using congrArg (fun z : ℝ => c * z) hprod
  have hd (i : Fin n) : HasDerivAt (fun y : ℝ => (y - r i)⁻¹)
      (-((x - r i)⁻¹) ^ 2) x := by
    apply (((hasDerivAt_id x).sub_const (r i)).fun_inv (hgap i)).congr_deriv
    simp only [neg_div, one_div, inv_pow, id_eq]
  have hsum : HasDerivAt (fun y : ℝ => ∑ i, (y - r i)⁻¹)
      (-(∑ i, ((x - r i)⁻¹) ^ 2)) x := by
    simpa only [Finset.sum_neg_distrib] using
      HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => hd i)
  have hlog : HasDerivAt (logDeriv (fun y : ℝ => P.eval y))
      (-(∑ i, ((x - r i)⁻¹) ^ 2)) x := by
    apply hsum.congr_of_eventuallyEq
    have hevent := P.continuousAt.eventually_ne hx
    filter_upwards [hevent] with y hy
    exact factorized_logDeriv P c r hfac hc y hy
  have hsecond := hlog.unique (real_logDeriv_hasDerivAt P x hx)
  have hsecond' : (∑ i, ((x - r i)⁻¹) ^ 2) =
      (P.derivative.eval x ^ 2 - P.derivative.derivative.eval x * P.eval x) /
        P.eval x ^ 2 := by
    calc
      _ = -((P.derivative.derivative.eval x * P.eval x - P.derivative.eval x ^ 2) /
          P.eval x ^ 2) := by linarith [hsecond]
      _ = _ := by ring
  have hfirst := factorized_logDeriv P c r hfac hc x hx
  rw [logDeriv_apply, Polynomial.deriv] at hfirst
  unfold dispersion
  rw [← hfirst, hsecond']
  unfold laguerre
  field_simp [hx]
  <;> ring

/-- The exact generic off-root strictness theorem; no simplicity is assumed. -/
theorem laguerre_strict_of_distinct_roots {P : ℝ[X]} (hP : P.Splits)
    (hdist : HasDistinctRoots P) (x : ℝ) (hx : P.eval x ≠ 0) :
    0 < laguerre P.natDegree P x := by
  classical
  have hpne : P ≠ 0 := by intro hz; simp [hz] at hx
  let r : Fin P.roots.toList.length → ℝ := P.roots.toList.get
  have hprod : (∏ i, (X - C (r i))) =
      (P.roots.map (fun a : ℝ => (X : ℝ[X]) - C a)).prod := by
    calc
      (∏ i, (X - C (r i))) =
          (P.roots.toList.map (fun a : ℝ => (X : ℝ[X]) - C a)).prod := by
        rw [← Fin.prod_ofFn]
        congr 1
        dsimp only [r]
        simpa only [List.get_eq_getElem] using
          (List.ofFn_getElem_eq_map P.roots.toList (fun a : ℝ => (X : ℝ[X]) - C a))
      _ = _ := Multiset.prod_map_toList _ _
  have hfac : P = C P.leadingCoeff * ∏ i, (X - C (r i)) := by
    rw [hprod]
    exact hP.eq_prod_roots
  have hdegree : P.roots.toList.length = P.natDegree := by
    rw [Multiset.length_toList, ← hP.natDegree_eq_card_roots]
  rw [← hdegree, factorized_laguerre_dispersion P P.leadingCoeff r hfac
    (Polynomial.leadingCoeff_ne_zero.mpr hpne) x hx]
  apply mul_pos (sq_pos_of_ne_zero hx)
  obtain ⟨a, b, ha, hb, hab⟩ := hdist
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp
    (Multiset.mem_toList.mpr ((Polynomial.mem_roots hpne).mpr ha))
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp
    (Multiset.mem_toList.mpr ((Polynomial.mem_roots hpne).mpr hb))
  apply dispersion_positive_of_distinct _ i j
  intro hij
  have heq := inv_injective hij
  change x - P.roots.toList.get i = x - P.roots.toList.get j at heq
  rw [hi, hj] at heq
  exact hab (by linarith)


end ManuscriptChain.NewtonTuran.StrictLaguerreGeneral


namespace ManuscriptChain.NewtonTuran.StrictNormalizedNewton


open ManuscriptChain.NewtonTuran.HigherDerivativeTuran ManuscriptChain.NewtonTuran.NormalizedNewton
open ManuscriptChain.NewtonTuran.DerivativeDistinctRoots ManuscriptChain.NewtonTuran.ConsecutiveDerivativeZeros
open ManuscriptChain.NewtonTuran.StrictLaguerreGeneral

theorem laguerre_strict_iff {P : ℝ[X]} (hP : P.Splits) (hdist : HasDistinctRoots P)
    (hd : 2 ≤ P.natDegree) (x : ℝ) :
    0 < laguerre P.natDegree P x ↔ P.eval x ≠ 0 ∨ P.derivative.eval x ≠ 0 := by
  constructor
  · intro hh
    by_contra hz
    push Not at hz
    simp only [laguerre, hz.1, hz.2, zero_pow (by decide : 2 ≠ 0),
      mul_zero, zero_mul, sub_self, lt_self_iff_false] at hh
  · rintro (ha | hb)
    · exact laguerre_strict_of_distinct_roots hP hdist x ha
    · by_cases ha : P.eval x = 0
      · have hn : (1 : ℝ) < (P.natDegree : ℝ) := by exact_mod_cast (by omega : 1 < P.natDegree)
        simp only [laguerre, ha, mul_zero, zero_mul, sub_zero]
        exact mul_pos (sub_pos.mpr hn) (sq_pos_of_ne_zero hb)
      · exact laguerre_strict_of_distinct_roots hP hdist x ha

private theorem normalize_laguerre_strict (A B C d f : ℝ) (hd : 1 < d) (hf : 0 < f)
    (h : 0 < (d - 1) * B ^ 2 - d * A * C) :
    A / f * (C / ((d - 1) * d * f)) < (B / (d * f)) ^ 2 := by
  have hd0 : d ≠ 0 := ne_of_gt (lt_trans zero_lt_one hd)
  have hd1 : d - 1 ≠ 0 := ne_of_gt (sub_pos.mpr hd)
  have hf0 : f ≠ 0 := ne_of_gt hf
  have heq : (B / (d * f)) ^ 2 - A / f * (C / ((d - 1) * d * f)) =
      ((d - 1) * B ^ 2 - d * A * C) / ((d - 1) * d ^ 2 * f ^ 2) := by
    field_simp [hd0, hd1, hf0]
  have hquot : 0 < ((d - 1) * B ^ 2 - d * A * C) /
      ((d - 1) * d ^ 2 * f ^ 2) := div_pos h (by positivity)
  rw [← heq] at hquot
  linarith

theorem normalizedJet_newton_strict_of_pair {P : ℝ[X]} (hP : P.Splits)
    (hdist : HasDistinctRoots P) (k : ℕ) (hk : k + 2 ≤ P.natDegree) (x : ℝ)
    (hpair : (Polynomial.derivative^[k] P).eval x ≠ 0 ∨
      (Polynomial.derivative^[k + 1] P).eval x ≠ 0) :
    normalizedJet P P.natDegree k x * normalizedJet P P.natDegree (k + 2) x <
      normalizedJet P P.natDegree (k + 1) x ^ 2 := by
  let n := P.natDegree
  have hkn : k ≤ n := by dsimp [n]; omega
  have hdn : 2 ≤ n - k := by dsimp [n]; omega
  have hd : 1 < ((n - k : ℕ) : ℝ) := by exact_mod_cast (show 1 < n - k by omega)
  have hf : 0 < (n.descFactorial k : ℝ) := by exact_mod_cast (Nat.descFactorial_pos.mpr hkn)
  have hdsub : ((n - (k + 1) : ℕ) : ℝ) = ((n - k : ℕ) : ℝ) - 1 := by
    have heq : n - (k + 1) + 1 = n - k := by omega
    have heqr : ((n - (k + 1) : ℕ) : ℝ) + 1 = ((n - k : ℕ) : ℝ) := by exact_mod_cast heq
    linarith
  have hfac1 : (n.descFactorial (k + 1) : ℝ) =
      ((n - k : ℕ) : ℝ) * (n.descFactorial k : ℝ) := by
    simp only [Nat.descFactorial_succ, Nat.cast_mul]
  have hfac2 : (n.descFactorial (k + 2) : ℝ) =
      (((n - k : ℕ) : ℝ) - 1) * ((n - k : ℕ) : ℝ) * (n.descFactorial k : ℝ) := by
    rw [show k + 2 = (k + 1) + 1 by omega, Nat.descFactorial_succ,
      Nat.cast_mul, hfac1, hdsub]
    ring
  have hlag := (laguerre_strict_iff (real_splits_iterated_derivative hP k)
    (iterated_derivative_hasDistinctRoots hP hdist k hk)
    (by rw [iterated_derivative_natDegree]; exact hdn) x).mpr
      (by simpa only [Function.iterate_succ_apply'] using hpair)
  rw [laguerre, iterated_derivative_natDegree] at hlag
  have hh := normalize_laguerre_strict
    ((Polynomial.derivative^[k] P).eval x)
    ((Polynomial.derivative^[k + 1] P).eval x)
    ((Polynomial.derivative^[k + 2] P).eval x)
    ((n - k : ℕ) : ℝ) (n.descFactorial k : ℝ) hd hf
    (by simpa only [Function.iterate_succ_apply'] using hlag)
  change normalizedJet P n k x * normalizedJet P n (k + 2) x <
    normalizedJet P n (k + 1) x ^ 2
  simpa only [normalizedJet, hfac1, hfac2] using hh

theorem normalizedJet_newton_strict_iff {P : ℝ[X]} (hP : P.Splits)
    (hdist : HasDistinctRoots P) (k : ℕ) (hk : k + 2 ≤ P.natDegree) (x : ℝ) :
    normalizedJet P P.natDegree k x * normalizedJet P P.natDegree (k + 2) x <
        normalizedJet P P.natDegree (k + 1) x ^ 2 ↔
      (Polynomial.derivative^[k] P).eval x ≠ 0 ∨
        (Polynomial.derivative^[k + 1] P).eval x ≠ 0 := by
  constructor
  · intro hh
    by_contra hz
    push Not at hz
    simp only [normalizedJet, hz.1, hz.2, zero_div, zero_mul,
      zero_pow (by decide : 2 ≠ 0), lt_self_iff_false] at hh
  · exact normalizedJet_newton_strict_of_pair hP hdist k hk x

theorem coefficient_newton_strict_iff_pair {P : ℝ[X]} (hP : P.Splits)
    (hdist : HasDistinctRoots P) (k : ℕ) (hk : k + 2 ≤ P.natDegree) :
    (P.coeff k / (P.natDegree.choose k : ℝ)) *
        (P.coeff (k + 2) / (P.natDegree.choose (k + 2) : ℝ)) <
        (P.coeff (k + 1) / (P.natDegree.choose (k + 1) : ℝ)) ^ 2 ↔
      P.coeff k ≠ 0 ∨ P.coeff (k + 1) ≠ 0 := by
  have hh := normalizedJet_newton_strict_iff hP hdist k hk 0
  rw [normalizedJet_zero P P.natDegree k (by omega),
    normalizedJet_zero P P.natDegree (k + 1) (by omega),
    normalizedJet_zero P P.natDegree (k + 2) hk] at hh
  have hv (j : ℕ) : (Polynomial.derivative^[j] P).eval 0 =
      (j.factorial : ℝ) * P.coeff j := by
    rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_iterate_derivative]
    simp only [zero_add, Nat.descFactorial_self, nsmul_eq_mul]
  have hf0 : (k.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  have hf1 : ((k + 1).factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (k + 1)
  rw [hv k, hv (k + 1)] at hh
  constructor
  · intro h
    rcases hh.mp h with ha | hb
    · exact Or.inl (mul_ne_zero_iff.mp ha).2
    · exact Or.inr (mul_ne_zero_iff.mp hb).2
  · intro h
    apply hh.mpr
    rcases h with ha | hb
    · exact Or.inl (mul_ne_zero hf0 ha)
    · exact Or.inr (mul_ne_zero hf1 hb)

/-- Exactly the strictness condition printed in Theorem 3.7(2). -/
theorem coefficient_newton_strict_criterion {P : ℝ[X]} (hP : P.Splits)
    (hdist : HasDistinctRoots P) (k : ℕ) (hk : k + 2 ≤ P.natDegree) :
    (P.coeff k / (P.natDegree.choose k : ℝ)) *
        (P.coeff (k + 2) / (P.natDegree.choose (k + 2) : ℝ)) <
        (P.coeff (k + 1) / (P.natDegree.choose (k + 1) : ℝ)) ^ 2 ↔
      P.coeff (k + 1) ≠ 0 ∨ (P.coeff k ≠ 0 ∧ P.coeff (k + 2) ≠ 0) := by
  constructor
  · intro hh
    by_cases hb : P.coeff (k + 1) = 0
    · right
      constructor <;> intro hz <;>
        simp only [hz, hb, zero_div, zero_mul, mul_zero,
          zero_pow (by decide : 2 ≠ 0), lt_self_iff_false] at hh
    · exact Or.inl hb
  · rintro (hb | ⟨ha, _⟩)
    · exact (coefficient_newton_strict_iff_pair hP hdist k hk).mpr (Or.inr hb)
    · exact (coefficient_newton_strict_iff_pair hP hdist k hk).mpr (Or.inl ha)

theorem hasDistinctRoots_taylor {P : ℝ[X]} (hdist : HasDistinctRoots P) (x : ℝ) :
    HasDistinctRoots (P.taylor x) := by
  obtain ⟨a, b, ha, hb, hab⟩ := hdist
  refine ⟨a - x, b - x, ?_, ?_, ?_⟩
  · simpa only [Polynomial.IsRoot.def, Polynomial.taylor_apply, Polynomial.eval_comp,
      Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C, sub_add_cancel] using ha
  · simpa only [Polynomial.IsRoot.def, Polynomial.taylor_apply, Polynomial.eval_comp,
      Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C, sub_add_cancel] using hb
  · intro hh
    exact hab (by linarith)

/-- At a non-root center all shifted Newton inequalities are strict, even
if individual shifted coefficients vanish. -/
theorem shifted_coefficient_newton_strict {P : ℝ[X]} (hP : P.Splits)
    (hdist : HasDistinctRoots P) (x : ℝ) (hx : P.eval x ≠ 0)
    (k : ℕ) (hk : k + 2 ≤ P.natDegree) :
    ((P.taylor x).coeff k / (P.natDegree.choose k : ℝ)) *
        ((P.taylor x).coeff (k + 2) / (P.natDegree.choose (k + 2) : ℝ)) <
        ((P.taylor x).coeff (k + 1) / (P.natDegree.choose (k + 1) : ℝ)) ^ 2 := by
  have hs : (P.taylor x).Splits := hP.comp_X_add_C x
  have hh := (coefficient_newton_strict_iff_pair (P := P.taylor x) hs
    (hasDistinctRoots_taylor hdist x) k
    (by simpa only [Polynomial.natDegree_taylor] using hk)).mpr
      (consecutive_taylor_nonvanishing hP k (by omega) x hx)
  simpa only [Polynomial.natDegree_taylor] using hh

theorem normalized_shifted_newton_strict {P : ℝ[X]} (hP : P.Splits)
    (hdist : HasDistinctRoots P) (x : ℝ) (hx : P.eval x ≠ 0)
    (k : ℕ) (hk : k + 2 ≤ P.natDegree) :
    (((P.taylor x).coeff k / P.eval x) / (P.natDegree.choose k : ℝ)) *
        (((P.taylor x).coeff (k + 2) / P.eval x) /
          (P.natDegree.choose (k + 2) : ℝ)) <
      (((P.taylor x).coeff (k + 1) / P.eval x) /
        (P.natDegree.choose (k + 1) : ℝ)) ^ 2 := by
  have hh := mul_lt_mul_of_pos_left (shifted_coefficient_newton_strict hP hdist x hx k hk)
    (sq_pos_of_ne_zero (inv_ne_zero hx))
  simpa only [div_eq_mul_inv, pow_two, mul_assoc, mul_left_comm, mul_comm] using hh


end ManuscriptChain.NewtonTuran.StrictNormalizedNewton
