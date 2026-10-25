import Zetahyperbolic.Section3.NewtonTuran
import Zetahyperbolic.Section3.PrimitivePolynomial
import Zetahyperbolic.Section3.SpectralInertia

/-!
# Theorem 3.7 for the actual primitive integer polynomial

The real-split polynomial hierarchy is instantiated with the project's
constructed primitive normalization. The actual inertia count proves two
distinct roots whenever h ≥ 2; no genericity or simple-root premise is used.
-/
noncomputable section
open Polynomial
open scoped BigOperators

namespace ManuscriptChain.NewtonTuran.Actual

open HigherDerivativeTuran NormalizedNewton DerivativeDistinctRoots
open StrictNormalizedNewton ConsecutiveDerivativeZeros Core
theorem spectral_polynomial_splits {n : ℕ}
    {p : Spectral.SymmetricAffinePencil n} (h : Spectral.RootFactorization p) :
    p.detPolynomial.Splits := by
  rw [h.factorization]
  apply Polynomial.Splits.mul (Polynomial.Splits.C _)
  apply Polynomial.Splits.prod
  intro i _
  exact Polynomial.Splits.of_natDegree_eq_one
    (Spectral.natDegree_spectralFactor p.center (h.beta i) (h.beta_ne_zero i))

/-- Splitting is obtained from the constructed actual Gram/spectral proof. -/
theorem actual_determinant_splits (p : Real.Parameters) (hp : Real.Admissible p) :
    (Real.realPolynomial (Real.delta p)).Splits := by
  simpa only [Real.manuscriptPencil_detPolynomial] using
    spectral_polynomial_splits (General.factorization p (GRAM_POSITIVE p hp))


/-- The real image of the constructed primitive integer polynomial. -/
def primitiveRealPolynomial (p : Real.Parameters) : ℝ[X] :=
  (ManuscriptChain.primitivePolynomial p).map (Int.castRingHom ℝ)

theorem primitiveRealPolynomial_identity (p : Real.Parameters) :
    primitiveRealPolynomial p =
      C ((primitive p).scale : ℝ) * Real.realPolynomial (Real.delta p) := by
  have h := congrArg (Polynomial.map (Rat.castHom ℝ)) (primitive p).identity
  have hc : (Rat.castHom ℝ).comp (Int.castRingHom ℚ) = Int.castRingHom ℝ := by
    ext
    simp
  rw [Polynomial.map_map, hc] at h
  simpa only [Polynomial.map_mul, Polynomial.map_C, Rat.coe_castHom,
    primitiveRealPolynomial, primitivePolynomial, Real.realPolynomial] using h

theorem primitiveRealPolynomial_splits (p : Real.Parameters) (hp : Real.Admissible p) :
    (primitiveRealPolynomial p).Splits := by
  rw [primitiveRealPolynomial_identity]
  exact (actual_determinant_splits p hp).C_mul _

theorem primitiveRealPolynomial_natDegree (p : Real.Parameters) :
    (primitiveRealPolynomial p).natDegree = p.h := by
  rw [primitiveRealPolynomial,
    Polynomial.natDegree_map_eq_of_injective Int.cast_injective,
    ManuscriptChain.primitivePolynomial_natDegree]

theorem primitiveRealPolynomial_center_ne_zero (p : Real.Parameters)
    (hp : Real.Admissible p) :
    (primitiveRealPolynomial p).eval (Real.zeta p.weight) ≠ 0 := by
  rw [primitiveRealPolynomial_identity, Polynomial.eval_mul, Polynomial.eval_C]
  apply mul_ne_zero
  · exact_mod_cast (ne_of_gt (primitive p).scale_pos)
  · exact General.center_nonvanishing p (GRAM_POSITIVE p hp)

/-- The inertia theorem supplies a root on each side of the zeta center. -/
theorem actual_primitive_hasDistinctRoots
    (p : Real.Parameters) (hp : Real.Admissible p) (hh : 2 ≤ p.h) :
    HasDistinctRoots (primitiveRealPolynomial p) := by
  have hside := SpectralInertia.actual_root_side_formula p hp
  have hleft : 0 < {i : Fin p.h | Real.zeta p.weight -
      (Spectral.actualEigenvalues (Real.manuscriptPencil p) i)⁻¹ < Real.zeta p.weight}.ncard := by
    rw [hside.1]
    split_ifs <;> omega
  have hright : 0 < {i : Fin p.h | Real.zeta p.weight < Real.zeta p.weight -
      (Spectral.actualEigenvalues (Real.manuscriptPencil p) i)⁻¹}.ncard := by
    rw [hside.2]
    split_ifs <;> omega
  obtain ⟨i, hi⟩ := Set.ncard_pos.mp hleft
  obtain ⟨j, hj⟩ := Set.ncard_pos.mp hright
  let c := Spectral.actualRootFactorization (Real.manuscriptPencil p)
    (GRAM_POSITIVE p hp) (General.derivative_nonsingular p)
  have hroot (l : Fin p.h) : (primitiveRealPolynomial p).IsRoot (c.root l) := by
    change (primitiveRealPolynomial p).eval (c.root l) = 0
    rw [primitiveRealPolynomial_identity, Polynomial.eval_mul, Polynomial.eval_C]
    have he := c.eval_root l
    rw [Real.manuscriptPencil_detPolynomial] at he
    rw [he, mul_zero]
  refine ⟨c.root i, c.root j, hroot i, hroot j, ?_⟩
  change c.root i < Real.zeta p.weight at hi
  change Real.zeta p.weight < c.root j at hj
  exact ne_of_lt (hi.trans hj)
/-- Complete higher-derivative Turan nonnegativity for the actual integer
normalization. `k=m-1` is exactly the manuscript's T_m expression. -/
theorem actual_primitive_all_derivative_turan
    (p : Real.Parameters) (hp : Real.Admissible p) (k : ℕ) (x : ℝ) :
    0 ≤ turan (Polynomial.derivative^[k] (primitiveRealPolynomial p)) x :=
  iterated_turan_nonnegative (primitiveRealPolynomial_splits p hp) k x

/-- The strict clause of the higher-derivative Turan theorem holds off roots,
through all nonconstant derivative orders of the actual normalized polynomial. -/
theorem actual_primitive_all_derivative_turan_strict
    (p : Real.Parameters) (hp : Real.Admissible p) (k : ℕ) (hk : k < p.h)
    (x : ℝ) (hx : (Polynomial.derivative^[k] (primitiveRealPolynomial p)).eval x ≠ 0) :
    0 < turan (Polynomial.derivative^[k] (primitiveRealPolynomial p)) x := by
  apply iterated_turan_strict (primitiveRealPolynomial_splits p hp) k _ x hx
  simpa only [primitiveRealPolynomial_natDegree] using hk

/-- The equality case is a multiple zero of the corresponding derivative. -/
theorem actual_primitive_all_derivative_turan_equality
    (p : Real.Parameters) (hp : Real.Admissible p) (k : ℕ) (hk : k < p.h) (x : ℝ) :
    turan (Polynomial.derivative^[k] (primitiveRealPolynomial p)) x = 0 ↔
      (Polynomial.derivative^[k] (primitiveRealPolynomial p)).eval x = 0 ∧
      (Polynomial.derivative
        (Polynomial.derivative^[k] (primitiveRealPolynomial p))).eval x = 0 := by
  apply iterated_turan_eq_zero_iff (primitiveRealPolynomial_splits p hp) k _ x
  simpa only [primitiveRealPolynomial_natDegree] using hk



/-- The sharpened, non-strict bound for the actual normalized determinant. -/
theorem actual_primitive_laguerre (p : Real.Parameters) (hp : Real.Admissible p)
    (x : ℝ) : 0 ≤ laguerre p.h (primitiveRealPolynomial p) x := by
  simpa only [primitiveRealPolynomial_natDegree] using
    laguerre_nonnegative_of_real_splits (primitiveRealPolynomial_splits p hp) x

/-- All binomial-normalized Newton coefficient inequalities for the actual
primitive integer polynomial, transported to real coefficients. -/
theorem actual_primitive_coefficient_newton
    (p : Real.Parameters) (hp : Real.Admissible p) (k : ℕ) (hk : k + 2 ≤ p.h) :
    ((primitiveRealPolynomial p).coeff k / (p.h.choose k : ℝ)) *
      ((primitiveRealPolynomial p).coeff (k + 2) / (p.h.choose (k + 2) : ℝ)) ≤
        ((primitiveRealPolynomial p).coeff (k + 1) / (p.h.choose (k + 1) : ℝ)) ^ 2 := by
  simpa only [primitiveRealPolynomial_natDegree] using
    coefficient_newton (primitiveRealPolynomial_splits p hp) k
      (by simpa only [primitiveRealPolynomial_natDegree] using hk)

/-- The full weak shifted Newton hierarchy for every real center of the
actual normalized determinant. -/
theorem actual_primitive_shifted_newton
    (p : Real.Parameters) (hp : Real.Admissible p) (a : ℝ) (k : ℕ)
    (hk : k + 2 ≤ p.h) :
    (((primitiveRealPolynomial p).taylor a).coeff k / (p.h.choose k : ℝ)) *
      (((primitiveRealPolynomial p).taylor a).coeff (k + 2) / (p.h.choose (k + 2) : ℝ)) ≤
        (((primitiveRealPolynomial p).taylor a).coeff (k + 1) /
          (p.h.choose (k + 1) : ℝ)) ^ 2 := by
  simpa only [primitiveRealPolynomial_natDegree] using
    shifted_coefficient_newton (primitiveRealPolynomial_splits p hp) a k
      (by simpa only [primitiveRealPolynomial_natDegree] using hk)

/-- Exactly the weak Newton hierarchy for the paper's coefficients
e_m = [Y^m] P(zeta + Y) / P(zeta), with binomial normalization. -/
theorem actual_primitive_centered_newton
    (p : Real.Parameters) (hp : Real.Admissible p) (k : ℕ) (hk : k + 2 ≤ p.h) :
    ((((primitiveRealPolynomial p).taylor (Real.zeta p.weight)).coeff k /
        (primitiveRealPolynomial p).eval (Real.zeta p.weight)) /
      (p.h.choose k : ℝ)) *
      ((((primitiveRealPolynomial p).taylor (Real.zeta p.weight)).coeff (k + 2) /
          (primitiveRealPolynomial p).eval (Real.zeta p.weight)) /
        (p.h.choose (k + 2) : ℝ)) ≤
      ((((primitiveRealPolynomial p).taylor (Real.zeta p.weight)).coeff (k + 1) /
          (primitiveRealPolynomial p).eval (Real.zeta p.weight)) /
        (p.h.choose (k + 1) : ℝ)) ^ 2 := by
  simpa only [primitiveRealPolynomial_natDegree] using
    normalized_shifted_newton (primitiveRealPolynomial_splits p hp)
      (Real.zeta p.weight) k
      (by simpa only [primitiveRealPolynomial_natDegree] using hk)

/-- Applied to the actual primitive manuscript polynomial at the zeta center. -/
theorem actual_centered_consecutive_nonvanishing
    (p : Real.Parameters) (hp : Real.Admissible p) (k : ℕ) (hk : k < p.h) :
    ((primitiveRealPolynomial p).taylor (Real.zeta p.weight)).coeff k ≠ 0 ∨
      ((primitiveRealPolynomial p).taylor (Real.zeta p.weight)).coeff (k + 1) ≠ 0 := by
  apply consecutive_taylor_nonvanishing (primitiveRealPolynomial_splits p hp) k
  · simpa only [primitiveRealPolynomial_natDegree] using hk
  · exact primitiveRealPolynomial_center_ne_zero p hp

/-- The exact strict/non-strict coefficient pattern in Theorem3.7(2). -/
theorem actual_coefficient_strict_criterion
    (p : Real.Parameters) (hp : Real.Admissible p) (hh : 2 ≤ p.h)
    (k : ℕ) (hk : k + 2 ≤ p.h) :
    ((primitiveRealPolynomial p).coeff k / (p.h.choose k : ℝ)) *
        ((primitiveRealPolynomial p).coeff (k + 2) / (p.h.choose (k + 2) : ℝ)) <
        ((primitiveRealPolynomial p).coeff (k + 1) / (p.h.choose (k + 1) : ℝ)) ^ 2 ↔
      (primitiveRealPolynomial p).coeff (k + 1) ≠ 0 ∨
        ((primitiveRealPolynomial p).coeff k ≠ 0 ∧
          (primitiveRealPolynomial p).coeff (k + 2) ≠ 0) := by
  simpa only [primitiveRealPolynomial_natDegree] using
    StrictNormalizedNewton.coefficient_newton_strict_criterion
      (primitiveRealPolynomial_splits p hp) (actual_primitive_hasDistinctRoots p hp hh)
      k (by simpa only [primitiveRealPolynomial_natDegree] using hk)

/-- Every normalized Taylor Newton inequality at the actual zeta center is
strict, with no individual-coefficient-nonvanishing premise. -/
theorem actual_centered_newton_strict
    (p : Real.Parameters) (hp : Real.Admissible p) (hh : 2 ≤ p.h)
    (k : ℕ) (hk : k + 2 ≤ p.h) :
    ((((primitiveRealPolynomial p).taylor (Real.zeta p.weight)).coeff k /
        (primitiveRealPolynomial p).eval (Real.zeta p.weight)) /
      (p.h.choose k : ℝ)) *
      ((((primitiveRealPolynomial p).taylor (Real.zeta p.weight)).coeff (k + 2) /
          (primitiveRealPolynomial p).eval (Real.zeta p.weight)) /
        (p.h.choose (k + 2) : ℝ)) <
      ((((primitiveRealPolynomial p).taylor (Real.zeta p.weight)).coeff (k + 1) /
          (primitiveRealPolynomial p).eval (Real.zeta p.weight)) /
        (p.h.choose (k + 1) : ℝ)) ^ 2 := by
  simpa only [primitiveRealPolynomial_natDegree] using
    StrictNormalizedNewton.normalized_shifted_newton_strict
      (primitiveRealPolynomial_splits p hp) (actual_primitive_hasDistinctRoots p hp hh)
      (Real.zeta p.weight) (primitiveRealPolynomial_center_ne_zero p hp)
      k (by simpa only [primitiveRealPolynomial_natDegree] using hk)


/-- The sharpened strict Laguerre bound at the true zeta center. -/
theorem actual_centered_laguerre_strict
    (p : Real.Parameters) (hp : Real.Admissible p) (hh : 2 ≤ p.h) :
    0 < laguerre p.h (primitiveRealPolynomial p) (Real.zeta p.weight) := by
  simpa only [primitiveRealPolynomial_natDegree] using
    StrictLaguerreGeneral.laguerre_strict_of_distinct_roots
      (primitiveRealPolynomial_splits p hp) (actual_primitive_hasDistinctRoots p hp hh)
      (Real.zeta p.weight) (primitiveRealPolynomial_center_ne_zero p hp)

/-- The ratio form printed in Theorem 3.7(1), with its strictness justified
by the actual bilateral root split. -/
theorem actual_centered_derivative_ratio_strict
    (p : Real.Parameters) (hp : Real.Admissible p) (hh : 2 ≤ p.h) :
    (primitiveRealPolynomial p).derivative.derivative.eval (Real.zeta p.weight) /
      (primitiveRealPolynomial p).eval (Real.zeta p.weight) <
      (1 - 1 / (p.h : ℝ)) *
        ((primitiveRealPolynomial p).derivative.eval (Real.zeta p.weight) /
          (primitiveRealPolynomial p).eval (Real.zeta p.weight)) ^ 2 := by
  let P := primitiveRealPolynomial p
  let x := Real.zeta p.weight
  have hx : P.eval x ≠ 0 := primitiveRealPolynomial_center_ne_zero p hp
  have hn : 0 < (p.h : ℝ) := by exact_mod_cast (by omega : 0 < p.h)
  have heq : (1 - 1 / (p.h : ℝ)) * (P.derivative.eval x / P.eval x)^2 -
      P.derivative.derivative.eval x / P.eval x =
        laguerre p.h P x / ((p.h : ℝ) * P.eval x^2) := by
    unfold laguerre
    field_simp [hx, ne_of_gt hn]
    <;> ring
  have hpos : 0 < laguerre p.h P x / ((p.h : ℝ) * P.eval x^2) :=
    div_pos (actual_centered_laguerre_strict p hp hh)
      (mul_pos hn (sq_pos_of_ne_zero hx))
  rw [← heq] at hpos
  exact sub_pos.mp hpos

/-- The remaining coefficient pattern has equality, with both sides zero. -/
theorem actual_coefficient_equality_criterion
    (p : Real.Parameters) (hp : Real.Admissible p) (hh : 2 ≤ p.h)
    (k : ℕ) (hk : k + 2 ≤ p.h) :
    ((primitiveRealPolynomial p).coeff (k + 1) / (p.h.choose (k + 1) : ℝ)) ^ 2 =
      ((primitiveRealPolynomial p).coeff k / (p.h.choose k : ℝ)) *
        ((primitiveRealPolynomial p).coeff (k + 2) / (p.h.choose (k + 2) : ℝ)) ↔
      (primitiveRealPolynomial p).coeff (k + 1) = 0 ∧
        ((primitiveRealPolynomial p).coeff k = 0 ∨
          (primitiveRealPolynomial p).coeff (k + 2) = 0) := by
  have hs := actual_coefficient_strict_criterion p hp hh k hk
  constructor
  · intro heq
    have hnot : ¬ ((primitiveRealPolynomial p).coeff (k + 1) ≠ 0 ∨
        ((primitiveRealPolynomial p).coeff k ≠ 0 ∧
          (primitiveRealPolynomial p).coeff (k + 2) ≠ 0)) := by
      intro hh'
      have hlt := hs.mpr hh'
      linarith
    simpa only [not_or, not_not, not_and_or] using hnot
  · rintro ⟨hm, hl | hr⟩
    · simp [hm, hl]
    · simp [hm, hr]

/-- Formal polynomial differentiation agrees with iterated analytic differentiation. -/
theorem iteratedDeriv_eval (P : ℝ[X]) (k : ℕ) :
    iteratedDeriv k (fun x : ℝ => P.eval x) =
      fun x => (Polynomial.derivative^[k] P).eval x := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [iteratedDeriv_succ, ih]
    funext x
    simp only [Polynomial.deriv, Function.iterate_succ_apply']

/-- The analytic-derivative notation in equation (3.7), on the actual polynomial. -/
theorem actual_analytic_turan_nonnegative
    (p : Real.Parameters) (hp : Real.Admissible p) (k : ℕ) (x : ℝ) :
    (iteratedDeriv (k+1) (fun y : ℝ => (primitiveRealPolynomial p).eval y) x)^2 -
      iteratedDeriv k (fun y : ℝ => (primitiveRealPolynomial p).eval y) x *
        iteratedDeriv (k+2) (fun y : ℝ => (primitiveRealPolynomial p).eval y) x ≥ 0 := by
  simpa only [iteratedDeriv_eval, Function.iterate_succ_apply', Core.turan] using
    actual_primitive_all_derivative_turan p hp k x

theorem actual_analytic_turan_strict
    (p : Real.Parameters) (hp : Real.Admissible p) (k : ℕ) (hk : k < p.h)
    (x : ℝ) (hx : iteratedDeriv k
      (fun y : ℝ => (primitiveRealPolynomial p).eval y) x ≠ 0) :
    (iteratedDeriv (k+1) (fun y : ℝ => (primitiveRealPolynomial p).eval y) x)^2 -
      iteratedDeriv k (fun y : ℝ => (primitiveRealPolynomial p).eval y) x *
        iteratedDeriv (k+2) (fun y : ℝ => (primitiveRealPolynomial p).eval y) x > 0 := by
  have hf : (Polynomial.derivative^[k] (primitiveRealPolynomial p)).eval x ≠ 0 := by
    simpa only [iteratedDeriv_eval] using hx
  simpa only [iteratedDeriv_eval, Function.iterate_succ_apply', Core.turan] using
    actual_primitive_all_derivative_turan_strict p hp k hk x hf

end ManuscriptChain.NewtonTuran.Actual
