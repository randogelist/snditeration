import Zetahyperbolic.Section2.Moments
import Mathlib.Tactic

/-!
# The literal continued fraction in Corollary 3.5 needs correction

This is an exact rank-one check of the manuscript's displayed formula (3.6),
not a refutation of the true spectral theorem. For `I + t T`, a resolvent
continued fraction has diagonal terms `1 + t*a` and numerators `t^2*b^2`.
The printed formula instead uses `a + t` and `b^2`, and its conversion from
normalized determinant ratios also omits the ratio of the base determinants.

The admissible case `(k,m,N,K)=(1,1,1,2)` already distinguishes the formulas.
Its actual determinant is `29/2 - 12*X`. At the zeta center its value `g` is
positive, whereas the displayed one-step fraction has value `-g/12`.
-/

noncomputable section
open Polynomial

namespace ManuscriptChain.ContinuedFractionObstruction

def exampleParams : Real.Parameters := ⟨1, 1, 1, 2⟩

theorem example_admissible : Real.Admissible exampleParams := by
  constructor <;> decide

@[simp] theorem example_dimension : exampleParams.h = 1 := rfl

theorem example_numerator : Real.numerator exampleParams 0 0 = X + 1 := by
  norm_num [Real.numerator, Real.D, exampleParams, Finset.prod_range_succ]

theorem example_tail : Real.tailD exampleParams = X + C 4 := by
  norm_num [Real.tailD, exampleParams, Polynomial.C_ofNat]

theorem example_quotient : Real.quotient exampleParams 0 0 = 1 := by
  rw [Real.quotient, example_numerator, example_tail]
  have hrem : (X + 1 : ℚ[X]) % (X + C 4) = C (-3) := by
    rw [show (X + C 4 : ℚ[X]) = X - C (-4) by simp]
    rw [Polynomial.mod_X_sub_C_eq_C_eval]
    norm_num
  have heq := EuclideanDomain.div_add_mod (X + 1 : ℚ[X]) (X + C 4)
  rw [hrem] at heq
  apply mul_left_cancel₀ (monic_X_add_C (4 : ℚ)).ne_zero
  have hC4 : (C (4 : ℚ) : ℚ[X]) = 4 := rfl
  have hCn3 : (C (-3 : ℚ) : ℚ[X]) = -3 := by rw [map_neg]; rfl
  rw [hC4, hCn3] at heq
  rw [hC4]
  linear_combination heq

theorem example_residue : Real.residue exampleParams 0 0 2 = -3 := by
  norm_num [Real.residue, example_numerator, example_tail]

theorem example_slope : Real.entryM exampleParams 0 0 = -12 := by
  change (∑ a ∈ Finset.Icc 2 2, Real.residue exampleParams 0 0 a * (a : ℚ) ^ 2) = -12
  rw [Finset.Icc_self, Finset.sum_singleton, example_residue]
  norm_num

theorem example_intercept : Real.entryA exampleParams 0 0 = 29 / 2 := by
  have hm : Real.polynomialMoment 1 1 = 1 / 4 := by
    have hs : (1 : ℚ[X]).support = {0} :=
      Polynomial.support_C (one_ne_zero : (1 : ℚ) ≠ 0)
    unfold Real.polynomialMoment
    rw [hs, Finset.sum_singleton]
    norm_num [Polynomial.coeff_one, Real.monomialMoment, bernoulli_two]
  rw [Real.entryA, example_quotient]
  change Real.polynomialMoment 1 1 +
    (∑ a ∈ Finset.Icc 2 2, Real.residue exampleParams 0 0 a * Real.poleConstant 1 a) = 29 / 2
  rw [hm, Finset.Icc_self, Finset.sum_singleton, example_residue]
  norm_num [Real.poleConstant, Real.harmonic, Finset.sum_range_succ]

theorem example_delta : Real.delta exampleParams = C (29 / 2) - C 12 * X := by
  let i : Fin exampleParams.h := ⟨0, by decide⟩
  have hdet : Real.delta exampleParams = Real.pencil exampleParams i i :=
    Matrix.det_fin_one (Real.pencil exampleParams)
  rw [hdet]
  change C (Real.entryA exampleParams 0 0) + C (Real.entryM exampleParams 0 0) * X = _
  rw [example_intercept, example_slope]
  simp only [map_neg]
  ring

theorem example_root : (Real.delta exampleParams).eval (29 / 24) = 0 := by
  rw [example_delta]
  norm_num

/-- The actual rank-one example has a single reciprocal-square atom.
Its size-two Hankel determinant vanishes, contradicting strict positivity
at every order in the literal wording of Corollary 3.6. -/
theorem example_reciprocal_hankel_singular :
    Matrix.det (fun i j : Fin 2 =>
      ((24 / 29 : ℚ) ^ 2) ^ (i.val + j.val)) = 0 := by
  erw [Matrix.det_fin_two]
  norm_num

/-- The displayed h=1 fraction cannot equal the determinant ratio at a
positive center for the actual slope `-12`. -/
theorem positive_center_refutes_printed_fraction (g : ℝ) (hg : 0 < g) :
    (1 / g : ℝ) ≠ 1 / ((-12 : ℝ) / g) := by
  have hl : 0 < (1 / g : ℝ) := one_div_pos.mpr hg
  have hr : (1 / ((-12 : ℝ) / g) : ℝ) < 0 := by
    exact one_div_neg.mpr (div_neg_of_neg_of_pos (by norm_num) hg)
  exact ne_of_gt (lt_trans hr hl)

/-- The corrected rank-one factorization keeps both the base determinant
and the identity term in `I + t B`. -/
theorem corrected_rank_one_fraction (g t : ℝ) (hg : g ≠ 0) :
    1 / (g - 12 * t) = (1 / g) * (1 / (1 + t * ((-12 : ℝ) / g))) := by
  rw [one_div_mul_one_div]
  congr 1
  field_simp
  ring

/-- Roots `-1` and `1` have the same squared reciprocal distance from zero. -/
def symmetricEvenSum (n : ℕ) : ℚ :=
  1 / ((-1 : ℚ) ^ (2 * n)) + 1 / ((1 : ℚ) ^ (2 * n))

@[simp] theorem symmetricEvenSum_eq_two (n : ℕ) : symmetricEvenSum n = 2 := by
  norm_num [symmetricEvenSum, pow_mul]

/-- A positive finite moment sequence need not have strictly positive
Hankel determinants, even when its underlying roots are distinct. -/
theorem symmetric_even_hankel_singular :
    Matrix.det (fun i j : Fin 2 => symmetricEvenSum (i.val + j.val)) = 0 := by
  erw [Matrix.det_fin_two]
  norm_num

/-- Distinct nonzero real factors can have a vanishing intermediate
coefficient. This does not contradict strict normalized Newton inequalities. -/
theorem distinct_factors_zero_middle :
    (-1 : ℚ) ≠ 1 ∧
      ((1 + C (-1 : ℚ) * X) * (1 + C (1 : ℚ) * X)).coeff 1 = 0 := by
  constructor
  · norm_num
  · have hp : (1 + C (-1 : ℚ) * X) * (1 + C (1 : ℚ) * X) = 1 - X ^ 2 := by
      simp only [map_neg, map_one]
      ring
    rw [hp]
    simp [Polynomial.coeff_one]

end ManuscriptChain.ContinuedFractionObstruction
