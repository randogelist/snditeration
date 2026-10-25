import Zetahyperbolic.Section3.ConcretePencil
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
  norm_num [Real.tailD, exampleParams]

theorem example_quotient : Real.quotient exampleParams 0 0 = 1 := by
  rw [Real.quotient, example_numerator, example_tail]
  have hrem : (X + 1 : ℚ[X]) % (X + C 4) = C (-3) := by
    rw [show (X + C 4 : ℚ[X]) = X - C (-4) by simp]
    rw [Polynomial.mod_X_sub_C_eq_C_eval]
    norm_num
  have heq := EuclideanDomain.div_add_mod (X + 1 : ℚ[X]) (X + C 4)
  rw [hrem] at heq
  apply mul_left_cancel₀ (monic_X_add_C (4 : ℚ)).ne_zero
  linear_combination heq

theorem example_residue : Real.residue exampleParams 0 0 2 = -3 := by
  norm_num [Real.residue, example_numerator, example_tail]

theorem example_slope : Real.entryM exampleParams 0 0 = -12 := by
  norm_num [Real.entryM, exampleParams, example_residue]

theorem example_intercept : Real.entryA exampleParams 0 0 = 29 / 2 := by
  rw [Real.entryA, example_quotient]
  norm_num [exampleParams, example_residue, Real.polynomialMoment,
    Real.monomialMoment, Real.poleConstant, Real.harmonic, Finset.sum_range_succ,
    bernoulli_two]

theorem example_delta : Real.delta exampleParams = C (29 / 2) - C 12 * X := by
  unfold Real.delta
  change Matrix.det (fun i j : Fin 1 => Real.pencil exampleParams i j) = _
  rw [Matrix.det_fin_one]
  simp only [Real.pencil, Fin.val_zero, example_intercept, example_slope]
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
  norm_num [Matrix.det_fin_two]

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
  simp [symmetricEvenSum, pow_mul]

/-- A positive finite moment sequence need not have strictly positive
Hankel determinants, even when its underlying roots are distinct. -/
theorem symmetric_even_hankel_singular :
    Matrix.det (fun i j : Fin 2 => symmetricEvenSum (i.val + j.val)) = 0 := by
  norm_num [Matrix.det_fin_two]

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
    simp

end ManuscriptChain.ContinuedFractionObstruction
