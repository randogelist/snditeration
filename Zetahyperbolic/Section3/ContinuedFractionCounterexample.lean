import Zetahyperbolic.Section3.Unconditional
import Zetahyperbolic.Section3.ContinuedFractionObstruction

/-!
# An unconditional actual-pencil obstruction to the literal Corollary 3.5

`ContinuedFractionObstruction` computes the actual admissible rank-one pencil.
This file supplies its positive center from the proved moment realization.
Thus the displayed one-step fraction in the manuscript, with `a₁ = M/G`,
cannot equal the ratio of consecutive determinant polynomials at the center.
The corrected resolvent statement and Theorem 3.1 are unaffected.
-/

noncomputable section

namespace ManuscriptChain.ContinuedFractionObstruction

theorem example_zero_shift_nonvanishing : (Real.delta exampleParams).eval 0 ≠ 0 := by
  rw [example_delta]
  norm_num

def exampleCenter : ℝ :=
  Real.evalQ (Real.delta exampleParams) (Real.zeta exampleParams.weight)

theorem exampleCenter_positive : 0 < exampleCenter := by
  have h : 0 < Matrix.det (Real.gram exampleParams (Real.zeta exampleParams.weight)) :=
    (GRAM_POSITIVE exampleParams example_admissible).det_pos
  rw [← Real.delta_eval_eq_det_gram] at h
  exact h

/-- The actual rank-one coefficient in the centered normalized pencil. -/
def exampleBeta : ℝ := (Real.entryM exampleParams 0 0 : ℝ) / exampleCenter

theorem exampleBeta_eq : exampleBeta = (-12 : ℝ) / exampleCenter := by
  simp [exampleBeta, example_slope]

theorem exampleCenter_eq :
    exampleCenter = 29 / 2 - 12 * Real.zeta exampleParams.weight := by
  rw [exampleCenter, example_delta]
  norm_num [Real.evalQ, Real.realPolynomial]

/-- This coefficient actually factors the unmodified centered determinant. -/
theorem example_centered_factorization (x : ℝ) :
    Real.evalQ (Real.delta exampleParams) x =
      exampleCenter * (1 + (x - Real.zeta exampleParams.weight) * exampleBeta) := by
  rw [example_delta, exampleBeta_eq]
  have hg : exampleCenter ≠ 0 := ne_of_gt exampleCenter_positive
  norm_num [Real.evalQ, Real.realPolynomial]
  field_simp
  rw [exampleCenter_eq]
  ring

/-- The h=1 instance of the printed fraction (3.6) is false at the center.
Its left side is positive; the printed right side is negative. -/
theorem literal_corollary_3_5_false :
    1 / exampleCenter ≠ 1 / (exampleBeta + (0 : ℝ)) := by
  rw [add_zero, exampleBeta_eq]
  exact positive_center_refutes_printed_fraction exampleCenter exampleCenter_positive

end ManuscriptChain.ContinuedFractionObstruction
