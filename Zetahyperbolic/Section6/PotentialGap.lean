import Zetahyperbolic.Section3.ActualSpectrum

/-!
# Theorem 6.10(1): exact finite potential-gap identity

The algebraic/logarithmic conservation law is established for the actual
whitened matrix, for every nonzero scalar normalization. The analytic
identification with equilibrium energy is a separate, unproved statement.
The last lemmas isolate the missing upper bound on the decay rate in the
printed deduction of a height/decay ratio greater than 581.
-/

noncomputable section
open Polynomial Matrix Filter
open scoped BigOperators Topology

namespace ManuscriptChain.PotentialGap
open Spectral

variable {n : ℕ}

theorem detPolynomial_coeff_dimension (p : SymmetricAffinePencil n) :
    p.detPolynomial.coeff n = p.direction.det := by
  have hid : p.polynomialMatrix =
      (X : ℝ[X]) • p.direction.map C + (p.base - p.center • p.direction).map C := by
    ext i j
    simp [SymmetricAffinePencil.polynomialMatrix, Matrix.map_apply,
      Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply]
    ring
  rw [SymmetricAffinePencil.detPolynomial, hid]
  simpa only [Fintype.card_fin] using
    Polynomial.coeff_det_X_add_C_card p.direction (p.base - p.center • p.direction)

theorem base_det_mul_whitened_det (p : SymmetricAffinePencil n)
    (hp : p.base.PosDef) :
    p.base.det * (whitenedMatrix p).det = p.direction.det := by
  have hsq := congrArg Matrix.det (whiteningSqrt_sq p hp)
  have hcong := congrArg Matrix.det (whitening_congruence p hp)
  simp only [Matrix.det_mul] at hsq hcong
  rw [← hsq]
  nlinarith only [hcong]

/-- Finite leading-coefficient identity, without any asymptotic input. -/
theorem abs_coefficient_eq_center_mul_det (p : SymmetricAffinePencil n)
    (hp : p.base.PosDef) (scale : ℝ) :
    |(C scale * p.detPolynomial).coeff n| =
      |(C scale * p.detPolynomial).eval p.center| * |(whitenedMatrix p).det| := by
  rw [Polynomial.coeff_C_mul, detPolynomial_coeff_dimension,
    Polynomial.eval_mul, Polynomial.eval_C, p.eval_detPolynomial_center,
    ← abs_mul, mul_assoc, base_det_mul_whitened_det p hp]

/-- A nonzero normalization and direction give the exact logarithmic law. -/
theorem log_coefficient_sub_log_center (p : SymmetricAffinePencil n)
    (hp : p.base.PosDef) (scale : ℝ) (hs : scale ≠ 0)
    (hM : p.direction.det ≠ 0) :
    Real.log |(C scale * p.detPolynomial).coeff n| -
      Real.log |(C scale * p.detPolynomial).eval p.center| =
      Real.log |(whitenedMatrix p).det| := by
  have heval : (C scale * p.detPolynomial).eval p.center ≠ 0 := by
    rw [Polynomial.eval_mul, Polynomial.eval_C, p.eval_detPolynomial_center]
    exact mul_ne_zero hs (ne_of_gt hp.det_pos)
  have hdet := whitenedMatrix_det_ne_zero p hp hM
  rw [abs_coefficient_eq_center_mul_det p hp scale,
    Real.log_mul (abs_ne_zero.mpr heval) (abs_ne_zero.mpr hdet)]
  ring

/-- The two normalized rates add to the normalized spectral determinant. -/
theorem normalized_log_identity (p : SymmetricAffinePencil n)
    (hp : p.base.PosDef) (scale : ℝ) (hs : scale ≠ 0)
    (hM : p.direction.det ≠ 0) (K : ℝ) :
    Real.log |(C scale * p.detPolynomial).coeff n| / K ^ 2 +
      (-Real.log |(C scale * p.detPolynomial).eval p.center| / K ^ 2) =
      Real.log |(whitenedMatrix p).det| / K ^ 2 := by
  rw [← add_div, ← sub_eq_add_neg, log_coefficient_sub_log_center p hp scale hs hM]

/-- The actual admissible odd-zeta pencils satisfy the finite conservation law. -/
theorem manuscript_normalized_log_identity (p : Real.Parameters)
    (hp : Real.Admissible p) (scale : ℝ) (hs : scale ≠ 0) :
    Real.log |(C scale * (Real.manuscriptPencil p).detPolynomial).coeff p.h| /
        (p.K : ℝ) ^ 2 +
      (-Real.log |(C scale * (Real.manuscriptPencil p).detPolynomial).eval
        (Real.zeta p.weight)| / (p.K : ℝ) ^ 2) =
      Real.log |(whitenedMatrix (Real.manuscriptPencil p)).det| / (p.K : ℝ) ^ 2 :=
  normalized_log_identity (Real.manuscriptPencil p) (GRAM_POSITIVE p hp)
    scale hs (General.derivative_nonsingular p) p.K

/-- Passing to limits preserves the exact algebraic identity. Limits themselves
must be proved for the particular parameter and normalization sequences. -/
theorem rate_conservation {ι : Type*} {l : Filter ι}
    {a b c : ι → ℝ} {A B : ℝ}
    (hid : ∀ i, a i + b i = c i)
    (ha : Tendsto a l (𝓝 A)) (hb : Tendsto b l (𝓝 B)) :
    Tendsto c l (𝓝 (A + B)) := by
  simpa only [hid] using ha.add hb

/-- Correct numerical implication: the rate needs an upper, not lower, bound. -/
theorem height_decay_ratio_gt_581 (height epsilon : ℝ)
    (hsum : (2331 / 10000 : ℝ) ≤ height + epsilon)
    (hepsilon : 0 < epsilon) (hupper : epsilon ≤ 1 / 2500) :
    581 < height / epsilon := by
  apply (lt_div_iff₀ hepsilon).2
  linarith

/-- A sharp explicit witness refutes the claimed deduction from a lower rate
bound, even with the exact sum identity and nonnegative height. -/
theorem lower_decay_bound_counterexample :
    ∃ height epsilon : ℝ, 0 ≤ height ∧ 0 < epsilon ∧
      (1 / 2500 : ℝ) ≤ epsilon ∧
      (2331 / 10000 : ℝ) = height + epsilon ∧ height / epsilon < 581 := by
  refine ⟨2321 / 10000, 1 / 1000, ?_⟩
  norm_num

/-- An upper bound on the positive evaluation yields a lower decay-rate bound. -/
theorem evaluation_upper_gives_rate_lower (value scale rate : ℝ)
    (hvalue : 0 < value) (hscale : 0 < scale)
    (heval : value ≤ Real.exp (-rate * scale)) :
    rate ≤ -Real.log value / scale := by
  have hlog := Real.log_le_log hvalue heval
  rw [Real.log_exp] at hlog
  apply (le_div_iff₀ hscale).2
  linarith

/-- A lower bound on the positive evaluation would supply the missing upper rate bound. -/
theorem evaluation_lower_gives_rate_upper (value scale rate : ℝ)
    (hscale : 0 < scale) (heval : Real.exp (-rate * scale) ≤ value) :
    -Real.log value / scale ≤ rate := by
  have hlog := Real.log_le_log (Real.exp_pos (-rate * scale)) heval
  rw [Real.log_exp] at hlog
  apply (div_le_iff₀ hscale).2
  linarith

end ManuscriptChain.PotentialGap
