import Zetahyperbolic.Section3.ContinuousMeasure
import Zetahyperbolic.Section3.Unconditional

/-!
Corrected Proposition 3.2: the actual real-parameter moment matrix and pole
slope form a nonsingular symmetric pencil for every real s > 1. The measure
and all its moments are constructed. At odd weights the pencil is exactly
the established rational Hankel pencil, with the corrected normalization.
-/

noncomputable section
open scoped BigOperators
open MeasureTheory Set Matrix Polynomial

namespace ManuscriptChain.ContinuousWeight
open PoleDiagonalization

def gram (p : Real.Parameters) (s : ℝ) : Matrix (Fin p.h) (Fin p.h) ℝ :=
  Moments.momentMatrix (momentMeasure p s) p.h

theorem gram_posDef (p : Real.Parameters) {s : ℝ} (hs : 0 < s) : (gram p s).PosDef := by
  apply Moments.momentMatrix_posDef (momentMeasure_nonzero p s hs)
  intro i j
  exact (integrable_momentMeasure_iff p s hs _).mpr
    (integrableOn_weightedDensity_moment p s hs _)

theorem gram_integral (p : Real.Parameters) {s : ℝ} (hs : 0 < s) (i j : Fin p.h) :
    gram p s i j = ∫ y : ℝ in Ioi 0,
      y ^ (2 * (i.val + j.val)) * weightedDensity p s y :=
  integral_momentMeasure p s hs _

/-- The real-parameter construction uses precisely the original
`D_N^(2m)/D_K` weight, rather than an assumed positive substitute. -/
theorem weightedDensity_eq_paper (p : Real.Parameters) (hp : Real.Admissible p)
    (s : ℝ) {y : ℝ} (hy : 0 < y) :
    weightedDensity p s y =
      Real.evalQ (Real.D p.N) (y ^ 2) ^ (2 * p.m) /
        Real.evalQ (Real.D p.K) (y ^ 2) * density s y := by
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
  unfold weightedDensity
  rw [hfac]
  simp only [Real.evalQ, Real.realPolynomial, Polynomial.map_pow, Polynomial.eval_pow]
  conv_rhs => rw [hexp, pow_succ]
  change Real.evalQ (Real.D p.N) (y ^ 2) ^ (2 * p.m - 1) /
      Real.evalQ (Real.tailD p) (y ^ 2) * density s y =
    (Real.evalQ (Real.D p.N) (y ^ 2) ^ (2 * p.m - 1) *
      Real.evalQ (Real.D p.N) (y ^ 2)) /
      (Real.evalQ (Real.D p.N) (y ^ 2) * Real.evalQ (Real.tailD p) (y ^ 2)) * density s y
  field_simp

/-- The Gram matrix of the constructed measure is exactly the displayed
positive-half-line integral of corrected Proposition 3.2. -/
theorem gram_eq_paper_integral (p : Real.Parameters) (hp : Real.Admissible p)
    {s : ℝ} (hs : 0 < s) (i j : Fin p.h) :
    gram p s i j = ∫ y : ℝ in Ioi 0, y ^ (2 * (i.val + j.val)) *
      (Real.evalQ (Real.D p.N) (y ^ 2) ^ (2 * p.m) /
        Real.evalQ (Real.D p.K) (y ^ 2) * density s y) := by
  rw [gram_integral p hs i j]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro y hy
  dsimp only
  rw [weightedDensity_eq_paper p hp s hy]

theorem weightedDensity_odd (p : Real.Parameters) (y : ℝ) :
    weightedDensity p (2 * (p.k : ℝ) + 1) y = ConcreteMoment.weightedDensity p y := by
  simp only [weightedDensity, density_odd, ConcreteMoment.weightedDensity]

theorem gram_odd (p : Real.Parameters) (hp : Real.Admissible p) :
    gram p (2 * (p.k : ℝ) + 1) = Real.gram p (Real.zeta p.weight) := by
  ext i j
  rw [gram_integral p (by positivity), Hyperbolic.gram_eq_weighted_integral p hp]
  simp_rw [weightedDensity_odd]

def poleWeight (p : Real.Parameters) (s : ℝ) (a : Fin p.h) : ℝ :=
  ((Real.D p.N).eval (poleNode p a) ^ (2 * p.m - 1) /
    (derivative (Real.tailD p)).eval (poleNode p a) : ℚ) *
    (poleIndex p a : ℝ) ^ (s - 1)

theorem poleWeight_ne_zero (p : Real.Parameters) (s : ℝ) (a : Fin p.h) :
    poleWeight p s a ≠ 0 := by
  have hi : 0 < poleIndex p a := poleIndex_pos p a
  have hratio : (Real.D p.N).eval (poleNode p a) ^ (2 * p.m - 1) /
      (derivative (Real.tailD p)).eval (poleNode p a) ≠ 0 := by
    exact left_ne_zero_of_mul (PoleDiagonalization.poleWeight_ne_zero p a)
  exact mul_ne_zero (by exact_mod_cast hratio)
    (ne_of_gt (Real.rpow_pos_of_pos (by exact_mod_cast hi) _))

def vandermonde (p : Real.Parameters) : Matrix (Fin p.h) (Fin p.h) ℝ :=
  (poleVandermonde p).map (Rat.castHom ℝ)

def direction (p : Real.Parameters) (s : ℝ) : Matrix (Fin p.h) (Fin p.h) ℝ :=
  vandermonde p * Matrix.diagonal (poleWeight p s) * (vandermonde p).transpose

theorem direction_symmetric (p : Real.Parameters) (s : ℝ) : (direction p s).IsSymm := by
  simp [Matrix.IsSymm, direction, Matrix.transpose_mul, Matrix.mul_assoc]

theorem direction_det_ne_zero (p : Real.Parameters) (s : ℝ) :
    (direction p s).det ≠ 0 := by
  have hv : (vandermonde p).det ≠ 0 := by
    change ((poleVandermonde p).map (fun q : ℚ => (q : ℝ))).det ≠ 0
    rw [← Rat.cast_det]
    exact_mod_cast poleVandermonde_det_ne_zero p
  rw [direction, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_diagonal]
  exact mul_ne_zero (mul_ne_zero hv
    (Finset.prod_ne_zero_iff.mpr (fun a _ => poleWeight_ne_zero p s a))) hv

theorem direction_odd (p : Real.Parameters) :
    direction p (2 * (p.k : ℝ) + 1) = Real.derivativeMatrix p := by
  have hw : poleWeight p (2 * (p.k : ℝ) + 1) =
      fun a => (PoleDiagonalization.poleWeight p a : ℝ) := by
    funext a
    simp only [poleWeight, PoleDiagonalization.poleWeight, Rat.cast_mul,
      add_sub_cancel_right]
    rw [show 2 * (p.k : ℝ) = ((2 * p.k : ℕ) : ℝ) by push_cast; rfl,
      Real.rpow_natCast, Rat.cast_pow, Rat.cast_natCast]
  rw [direction, hw, vandermonde]
  have h := congrArg (fun M : Matrix (Fin p.h) (Fin p.h) ℚ => M.map (Rat.castHom ℝ))
    (rationalDerivativeMatrix_factorization p)
  simp only [Matrix.map_mul, Matrix.diagonal_map (map_zero (Rat.castHom ℝ)),
    Matrix.transpose_map] at h
  simpa only [Rat.coe_castHom, rationalDerivativeMatrix, Real.derivativeMatrix,
    Matrix.map] using h.symm

def center (s : ℝ) : ℝ := (riemannZeta (s : ℂ)).re

def pencil (p : Real.Parameters) (s : ℝ) : Spectral.SymmetricAffinePencil p.h where
  center := center s
  base := gram p s
  direction := direction p s
  base_symmetric := by
    ext i j
    simp [gram, Moments.momentMatrix, Nat.add_comm]
  direction_symmetric := direction_symmetric p s

theorem center_odd (p : Real.Parameters) (hp : Real.Admissible p) :
    center (2 * (p.k : ℝ) + 1) = Real.zeta p.weight := by
  rw [Real.zeta_eq_riemannZeta_re (by have h := hp.k_pos; simp [Real.Parameters.weight]; omega)]
  congr 2
  simp [center, Real.Parameters.weight]

theorem pencil_odd (p : Real.Parameters) (hp : Real.Admissible p) :
    pencil p (2 * (p.k : ℝ) + 1) = Real.manuscriptPencil p := by
  have hc := center_odd p hp
  have hg := gram_odd p hp
  have hd := direction_odd p
  simp only [pencil, Real.manuscriptPencil, hc, hg, hd]

/-- Corrected real-weight hyperbolicity, with all analytic obligations discharged. -/
theorem proposition_3_2_corrected (p : Real.Parameters) {s : ℝ} (hs : 1 < s) :
    (pencil p s).base.PosDef ∧ (pencil p s).direction.det ≠ 0 ∧
    (pencil p s).detPolynomial.natDegree = p.h ∧
    ∀ z : ℂ, Polynomial.eval₂ (algebraMap ℝ ℂ) z (pencil p s).detPolynomial = 0 →
      z.im = 0 := by
  have hp := gram_posDef p (show 0 < s by linarith)
  have hd := direction_det_ne_zero p s
  exact ⟨hp, hd, Spectral.theorem_3_1_degree_of_posDef (pencil p s) hp hd,
    Spectral.theorem_3_1_hyperbolicity_of_posDef (pencil p s) hp hd⟩

end ManuscriptChain.ContinuousWeight
