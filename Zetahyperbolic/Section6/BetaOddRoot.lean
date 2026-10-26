import Zetahyperbolic.Section6.BetaOddGram
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-!
# The actual rational Padé root for every odd beta weight

For every positive dimension, the literal pencil has a unique rational root,
an exact inverse-Gram error formula and the printed one-sided sign. All
positivity and nonzero-slope premises are discharged from the actual measure.
This module makes no asymptotic or transcendence assertion.
-/
noncomputable section
open Matrix

namespace ManuscriptChain.BetaOddRoot
open BetaOddMoments BetaOddGram

def alternatingVector (h : ℕ) : Fin h → ℝ := fun i => (-1:ℝ)^i.val

theorem alternatingVector_ne_zero (h : ℕ) (hh : 0<h) : alternatingVector h ≠ 0 := by
  intro hz
  have he := congrFun hz (⟨0,hh⟩ : Fin h)
  norm_num [alternatingVector] at he

def inverseGram (k N h : ℕ) : ℝ :=
  alternatingVector h ⬝ᵥ ((pencil k N h (moment k 0))⁻¹ *ᵥ alternatingVector h)

theorem inverseGram_pos (k N h : ℕ) (hh : 0<h) : 0 < inverseGram k N h := by
  simpa only [inverseGram, star_trivial] using
    (actual_beta_gram_posDef k N h).inv.dotProduct_mulVec_pos
      (alternatingVector_ne_zero h hh)

theorem det_rank_one {h : ℕ} (A : Matrix (Fin h) (Fin h) ℝ)
    (hA : IsUnit A.det) (c : ℝ) (v : Fin h → ℝ) :
    (A + c • Matrix.vecMulVec v v).det =
      A.det * (1 + c * (v ⬝ᵥ (A⁻¹ *ᵥ v))) := by
  rw [← Matrix.smul_vecMulVec, Matrix.vecMulVec_eq Unit,
    Matrix.det_add_replicateCol_mul_replicateRow hA]
  rw [Matrix.mul_assoc, ← Matrix.replicateCol_mulVec]
  simp only [Matrix.det_unique, Matrix.add_apply, Matrix.one_apply_eq,
    Matrix.replicateRow_mul_replicateCol_apply, Matrix.mulVec_smul,
    dotProduct_smul, smul_eq_mul]

theorem slope_eq (N h : ℕ) : BetaOddGram.slope N h =
    (-1:ℝ)^N • Matrix.vecMulVec (alternatingVector h) (alternatingVector h) := by
  ext i j
  simp only [BetaOddGram.slope, alternatingVector, Matrix.smul_apply, smul_eq_mul,
    Matrix.vecMulVec, Matrix.of_apply, pow_add]

/-- Exact matrix determinant lemma for the actual beta pencil. -/
theorem determinant_formula (k N h : ℕ) (X : ℝ) :
    (pencil k N h X).det = (pencil k N h (moment k 0)).det *
      (1 + (-1:ℝ)^N * (X-moment k 0) * inverseGram k N h) := by
  rw [pencil_affine k N h X (moment k 0), slope_eq, smul_smul,
    det_rank_one _ (isUnit_iff_ne_zero.mpr (actual_beta_gram_det_pos k N h).ne')]
  unfold inverseGram
  ring

def root (k N h : ℕ) : ℝ := moment k 0 - (-1:ℝ)^N / inverseGram k N h

theorem sign_sq (N : ℕ) : (-1:ℝ)^N * (-1:ℝ)^N = 1 := by
  rw [← mul_pow]
  norm_num

theorem root_zero (k N h : ℕ) (hh : 0<h) : (pencil k N h (root k N h)).det = 0 := by
  rw [determinant_formula]
  have hq := (inverseGram_pos k N h hh).ne'
  have hs := sign_sq N
  suffices he : 1 + (-1:ℝ)^N * (root k N h-moment k 0) * inverseGram k N h = 0 by
    rw [he, mul_zero]
  have hc : root k N h-moment k 0 = -(-1:ℝ)^N / inverseGram k N h := by
    unfold root
    ring
  rw [hc]
  have hp : (-1:ℝ)^N * (-(-1:ℝ)^N / inverseGram k N h) * inverseGram k N h =
      -((-1:ℝ)^N * (-1:ℝ)^N) := by
    field_simp [hq] <;> ring
  rw [hp, hs]
  norm_num

theorem root_unique (k N h : ℕ) (hh : 0<h) (X : ℝ) :
    (pencil k N h X).det = 0 ↔ X = root k N h := by
  constructor
  · intro hz
    rw [determinant_formula] at hz
    have he := (mul_eq_zero.mp hz).resolve_left (actual_beta_gram_det_pos k N h).ne'
    have hq := (inverseGram_pos k N h hh).ne'
    have hs := sign_sq N
    have he2 : (-1:ℝ)^N * (X-moment k 0) * inverseGram k N h = -1 := by
      linarith
    have he3 : (X-moment k 0) * inverseGram k N h = -(-1:ℝ)^N := by
      calc
        _ = ((-1:ℝ)^N * (-1:ℝ)^N) *
            ((X-moment k 0) * inverseGram k N h) := by rw [hs]; ring
        _ = (-1:ℝ)^N * ((-1:ℝ)^N * (X-moment k 0) * inverseGram k N h) := by ring
        _ = _ := by rw [he2]; ring
    unfold root
    field_simp [hq]
    nlinarith [he3]
  · rintro rfl
    exact root_zero k N h hh

/-- The root lies below the beta value for even N, above it for odd N. -/
theorem root_side (k N h : ℕ) (hh : 0<h) :
    0 < (-1:ℝ)^N * (moment k 0 - root k N h) := by
  have hq := inverseGram_pos k N h hh
  have hs := sign_sq N
  have he : (-1:ℝ)^N * (moment k 0-root k N h) = 1 / inverseGram k N h := by
    simp only [root, sub_sub_cancel]
    rw [← mul_div_assoc, hs]
  rw [he]
  exact one_div_pos.mpr hq

theorem root_error (k N h : ℕ) (hh : 0<h) :
    |moment k 0-root k N h| = (inverseGram k N h)⁻¹ := by
  unfold root
  rw [sub_sub_cancel, abs_div, abs_pow]
  norm_num [abs_of_pos (inverseGram_pos k N h hh), one_div]

/-- Rational coefficients of the literal uncentered pencil. -/
def rationalPencil (k N h : ℕ) (X : ℚ) : Matrix (Fin h) (Fin h) ℚ :=
  fun i j => (-1:ℚ)^(N+i.val+j.val) * (X -
    ∑ n ∈ Finset.range (N+i.val+j.val), (-1:ℚ)^n / (2*(n:ℚ)+1)^(2*k+1))

theorem rationalPencil_cast (k N h : ℕ) (X : ℚ) :
    (rationalPencil k N h X).map (algebraMap ℚ ℝ) = pencil k N h X := by
  ext i j
  simp [rationalPencil, pencil, betaPartialSum]

theorem rational_det_cast (k N h : ℕ) (X : ℚ) :
    ((rationalPencil k N h X).det : ℝ) = (pencil k N h X).det := by
  rw [← rationalPencil_cast]
  exact RingHom.map_det (algebraMap ℚ ℝ) _

def rationalRoot (k N h : ℕ) : ℚ :=
  -(rationalPencil k N h 0).det /
    ((rationalPencil k N h 1).det - (rationalPencil k N h 0).det)

theorem determinant_affine (k N h : ℕ) (X : ℝ) :
    (pencil k N h X).det = (pencil k N h 0).det +
      X * ((pencil k N h 1).det - (pencil k N h 0).det) := by
  rw [determinant_formula k N h X, determinant_formula k N h 0,
    determinant_formula k N h 1]
  ring

theorem determinant_slope_ne_zero (k N h : ℕ) (hh : 0<h) :
    (pencil k N h 1).det - (pencil k N h 0).det ≠ 0 := by
  rw [determinant_formula k N h 1, determinant_formula k N h 0]
  have he : (pencil k N h (moment k 0)).det *
      (1 + (-1:ℝ)^N * (1-moment k 0) * inverseGram k N h) -
      (pencil k N h (moment k 0)).det *
      (1 + (-1:ℝ)^N * (0-moment k 0) * inverseGram k N h) =
      (pencil k N h (moment k 0)).det * (-1:ℝ)^N * inverseGram k N h := by ring
  rw [he]
  exact mul_ne_zero (mul_ne_zero (actual_beta_gram_det_pos k N h).ne'
    (pow_ne_zero _ (by norm_num))) (inverseGram_pos k N h hh).ne'

/-- The unique root is an explicitly defined rational number for every k,N,h>0. -/
theorem root_eq_rationalRoot (k N h : ℕ) (hh : 0<h) :
    root k N h = (rationalRoot k N h : ℝ) := by
  symm
  apply (root_unique k N h hh _).1
  rw [determinant_affine]
  have he : (rationalRoot k N h : ℝ) = -(pencil k N h 0).det /
      ((pencil k N h 1).det - (pencil k N h 0).det) := by
    simp only [rationalRoot, Rat.cast_div, Rat.cast_neg, Rat.cast_sub,
      rational_det_cast, Rat.cast_zero, Rat.cast_one]
  rw [he]
  field_simp [determinant_slope_ne_zero k N h hh] <;> ring

end ManuscriptChain.BetaOddRoot
