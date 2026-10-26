import Mathlib

/-! Source-preserving integration from randogelist/zetahyperbolic-axiom@295eecb40a82557cf2b85101eb69707c357b0127.
Original declarations retain their namespaces and exact statements. Redundant
imports of source-paper blueprints are removed; no theorem premise is changed.
The printed all-orders strict-positivity claim remains false. -/


/-!
# Corollary 3.6 — corrected finite atomic Stieltjes moment statement

The paper's finite reciprocal-root moments form a positive semidefinite
Hankel system, not a positive definite system in every order.
The Gram factorization below is for arbitrary numbers of atoms and
arbitrary truncation order. The explicit two-atom determinant identities
exhibit positivity at order 2 and rank obstruction at order 3.

No statement of irrationality, spectral gap, or infinite support is used.
-/

noncomputable section
open scoped BigOperators
open Matrix

namespace PaperAdvances.Corollary3_6

/-- Hankel matrix of the first `n` moments of `h` real atoms. -/
def finiteHankel {h : ℕ} (u : Fin h → ℝ) (n : ℕ) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j => ∑ k : Fin h, u k ^ (i.val + j.val)

/-- Rectangular Vandermonde matrix, with columns indexed by atoms. -/
def finiteVandermonde {h : ℕ} (u : Fin h → ℝ) (n : ℕ) :
    Matrix (Fin n) (Fin h) ℝ :=
  fun i k => u k ^ i.val

/-- Finite atomic Hankel = Vandermonde times its transpose.
    Thus positivity is of Gram type and the rank is at most `h`. -/
theorem finite_hankel_gram {h : ℕ} (u : Fin h → ℝ) (n : ℕ) :
    finiteHankel u n =
      finiteVandermonde u n * (finiteVandermonde u n)ᵀ := by
  classical
  ext i j
  simp [finiteHankel, finiteVandermonde, Matrix.mul_apply, pow_add]

/-- Two distinct atoms give a nonnegative order-two Hankel determinant. -/
theorem two_atom_order_two_det (u v : ℝ) :
    (2 : ℝ) * (u^2 + v^2) - (u + v)^2 = (u - v)^2 := by
  ring

theorem two_atom_order_two_nonnegative (u v : ℝ) :
    0 ≤ (2 : ℝ) * (u^2 + v^2) - (u + v)^2 := by
  rw [two_atom_order_two_det]
  positivity

/-- The order-three Hankel determinant of any two-atom measure is zero.
    This is an exact counterexample to strict positivity at every order. -/
theorem two_atom_order_three_det_zero (u v : ℝ) :
    (2 : ℝ) * ((u^2 + v^2)*(u^4 + v^4) - (u^3 + v^3)^2)
      - (u+v) * ((u+v)*(u^4 + v^4) - (u^2 + v^2)*(u^3 + v^3))
      + (u^2 + v^2) * ((u+v)*(u^3 + v^3) - (u^2 + v^2)^2) = 0 := by
  ring

end PaperAdvances.Corollary3_6

#print axioms PaperAdvances.Corollary3_6.finite_hankel_gram
#print axioms PaperAdvances.Corollary3_6.two_atom_order_three_det_zero



/-!
# Corrected Corollary 3.6 -- arbitrary finite atomic Hankel Gram

The signed reciprocal-root power sums of a real-rooted polynomial give
**finite** atomic moments. Their Hankel matrices are positive semidefinite
at every truncation size, but cannot be strictly positive definite above
the number of distinct atoms.

For h pairwise distinct atoms, the full h-by-h Hankel matrix is positive
definite and has determinant equal to the square of the Vandermonde
determinant. No analytic hypothesis is used.

The printed manuscript's assertion of strict positivity for every order
must therefore be corrected; we do not formalize that false assertion.
-/

noncomputable section
open Matrix
namespace PaperAdvances.Corollary3_6_FullGram

open PaperAdvances.Corollary3_6

/-- Positive semidefiniteness for every finite set of atoms, with no
    distinctness or size restrictions. -/
theorem finite_hankel_posSemidef {h : ℕ}
    (u : Fin h → ℝ) (n : ℕ) :
    (finiteHankel u n).PosSemidef := by
  rw [finite_hankel_gram]
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
    Matrix.posSemidef_self_mul_conjTranspose (finiteVandermonde u n)

/-- Row independence suffices for strict positivity, regardless of shape. -/
theorem finite_hankel_posDef_of_injective {h : ℕ}
    (u : Fin h → ℝ) (n : ℕ)
    (hv : Function.Injective (finiteVandermonde u n).vecMul) :
    (finiteHankel u n).PosDef := by
  rw [finite_hankel_gram]
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
    Matrix.PosDef.mul_conjTranspose_self (finiteVandermonde u n) hv

/-- For an equal-size Vandermonde, the determinant of the
    finite Hankel Gram is the Vandermonde determinant squared. -/
theorem finite_hankel_square_det {h : ℕ} (u : Fin h → ℝ) :
    (finiteHankel u h).det =
      (finiteVandermonde u h).det ^ 2 := by
  rw [finite_hankel_gram, Matrix.det_mul, Matrix.det_transpose]
  ring

/-- Pairwise distinct atoms make the square Vandermonde invertible. -/
theorem finite_vandermonde_det_ne_zero {h : ℕ} (u : Fin h → ℝ)
    (hu : Function.Injective u) :
    (finiteVandermonde u h).det ≠ 0 := by
  have heq : finiteVandermonde u h =
      (Matrix.vandermonde u).transpose := by
    ext i j
    rfl
  rw [heq, Matrix.det_transpose]
  exact Matrix.det_vandermonde_ne_zero_iff.mpr hu

/-- The full-order finite Hankel determinant is strictly positive for
    pairwise distinct real atoms. -/
theorem finite_hankel_full_det_pos {h : ℕ} (u : Fin h → ℝ)
    (hu : Function.Injective u) :
    0 < (finiteHankel u h).det := by
  rw [finite_hankel_square_det]
  exact sq_pos_of_ne_zero (finite_vandermonde_det_ne_zero u hu)

/-- Strict positive definiteness in the distinct-atom full-order case. -/
theorem finite_hankel_full_posDef {h : ℕ} (u : Fin h → ℝ)
    (hu : Function.Injective u) :
    (finiteHankel u h).PosDef := by
  -- Use the same explicit matrix-first iff application as the native
  -- compiler-PASS `Theorem_3_9_PositiveSlope.poleM_posDef` proof.
  have hVdet : IsUnit (finiteVandermonde u h).det :=
    isUnit_iff_ne_zero.mpr (finite_vandermonde_det_ne_zero u hu)
  have hVunit : IsUnit (finiteVandermonde u h) :=
    (Matrix.isUnit_iff_isUnit_det (finiteVandermonde u h)).2 hVdet
  have hVinj : Function.Injective (finiteVandermonde u h).vecMul :=
    Matrix.vecMul_injective_iff_isUnit.2 hVunit
  exact finite_hankel_posDef_of_injective u h hVinj

end PaperAdvances.Corollary3_6_FullGram

#print axioms PaperAdvances.Corollary3_6_FullGram.finite_hankel_posSemidef
#print axioms PaperAdvances.Corollary3_6_FullGram.finite_hankel_full_det_pos
#print axioms PaperAdvances.Corollary3_6_FullGram.finite_hankel_full_posDef



/-!
# Corollary 3.6: exact finite Stieltjes hierarchy after necessary correction

The printed assertion of strictly positive Hankel determinants at *all* orders
for finitely many atomic roots is false. This module proves the valid strong
replacement: arbitrary real atoms with nonnegative masses have positive
semidefinite Hankel matrices of *every* order. If the masses are positive and
the atoms are pairwise distinct, the full atomic-order determinant and matrix
are strictly positive. Every larger square Hankel determinant is exactly zero.

This result is unconditional and contains no arithmetic Witness.
-/

noncomputable section
open scoped BigOperators
open Matrix

namespace PaperAdvances.Corollary3_6_WeightedCorrected

open PaperAdvances.Corollary3_6
open PaperAdvances.Corollary3_6_FullGram

/-- The order-n moment Hankel matrix for a finite real atomic measure with
masses `w`; no distinctness or sign assumptions are built into the definition. -/
def weightedHankel {h : ℕ} (u w : Fin h → ℝ) (n : ℕ) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j => ∑ k : Fin h, w k * u k ^ (i.val + j.val)

/-- An exact finite weighted Vandermonde Gram factorization. -/
theorem weighted_hankel_gram {h : ℕ} (u w : Fin h → ℝ) (n : ℕ) :
    weightedHankel u w n =
      finiteVandermonde u n * Matrix.diagonal w *
        (finiteVandermonde u n)ᵀ := by
  classical
  ext i j
  unfold weightedHankel
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, finiteVandermonde]
  apply Finset.sum_congr rfl
  intro k hk
  rw [pow_add]
  ring

/-- Every truncation of any finite nonnegative atomic moment measure
is positive semidefinite, including truncation orders larger than the
number of atoms. -/
theorem weighted_hankel_posSemidef {h : ℕ} (u w : Fin h → ℝ) (n : ℕ)
    (hw : ∀ k, 0 ≤ w k) :
    (weightedHankel u w n).PosSemidef := by
  rw [weighted_hankel_gram]
  have hd : (Matrix.diagonal w : Matrix (Fin h) (Fin h) ℝ).PosSemidef :=
    Matrix.posSemidef_diagonal_iff.mpr hw
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
    hd.mul_mul_conjTranspose_same (finiteVandermonde u n)

/-- At exactly the number of atoms, all strictly positive masses and
pairwise distinct atoms make the weighted Hankel matrix positive definite. -/
theorem weighted_hankel_full_posDef {h : ℕ} (u w : Fin h → ℝ)
    (hu : Function.Injective u) (hw : ∀ k, 0 < w k) :
    (weightedHankel u w h).PosDef := by
  rw [weighted_hankel_gram]
  have hd : (Matrix.diagonal w : Matrix (Fin h) (Fin h) ℝ).PosDef :=
    Matrix.posDef_diagonal_iff.mpr hw
  have hVunit : IsUnit (finiteVandermonde u h) :=
    (Matrix.isUnit_iff_isUnit_det (finiteVandermonde u h)).2
      (isUnit_iff_ne_zero.mpr (finite_vandermonde_det_ne_zero u hu))
  have hVinj : Function.Injective (finiteVandermonde u h).vecMul :=
    Matrix.vecMul_injective_iff_isUnit.2 hVunit
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
    hd.mul_mul_conjTranspose_same (B := finiteVandermonde u h) hVinj

/-- Exact *rank obstruction*: once the Hankel order exceeds the number
of atoms, its determinant is zero, even without any assumption on masses.
This repairs the overstrong strict-Hankel claim in the PDF. -/
theorem weighted_hankel_det_zero_above_support {h : ℕ} (u w : Fin h → ℝ)
    (n : ℕ) (hn : h < n) : (weightedHankel u w n).det = 0 := by
  classical
  by_contra hne
  have hmat : IsUnit (weightedHankel u w n) :=
    (Matrix.isUnit_iff_isUnit_det (weightedHankel u w n)).2
      (isUnit_iff_ne_zero.mpr hne)
  have hfull : (weightedHankel u w n).rank = n := by
    simpa using Matrix.rank_of_isUnit (weightedHankel u w n) hmat
  have hbound : (weightedHankel u w n).rank ≤ h := by
    rw [weighted_hankel_gram]
    exact ((Matrix.rank_mul_le_left _ _).trans
      (Matrix.rank_mul_le_left _ _)).trans
        (Matrix.rank_le_width (finiteVandermonde u n))
  omega

/-- Unweighted special case: every Hankel determinant of order exceeding
its finite atomic support is exactly zero. -/
theorem finite_hankel_det_zero_above_support {h : ℕ} (u : Fin h → ℝ)
    (n : ℕ) (hn : h < n) : (finiteHankel u n).det = 0 := by
  have hsame : weightedHankel u (fun _ => 1) n = finiteHankel u n := by
    ext i j
    simp [weightedHankel, finiteHankel]
  rw [← hsame]
  exact weighted_hankel_det_zero_above_support u (fun _ => 1) n hn

end PaperAdvances.Corollary3_6_WeightedCorrected

#print axioms PaperAdvances.Corollary3_6_WeightedCorrected.weighted_hankel_gram
#print axioms PaperAdvances.Corollary3_6_WeightedCorrected.weighted_hankel_posSemidef
#print axioms PaperAdvances.Corollary3_6_WeightedCorrected.weighted_hankel_full_posDef
#print axioms PaperAdvances.Corollary3_6_WeightedCorrected.weighted_hankel_det_zero_above_support



/-!
# Corollary 3.6: complete finite atomic rank threshold, including EVERY n

The finite weighted Hankel matrix is positive definite at each order n ≤ h,
provided the h atoms are pairwise distinct and all weights are positive.
Its determinant is zero for every n > h, *even for signed weights*.
Hence we obtain the exact (sharp) full-size positive determinant criterion.
This is the correct finite-support replacement for the PDF's impossible
all-orders strict-Hankel-positivity clause. It does not assert the stronger,
false printed claim or any infinite-atom spectral theorem.
-/

noncomputable section
open Matrix

namespace PaperAdvances.Corollary3_6_ExactFiniteRank

open PaperAdvances.Corollary3_6
open PaperAdvances.Corollary3_6_WeightedCorrected

/-- Every lower-order Hankel matrix is a leading principal submatrix of
  the full h-by-h atomic Hankel matrix, with no weight restrictions. -/
theorem weighted_leading_block {h : ℕ} (u w : Fin h → ℝ)
    (n : ℕ) (hn : n ≤ h) :
    weightedHankel u w n =
      (weightedHankel u w h).submatrix (Fin.castLE hn) (Fin.castLE hn) := by
  ext i j
  simp only [weightedHankel, Matrix.submatrix_apply, Fin.val_castLE]

/-- All moment Hankel truncations up to the number of distinct atoms
  are strictly positive definite, including n=0 and all intermediate n. -/
theorem weighted_posDef_up_to_support {h : ℕ} (u w : Fin h → ℝ)
    (hu : Function.Injective u) (hw : ∀ i, 0 < w i)
    (n : ℕ) (hn : n ≤ h) :
    (weightedHankel u w n).PosDef := by
  rw [weighted_leading_block u w n hn]
  exact (weighted_hankel_full_posDef u w hu hw).submatrix
    (Fin.castLE_injective hn)

/-- Precise sign criterion of the finite positive measure's determinants.
  No claim of strict positivity beyond finite support is possible. -/
theorem weighted_det_pos_iff_order_le_support {h : ℕ} (u w : Fin h → ℝ)
    (hu : Function.Injective u) (hw : ∀ i, 0 < w i)
    (n : ℕ) :
    0 < (weightedHankel u w n).det ↔ n ≤ h := by
  constructor
  · intro hp
    by_contra hn
    have hstrict : h < n := by omega
    have hz := weighted_hankel_det_zero_above_support u w n hstrict
    rw [hz] at hp
    exact (lt_irrefl 0) hp
  · intro hn
    exact (weighted_posDef_up_to_support u w hu hw n hn).det_pos

/-- Exact unweighted Stieltjes determinant dichotomy. -/
theorem unweighted_det_pos_iff_order_le_support {h : ℕ} (u : Fin h → ℝ)
    (hu : Function.Injective u) (n : ℕ) :
    0 < (finiteHankel u n).det ↔ n ≤ h := by
  have heq : weightedHankel u (fun _ => (1 : ℝ)) n = finiteHankel u n := by
    ext i j
    simp [weightedHankel, finiteHankel]
  rw [← heq]
  exact weighted_det_pos_iff_order_le_support u (fun _ => 1) hu
    (fun _ => by norm_num) n

end PaperAdvances.Corollary3_6_ExactFiniteRank

#print axioms PaperAdvances.Corollary3_6_ExactFiniteRank.weighted_leading_block
#print axioms PaperAdvances.Corollary3_6_ExactFiniteRank.weighted_posDef_up_to_support
#print axioms PaperAdvances.Corollary3_6_ExactFiniteRank.weighted_det_pos_iff_order_le_support
#print axioms PaperAdvances.Corollary3_6_ExactFiniteRank.unweighted_det_pos_iff_order_le_support
