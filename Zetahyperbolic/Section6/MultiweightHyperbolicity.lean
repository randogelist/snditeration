import Zetahyperbolic.Section5.RationalIndependence
import Zetahyperbolic.Section5.DualCenteredSpectrum

/-!
# Theorem 6.7(1): the actual multiweight rational pencil

The finite weighted harmonic constant is the sum of the manuscript's
single-weight constants. Its slope is one copy of CCᵀ because the variable
is Z = sum a_m X_m. No sign assumption on the weights is needed.
This proves the full-degree real spectrum; it does not assert either
infinite Krein cone or the arithmetic part of Theorem 6.7.
-/
noncomputable section
open Matrix Polynomial
open scoped BigOperators
namespace ManuscriptChain.Multiweight
open DualAlgebra DualSpectral Section5DualSpectrum

def constant {k h K : ℕ} (a : Fin k → ℤ)
    (c : Matrix (Fin h) (Fin (K+1)) ℚ) : Matrix (Fin h) (Fin h) ℚ :=
  fun i j => ∑ m, (a m : ℚ) * dualConstantMatrix (2*(m.val+1)+1) c i j

def entry {k h K : ℕ} (a : Fin k → ℤ)
    (c : Matrix (Fin h) (Fin (K+1)) ℚ) (i j : Fin h) : ℚ[X] :=
  C (constant a c i j) + C (dualSlopeMatrix c i j) * X

def delta {k h K : ℕ} (a : Fin k → ℤ)
    (c : Matrix (Fin h) (Fin (K+1)) ℚ) : ℚ[X] :=
  Matrix.det (entry a c)

theorem constant_symmetric {k h K : ℕ} (a : Fin k → ℤ)
    (c : Matrix (Fin h) (Fin (K+1)) ℚ) : (constant a c).IsSymm := by
  ext i j
  simp only [Matrix.transpose_apply, constant]
  apply Finset.sum_congr rfl
  intro m hm
  have hs := congrFun (congrFun (dualConstantMatrix_symmetric (2*(m.val+1)+1) c) i) j
  change dualConstantMatrix (2*(m.val+1)+1) c j i =
    dualConstantMatrix (2*(m.val+1)+1) c i j at hs
  rw [hs]

/-- Literal substitution Z=sum a_m X_m reproduces the weighted single-value pencils. -/
theorem entry_eval_coupled {k h K : ℕ} (a : Fin k → ℤ)
    (c : Matrix (Fin h) (Fin (K+1)) ℚ) (x : Fin k → ℝ) (i j : Fin h) :
    Polynomial.eval₂ (Rat.castHom ℝ) (∑ m, (a m : ℝ) * x m) (entry a c i j) =
      ∑ m, (a m : ℝ) * Polynomial.eval₂ (Rat.castHom ℝ) (x m)
        (Real.dualEntry (2*(m.val+1)+1) c i j) := by
  simp only [entry, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X,
    Rat.coe_castHom]
  simp only [constant, Real.dualEntry, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X,
    Rat.cast_sum, Rat.cast_mul, Rat.cast_intCast, Rat.coe_castHom,
    mul_add, Finset.mul_sum, Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro m hm
  ring

theorem entry_derivative {k h K : ℕ} (a : Fin k → ℤ)
    (c : Matrix (Fin h) (Fin (K+1)) ℚ) (i j : Fin h) :
    (entry a c i j).derivative =
      C ((c * c.transpose) i j) := by
  simp [entry, dualSlopeMatrix, Matrix.mul_apply]

def spectralPencil {k h K : ℕ} (a : Fin k → ℤ)
    (c : Matrix (Fin h) (Fin (K+1)) ℚ)
    (hc : coefficientRowsSeparate (realCoefficients c)) : PositiveSlopePencil h where
  constant := (constant a c).map (fun q : ℚ => (q : ℝ))
  slope := coefficientSlope (realCoefficients c)
  constant_symmetric := (constant_symmetric a c).map _
  slope_posDef := coefficientSlope_posDef _ hc

theorem spectralPencil_matrix {k h K : ℕ} (a : Fin k → ℤ)
    (c : Matrix (Fin h) (Fin (K+1)) ℚ)
    (hc : coefficientRowsSeparate (realCoefficients c)) :
    (spectralPencil a c hc).polynomialMatrix =
      fun i j => (Polynomial.mapRingHom (Rat.castHom ℝ)) (entry a c i j) := by
  funext i j
  change C ((constant a c i j : ℚ) : ℝ) +
      X * C (∑ r, (c i r : ℝ) * (c j r : ℝ)) =
    (C (constant a c i j) + C (dualSlopeMatrix c i j) * X).map (Rat.castHom ℝ)
  rw [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C,
    Polynomial.map_C, Polynomial.map_X]
  simp only [dualSlopeMatrix, map_sum, map_mul, Rat.coe_castHom]
  ring

theorem spectralPencil_det {k h K : ℕ} (a : Fin k → ℤ)
    (c : Matrix (Fin h) (Fin (K+1)) ℚ)
    (hc : coefficientRowsSeparate (realCoefficients c)) :
    (spectralPencil a c hc).detPolynomial = Real.realPolynomial (delta a c) := by
  unfold PositiveSlopePencil.detPolynomial
  rw [spectralPencil_matrix]
  exact ((Polynomial.mapRingHom (Rat.castHom ℝ)).map_det (entry a c)).symm

/-- Exact Theorem 6.7(1), including the manuscript's rational polynomial hypothesis. -/
theorem theorem_6_7_part_one {k h K : ℕ} (a : Fin k → ℤ)
    (A : Fin h → ℚ[X]) (hA : LinearIndependent ℚ A)
    (hdegree : ∀ i, (A i).natDegree ≤ K) :
    let c := polynomialCoefficients K A
    (dualSlopeMatrix c).PosDef ∧
    (delta a c).natDegree = h ∧
    ∀ z : ℂ, Polynomial.eval₂ (algebraMap ℚ ℂ) z (delta a c) = 0 → z.im = 0 := by
  dsimp only
  let c := polynomialCoefficients K A
  have hi : Function.Injective c.vecMul := Matrix.vecMul_injective_iff.mpr
    (polynomialCoefficients_independent A hA hdegree)
  have hs := real_rows_separate_of_rational_injective c hi
  refine ⟨?_, ?_, ?_⟩
  · change (c * c.transpose).PosDef
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.PosDef.mul_conjTranspose_self c hi
  · have hd := positiveSlopePencil_degree (spectralPencil a c hs)
    rw [spectralPencil_det, Real.realPolynomial, Polynomial.natDegree_map] at hd
    exact hd
  · intro z hz
    apply positiveSlopePencil_every_complex_root_real (spectralPencil a c hs) z
    rw [spectralPencil_det, Real.realPolynomial, Polynomial.eval₂_map]
    rw [Subsingleton.elim ((algebraMap ℝ ℂ).comp (Rat.castHom ℝ)) (algebraMap ℚ ℂ)]
    exact hz

end ManuscriptChain.Multiweight

#print axioms ManuscriptChain.Multiweight.theorem_6_7_part_one
#print axioms ManuscriptChain.Multiweight.entry_eval_coupled
