import Zetahyperbolic.Section6.CoefficientGramHadamard

/-!
# The complete coefficient-growth assertion of Theorem 6.10(2)

The coefficients are those of actual integer polynomials of bounded degree.
Polynomial independence implies real row independence by scalar extension.
The finite bound has an arbitrary nonnegative real height exponent, and the
asymptotic result uses the printed dimension floor(lambda*K).
-/
noncomputable section
open Matrix Filter Polynomial
open scoped BigOperators Topology

namespace ManuscriptChain.CoefficientGramGrowth

def polynomialCoefficients {h K : ℕ} (P : Fin h → ℤ[X]) :
    Matrix (Fin h) (Fin (K + 1)) ℤ := fun i r => (P i).coeff r.val

/-- Truncation loses no linear-independence information within the degree bound. -/
theorem polynomialCoefficients_independent {h K : ℕ} (P : Fin h → ℤ[X])
    (hdeg : ∀ i, (P i).natDegree ≤ K) (hP : LinearIndependent ℤ P) :
    LinearIndependent ℤ (polynomialCoefficients (K := K) P).row := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg
  apply Fintype.linearIndependent_iff.mp hP g
  ext n
  by_cases hn : n < K + 1
  · have he := congrFun hg (⟨n, hn⟩ : Fin (K + 1))
    simpa [polynomialCoefficients, Matrix.row, Polynomial.finsetSum_coeff,
      Polynomial.coeff_smul] using he
  · have hz : ∀ i, (P i).coeff n = 0 := fun i =>
      Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (hdeg i) (by omega))
    simp [Polynomial.finsetSum_coeff, Polynomial.coeff_smul, hz]

set_option backward.isDefEq.respectTransparency false in
/-- Independence of integer polynomials supplies the real full-row-rank premise. -/
theorem polynomialCoefficients_vecMul_injective {h K : ℕ} (P : Fin h → ℤ[X])
    (hdeg : ∀ i, (P i).natDegree ≤ K) (hP : LinearIndependent ℤ P) :
    Function.Injective
      ((polynomialCoefficients (K := K) P).map (Int.castRingHom ℝ)).vecMul := by
  rw [Matrix.vecMul_injective_iff]
  have hi := polynomialCoefficients_independent P hdeg hP
  have he := (linearIndependent_algebraMap_comp_iff (S := ℝ)).2 hi
  simpa [Matrix.row, Matrix.map, Matrix.of, Function.comp_def] using he

/-- This is the slope of the actual rational Beukers pencil, after real embedding. -/
theorem dualSlope_eq_realGram {h K : ℕ} (C : Matrix (Fin h) (Fin (K + 1)) ℤ) :
    (ManuscriptChain.DualAlgebra.dualSlopeMatrix
      (C.map (Int.castRingHom ℚ))).map (Rat.castHom ℝ) = realGram C := by
  ext i j
  simp [ManuscriptChain.DualAlgebra.dualSlopeMatrix, realGram, Matrix.mul_apply]

/-- Exact printed finite bound for an arbitrary real exponent A, including A=0. -/
theorem det_bounds_real_exponent {h K : ℕ} (C : Matrix (Fin h) (Fin (K + 1)) ℤ)
    (hC : Function.Injective (C.map (Int.castRingHom ℝ)).vecMul)
    (A : ℝ) (hA : 0 ≤ A)
    (hentry : ∀ i j, |(C i j : ℝ)| ≤ (K : ℝ) ^ A) :
    1 ≤ (realGram C).det ∧
      (realGram C).det ≤ ((K + 1 : ℕ) : ℝ) ^ h * (K : ℝ) ^ (2 * A * h) := by
  refine ⟨one_le_det C hC, ?_⟩
  calc
    (realGram C).det ≤ ((K + 1 : ℕ) : ℝ) ^ h * ((K : ℝ) ^ A) ^ (2 * h) :=
      det_upper_height C hC (Real.rpow_nonneg (by positivity) _) hentry
    _ = _ := by
      rw [← Real.rpow_mul_natCast (by positivity : (0 : ℝ) ≤ K)]
      have he : A * ((2 * h : ℕ) : ℝ) = 2 * A * (h : ℝ) := by
        push_cast
        ring
      rw [he]

/-- Real polynomial height is bounded by a natural exponent without changing the limit. -/
theorem normalized_log_det_tendsto_zero_real_exponent
    (h : ℕ → ℕ) (C : ∀ K, Matrix (Fin (h K)) (Fin (K + 1)) ℤ)
    (A : ℝ) (hA : 0 ≤ A) (hsize : ∀ K, h K ≤ K + 1)
    (hrows : ∀ K, Function.Injective ((C K).map (Int.castRingHom ℝ)).vecMul)
    (hentry : ∀ K i j, |(C K i j : ℝ)| ≤ (K : ℝ) ^ A) :
    Tendsto (fun K => Real.log (realGram (C K)).det / (K : ℝ) ^ 2) atTop (𝓝 0) := by
  apply normalized_log_det_tendsto_zero h C ⌈A⌉₊ hsize hrows
  intro K i j
  calc
    |(C K i j : ℝ)| ≤ (K : ℝ) ^ A := hentry K i j
    _ ≤ ((K + 1 : ℕ) : ℝ) ^ A :=
      Real.rpow_le_rpow (by positivity) (by exact_mod_cast Nat.le_succ K) hA
    _ ≤ ((K + 1 : ℕ) : ℝ) ^ (⌈A⌉₊ : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le K))
        (Nat.le_ceil A)
    _ = ((K + 1 : ℕ) : ℝ) ^ ⌈A⌉₊ := Real.rpow_natCast _ _

/-- The exact floor dimension in the manuscript lies within the coefficient dimension. -/
theorem floor_dimension_le (lam : ℝ) (hlam : lam ≤ 1) (K : ℕ) :
    ⌊lam * K⌋₊ ≤ K + 1 := by
  apply Nat.floor_le_of_le
  have hK : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  push_cast
  nlinarith

/-- Full Theorem 6.10(2) for actual independent integer polynomial families.
The first conjunct is the exact finite determinant bound for every K;
the second is the asserted vanishing quadratic logarithmic growth. -/
theorem theorem_6_10_part_two
    (lam A : ℝ) (hlam0 : 0 < lam) (hlam1 : lam < 1) (hA : 0 ≤ A)
    (P : ∀ K : ℕ, Fin ⌊lam * K⌋₊ → ℤ[X])
    (hdeg : ∀ K i, (P K i).natDegree ≤ K)
    (hP : ∀ K, LinearIndependent ℤ (P K))
    (hentry : ∀ K i r, |((P K i).coeff r : ℝ)| ≤ (K : ℝ) ^ A) :
    (∀ K, 1 ≤ (realGram (polynomialCoefficients (K := K) (P K))).det ∧
      (realGram (polynomialCoefficients (K := K) (P K))).det ≤
        ((K + 1 : ℕ) : ℝ) ^ ⌊lam * K⌋₊ * (K : ℝ) ^ (2 * A * ⌊lam * K⌋₊)) ∧
    Tendsto (fun K =>
      Real.log (realGram (polynomialCoefficients (K := K) (P K))).det / (K : ℝ) ^ 2)
      atTop (𝓝 0) := by
  have hrows (K : ℕ) := polynomialCoefficients_vecMul_injective (P K) (hdeg K) (hP K)
  constructor
  · intro K
    apply det_bounds_real_exponent _ (hrows K) A hA
    intro i r
    exact hentry K i r.val
  · apply normalized_log_det_tendsto_zero_real_exponent
      (fun K => ⌊lam * K⌋₊)
      (fun K => polynomialCoefficients (K := K) (P K)) A hA
      (floor_dimension_le lam hlam1.le) hrows
    intro K i r
    exact hentry K i r.val

end ManuscriptChain.CoefficientGramGrowth

#print axioms ManuscriptChain.CoefficientGramGrowth.theorem_6_10_part_two
#print axioms ManuscriptChain.CoefficientGramGrowth.dualSlope_eq_realGram
