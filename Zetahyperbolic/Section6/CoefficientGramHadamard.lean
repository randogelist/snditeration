import Zetahyperbolic.Section6.CoefficientGramGrowth
import Zetahyperbolic.Section5.DualPencilCCT

/-!
# Theorem 6.10(2): exact finite coefficient bound

The LDL proof below is transferred from the verified companion revision
7250b47ba4d20ba934e890966a9b77a559689cfd. New endpoints retain arbitrary
nonnegative real height exponents and the printed floor dimension.
-/
noncomputable section
open Matrix Filter
open scoped BigOperators Topology

namespace ManuscriptChain.CoefficientGramGrowth

/-- Hadamard's diagonal bound, obtained from the actual LDL decomposition.
No unit-diagonal normalization of the triangular factor is needed. -/
theorem posDef_det_le_prod_diagonal {n : ℕ} {G : Matrix (Fin n) (Fin n) ℝ}
    (hG : G.PosDef) : G.det ≤ ∏ i, G i i := by
  have hD : ∀ i, 0 < LDL.diagEntries hG i := by
    have hd : (LDL.diag hG).PosDef := by
      rw [LDL.diag_eq_lowerInv_conj]
      exact hG.mul_mul_conjTranspose_same
        (Matrix.vecMul_injective_of_invertible (LDL.lowerInv hG))
    intro i
    simpa only [LDL.diag, Matrix.diagonal_apply_eq] using hd.diag_pos (i := i)
  have hLI : (LDL.lowerInv hG).IsLowerTriangular :=
    fun _ _ hij => LDL.lowerInv_triangular hG hij
  have hL : (LDL.lower hG).IsLowerTriangular :=
    Matrix.blockTriangular_inv_of_blockTriangular hLI
  have hdetL := Matrix.det_of_isLowerTriangular (LDL.lower hG) hL
  have hentry (i : Fin n) : G i i =
      ∑ j, LDL.lower hG i j ^ 2 * LDL.diagEntries hG j := by
    calc
      G i i = (LDL.lower hG * LDL.diag hG * (LDL.lower hG)ᴴ) i i :=
        (congrArg (fun A : Matrix (Fin n) (Fin n) ℝ => A i i)
          (LDL.lower_conj_diag hG)).symm
      _ = _ := by
        rw [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.mul_apply]
        simp only [LDL.diag, Matrix.mul_diagonal, Matrix.transpose_apply]
        apply Finset.sum_congr rfl
        intro j hj
        ring
  have hbound (i : Fin n) :
      LDL.lower hG i i ^ 2 * LDL.diagEntries hG i ≤ G i i := by
    rw [hentry]
    exact Finset.single_le_sum
      (fun j _ => mul_nonneg (sq_nonneg _) (hD j).le) (Finset.mem_univ i)
  calc
    G.det = ∏ i, LDL.lower hG i i * LDL.diagEntries hG i * LDL.lower hG i i := by
      calc
        G.det = (LDL.lower hG * LDL.diag hG * (LDL.lower hG)ᴴ).det :=
          (congrArg (fun A : Matrix (Fin n) (Fin n) ℝ => A.det)
            (LDL.lower_conj_diag hG)).symm
        _ = _ := by
          simp only [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.det_mul,
            Matrix.det_transpose, LDL.diag, Matrix.det_diagonal, hdetL,
            Finset.prod_mul_distrib]
    _ = ∏ i, LDL.lower hG i i ^ 2 * LDL.diagEntries hG i := by
      apply Finset.prod_congr rfl
      intro i hi
      ring
    _ ≤ ∏ i, G i i := Finset.prod_le_prod
      (fun i _ => mul_nonneg (sq_nonneg _) (hD i).le) (fun i _ => hbound i)

/-- The exact coefficient-height Hadamard bound, for any real height budget. -/
theorem det_upper_height {h K : ℕ} (C : Matrix (Fin h) (Fin (K + 1)) ℤ)
    (hC : Function.Injective (C.map (Int.castRingHom ℝ)).vecMul)
    {B : ℝ} (hB : 0 ≤ B) (hentry : ∀ i j, |(C i j : ℝ)| ≤ B) :
    (realGram C).det ≤ ((K + 1 : ℕ) : ℝ) ^ h * B ^ (2 * h) := by
  have hp := realGram_posDef C hC
  have hdiag (i : Fin h) : realGram C i i ≤ ((K + 1 : ℕ) : ℝ) * B ^ 2 := by
    change (∑ r : Fin (K + 1), (C i r : ℝ) * (C i r : ℝ)) ≤ _
    calc
      _ ≤ ∑ _r : Fin (K + 1), B ^ 2 := by
        apply Finset.sum_le_sum
        intro r hr
        calc
          (C i r : ℝ) * (C i r : ℝ) = |(C i r : ℝ)| * |(C i r : ℝ)| := by
            rw [← pow_two, ← pow_two, sq_abs]
          _ ≤ B * B := mul_le_mul (hentry i r) (hentry i r) (abs_nonneg _) hB
          _ = B ^ 2 := by ring
      _ = _ := by simp
  calc
    (realGram C).det ≤ ∏ i, realGram C i i := posDef_det_le_prod_diagonal hp
    _ ≤ ∏ _i : Fin h, ((K + 1 : ℕ) : ℝ) * B ^ 2 :=
      Finset.prod_le_prod (fun i _ => (hp.diag_pos (i := i)).le) (fun i _ => hdiag i)
    _ = _ := by
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, mul_pow,
        ← pow_mul]

/-- The printed finite bound in Theorem 6.10(2), for natural height exponents. -/
theorem det_bounds_printed {h K A : ℕ} (C : Matrix (Fin h) (Fin (K + 1)) ℤ)
    (hC : Function.Injective (C.map (Int.castRingHom ℝ)).vecMul)
    (hentry : ∀ i j, |(C i j : ℝ)| ≤ (K : ℝ) ^ A) :
    1 ≤ (realGram C).det ∧
      (realGram C).det ≤ ((K + 1 : ℕ) : ℝ) ^ h * (K : ℝ) ^ (2 * A * h) := by
  refine ⟨one_le_det C hC, ?_⟩
  calc
    (realGram C).det ≤ ((K + 1 : ℕ) : ℝ) ^ h * ((K : ℝ) ^ A) ^ (2 * h) :=
      det_upper_height C hC (by positivity) hentry
    _ = _ := by
      rw [← pow_mul, show A * (2 * h) = 2 * A * h by ring]


end ManuscriptChain.CoefficientGramGrowth

