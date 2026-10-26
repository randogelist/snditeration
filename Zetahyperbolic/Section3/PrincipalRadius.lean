import Zetahyperbolic.Section3.CauchyInterlacing

/-!
# Monotonicity of the sharp principal root radius

The operator norms increase under principal enlargement, so their positive
reciprocals decrease. A positivity premise on the smaller norm excludes the
actual constant-polynomial case exhibited in `PrincipalDegreeLoss`.
-/
noncomputable section
open Matrix Polynomial
namespace ManuscriptChain.Cauchy

variable {n r : ℕ}

/-- Every restricted eigenvalue lies between the full spectral extrema bounds. -/
theorem principal_eigenvalue_abs_le (p : Spectral.SymmetricAffinePencil n)
    (hp : p.base.PosDef) (choose : Fin r → Fin n) (hchoose : Function.Injective choose)
    (i : Fin r) :
    |Spectral.actualEigenvalues (principalPencil p choose) i| ≤ Spectral.actualOperatorNorm p := by
  let b := Spectral.actualEigenvalues (principalPencil p choose)
  let a := Spectral.actualEigenvalues p
  let N := Spectral.actualOperatorNorm p
  have ha (j : Fin n) : -N ≤ a j ∧ a j ≤ N :=
    abs_le.mp (Spectral.actualEigenvalues_abs_le_operatorNorm p j)
  apply abs_le.mpr
  constructor
  · by_contra hbad
    have hbi : b i < -N := lt_of_not_ge hbad
    have hfull : {j | b i < a j} = Set.univ := by
      ext j
      simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
      exact hbi.trans_le (ha j).1
    have hproper : {j | b i < b j} ≠ Set.univ := by
      intro heq
      have hh : i ∈ {j | b i < b j} := by rw [heq]; trivial
      exact (lt_irrefl (b i)) hh
    have hsmall := Set.ncard_lt_card hproper
    have h := (eigenvalue_count_interlacing p hp choose hchoose (b i)).2
    change {j | b i < a j}.ncard + r ≤ {j | b i < b j}.ncard + n at h
    rw [hfull, Set.ncard_univ, Nat.card_fin] at h
    simp only [Nat.card_fin] at hsmall
    omega
  · by_contra hbad
    have hbi : N < b i := lt_of_not_ge hbad
    have hfull : {j | N < a j} = ∅ := by
      ext j
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      exact not_lt.mpr (ha j).2
    have h := (eigenvalue_count_interlacing p hp choose hchoose N).1
    change {j | N < b j}.ncard ≤ {j | N < a j}.ncard at h
    rw [hfull, Set.ncard_empty] at h
    have hpos : 0 < {j | N < b j}.ncard := Set.ncard_pos.mpr ⟨i, hbi⟩
    omega

/-- The norm of the actually whitened restricted pencil cannot exceed the full norm. -/
theorem principal_operatorNorm_le (p : Spectral.SymmetricAffinePencil n)
    (hp : p.base.PosDef) (choose : Fin r → Fin n) (hchoose : Function.Injective choose) :
    Spectral.actualOperatorNorm (principalPencil p choose) ≤ Spectral.actualOperatorNorm p := by
  rw [Spectral.actualOperatorNorm_eq_eigenvalueNorm (principalPencil p choose)]
  apply (pi_norm_le_iff_of_nonneg (show 0 ≤ Spectral.actualOperatorNorm p from norm_nonneg _)).mpr
  intro i
  exact principal_eigenvalue_abs_le p hp choose hchoose i

/-- Root radii decrease under principal enlargement whenever the smaller pencil
has nonzero spectrum. Constant pencils have no nearest finite root. -/
theorem principal_positive_radius_antitone (p : Spectral.SymmetricAffinePencil n)
    (hp : p.base.PosDef) (choose : Fin r → Fin n) (hchoose : Function.Injective choose)
    (hsmall : 0 < Spectral.actualOperatorNorm (principalPencil p choose)) :
    0 < Spectral.actualOperatorNorm p ∧
      1 / Spectral.actualOperatorNorm p ≤
        1 / Spectral.actualOperatorNorm (principalPencil p choose) := by
  have hle := principal_operatorNorm_le p hp choose hchoose
  exact ⟨hsmall.trans_le hle, one_div_le_one_div_of_le hsmall hle⟩

/-- Actual manuscript specialization of the repaired radius monotonicity. -/
theorem actual_principal_positive_radius_antitone (p : Real.Parameters)
    (hp : Real.Admissible p) (choose : Fin r → Fin p.h)
    (hchoose : Function.Injective choose)
    (hsmall : 0 < Spectral.actualOperatorNorm (Principal.manuscriptPrincipalPencil p choose)) :
    1 / Spectral.actualOperatorNorm (Real.manuscriptPencil p) ≤
      1 / Spectral.actualOperatorNorm (Principal.manuscriptPrincipalPencil p choose) :=
  (principal_positive_radius_antitone (Real.manuscriptPencil p) (GRAM_POSITIVE p hp) choose hchoose hsmall).2

end ManuscriptChain.Cauchy

