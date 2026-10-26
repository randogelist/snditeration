import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

/-! The nonarchimedean determinant estimate used by the paired-monomial
construction. All nonidentity permutation terms are strictly smaller than
the diagonal product, so cancellation of that product is impossible. -/

noncomputable section
open scoped BigOperators

namespace ManuscriptChain.Beukers

private lemma padic_finite_sum_norm_lt_one (p : ℕ) [Fact p.Prime]
    {ι : Type*} (s : Finset ι) (f : ι → ℚ_[p])
    (hf : ∀ i ∈ s, ‖f i‖ < 1) : ‖∑ i ∈ s, f i‖ < 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact (Padic.nonarchimedean _ _).trans_lt
        (max_lt (hf a (Finset.mem_insert_self a s))
          (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))))

private lemma padic_sign_smul_norm (p : ℕ) [Fact p.Prime]
    (u : ℤˣ) (x : ℚ_[p]) : ‖u • x‖ = ‖x‖ := by
  rcases Int.units_eq_one_or u with hu | hu
  · simp [hu, Units.smul_def]
  · simp [hu, Units.smul_def]

/-- A matrix with unit diagonal entries and strictly smaller off-diagonal
entries has determinant of norm one, in every finite dimension. -/
theorem padic_det_norm_eq_one_of_diagonal_dominant
    (p : ℕ) [Fact p.Prime] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℚ_[p])
    (hdiag : ∀ i, ‖M i i‖ = 1)
    (hoff : ∀ i j, i ≠ j → ‖M i j‖ < 1) : ‖M.det‖ = 1 := by
  classical
  let term (σ : Equiv.Perm ι) : ℚ_[p] :=
    Equiv.Perm.sign σ • ∏ i, M (σ i) i
  have hterm (σ : Equiv.Perm ι) :
      ‖term σ‖ = ∏ i, ‖M (σ i) i‖ := by
    dsimp only [term]
    rw [padic_sign_smul_norm, norm_prod]
  have hle (i j : ι) : ‖M i j‖ ≤ 1 := by
    by_cases hij : i = j
    · subst j
      exact (hdiag i).le
    · exact (hoff i j hij).le
  have hone : ‖term (1 : Equiv.Perm ι)‖ = 1 := by
    rw [hterm]
    simp [hdiag]
  have hsmall (σ : Equiv.Perm ι) (hσ : σ ≠ 1) : ‖term σ‖ < 1 := by
    obtain ⟨i, hi⟩ : ∃ i, σ i ≠ i := by
      by_contra h
      push_neg at h
      apply hσ
      ext i
      simpa using h i
    rw [hterm, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
    calc
      _ ≤ ‖M (σ i) i‖ * 1 := mul_le_mul_of_nonneg_left
        (Finset.prod_le_one (fun j _ => norm_nonneg _) (fun j _ => hle (σ j) j))
        (norm_nonneg _)
      _ < 1 := by simpa using hoff (σ i) i hi
  have hsum : ‖∑ σ ∈ (Finset.univ : Finset (Equiv.Perm ι)).erase 1,
      term σ‖ < 1 := by
    apply padic_finite_sum_norm_lt_one
    intro σ hσ
    exact hsmall σ (Finset.ne_of_mem_erase hσ)
  have hsplit : M.det =
      (∑ σ ∈ (Finset.univ : Finset (Equiv.Perm ι)).erase 1, term σ) + term 1 := by
    rw [Matrix.det_apply]
    exact (Finset.sum_erase_add _ _ (Finset.mem_univ (1 : Equiv.Perm ι))).symm
  rw [hsplit, Padic.add_eq_max_of_ne]
  · simpa only [hone] using max_eq_right hsum.le
  · rw [hone]
    exact ne_of_lt hsum

/-- The corresponding exact determinant scaling identity before dividing
by the nonzero normalization factor. -/
theorem padic_det_norm_scaled_diagonal_dominant
    (p : ℕ) [Fact p.Prime] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℚ_[p]) (a : ℚ_[p])
    (hdiag : ∀ i, ‖a * M i i‖ = 1)
    (hoff : ∀ i j, i ≠ j → ‖a * M i j‖ < 1) :
    ‖a‖ ^ Fintype.card ι * ‖M.det‖ = 1 := by
  have h := padic_det_norm_eq_one_of_diagonal_dominant p (a • M)
    (fun i => by simpa only [Matrix.smul_apply, smul_eq_mul] using hdiag i)
    (fun i j hij => by simpa only [Matrix.smul_apply, smul_eq_mul] using hoff i j hij)
  simpa only [Matrix.det_smul, norm_mul, norm_pow] using h

/-- Prime-power normalization gives the exact unscaled determinant norm. -/
theorem padic_det_norm_eq_prime_pow
    (p s : ℕ) [Fact p.Prime] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℚ_[p])
    (hdiag : ∀ i, ‖(p : ℚ_[p]) ^ s * M i i‖ = 1)
    (hoff : ∀ i j, i ≠ j → ‖(p : ℚ_[p]) ^ s * M i j‖ < 1) :
    ‖M.det‖ = (p : ℝ) ^ (s * Fintype.card ι) := by
  have h := padic_det_norm_scaled_diagonal_dominant p M ((p : ℚ_[p]) ^ s)
    hdiag hoff
  have he : ((p : ℝ) ^ (s * Fintype.card ι))⁻¹ * ‖M.det‖ = 1 := by
    simpa only [norm_pow, Padic.norm_p, inv_pow, ← pow_mul] using h
  have hp : (p : ℝ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  exact ((inv_mul_eq_one₀ (pow_ne_zero _ hp)).mp he).symm

/-- Exact rational valuation recovered from the norm in Q_p. -/
theorem rational_valuation_of_prime_power_norm
    (p n : ℕ) [Fact p.Prime] (q : ℚ)
    (hq : ‖(q : ℚ_[p])‖ = (p : ℝ) ^ n) :
    padicValRat p q = -(n : ℤ) := by
  have hp : p.Prime := Fact.out
  have hqne : q ≠ 0 := by
    intro hz
    have hpos : (0 : ℝ) < (p : ℝ) ^ n :=
      pow_pos (by exact_mod_cast hp.pos) n
    simp only [hz, Rat.cast_zero, norm_zero] at hq
    linarith
  rw [Padic.eq_padicNorm, padicNorm.eq_zpow_of_nonzero hqne] at hq
  have he : (p : ℚ) ^ (-padicValRat p q) = (p : ℚ) ^ (n : ℤ) := by
    rw [zpow_natCast]
    exact_mod_cast hq
  have hv := (zpow_right_inj₀
    (show (0 : ℚ) < p by exact_mod_cast hp.pos)
    (show (p : ℚ) ≠ 1 by exact_mod_cast hp.ne_one)).mp he
  omega

end ManuscriptChain.Beukers
