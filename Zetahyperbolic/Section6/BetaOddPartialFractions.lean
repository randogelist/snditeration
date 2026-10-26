import Zetahyperbolic.Section6.BetaOddPencil
import Zetahyperbolic.Section3.PartialFractionsQuotient
import Mathlib.Algebra.Polynomial.PartialFractions

/-! Exact polynomial partial fractions for the literal odd-square kernel.
This identifies the quotient and residue evaluation in `BetaOddPencil`
without an analytic moment-identification premise. -/

noncomputable section
open scoped BigOperators
open Polynomial
namespace ManuscriptChain.BetaOddPartialFractions
open BetaOddResidueSigns BetaOddPencil

theorem oddPrefix_factorization (N K : ℕ) (hNK : N ≤ K) :
    oddPrefix K = oddPrefix N * tail N K := by
  exact (Finset.prod_range_mul_prod_Ico
    (fun j => (X + C (oddSquare j) : ℚ[X])) hNK).symm

theorem oddPrefix_ne_zero (N : ℕ) : oddPrefix N ≠ 0 :=
  (Polynomial.monic_prod_of_monic _ _ (fun _ _ => monic_X_add_C _)).ne_zero

theorem tail_monic (N K : ℕ) : (tail N K).Monic :=
  Polynomial.monic_prod_of_monic _ _ (fun _ _ => monic_X_add_C _)

theorem tail_derivative_ne_zero (N K a : ℕ) (ha : a ∈ Finset.Ico N K) :
    (derivative (tail N K)).eval (-oddSquare a) ≠ 0 := by
  rw [tail_derivative_eval N K a ha]
  apply Finset.prod_ne_zero_iff.mpr
  intro b hb
  exact sub_ne_zero.mpr (fun h => (Finset.mem_erase.mp hb).1
    (oddSquare_strictMono.injective h))

theorem factors_pairwise_coprime (N K : ℕ) :
    Set.Pairwise (↑(Finset.Ico N K) : Set ℕ)
      (fun a b : ℕ => IsCoprime (X + C (oddSquare a)) (X + C (oddSquare b))) := by
  intro a ha b hb hab
  have hd : oddSquare a - oddSquare b ≠ 0 :=
    sub_ne_zero.mpr (fun h => hab (oddSquare_strictMono.injective h))
  refine ⟨C ((oddSquare a - oddSquare b)⁻¹),
    -C ((oddSquare a - oddSquare b)⁻¹), ?_⟩
  calc
    _ = C ((oddSquare a - oddSquare b)⁻¹) * C (oddSquare a - oddSquare b) := by
      rw [Polynomial.C_sub]
      ring
    _ = 1 := by rw [← Polynomial.C_mul]; simp [hd]

structure Decomposition (N K : ℕ) (f : ℚ[X]) where
  quotient : ℚ[X]
  remainder : ℕ → ℚ[X]
  remainder_degree : ∀ a ∈ Finset.Ico N K,
    (remainder a).degree < (X + C (oddSquare a)).degree
  numerator_eq : f = quotient * tail N K +
    ∑ a ∈ Finset.Ico N K, remainder a *
      ∏ b ∈ (Finset.Ico N K).erase a, (X + C (oddSquare b))

theorem decomposition_exists (N K : ℕ) (f : ℚ[X]) : Nonempty (Decomposition N K f) := by
  classical
  obtain ⟨q, r, hr, hf⟩ :=
    Polynomial.eq_quo_mul_prod_add_sum_rem_mul_prod
      (f := f) (s := Finset.Ico N K)
      (g := fun a : ℕ => X + C (oddSquare a))
      (hg := fun _ _ => monic_X_add_C _) (hgg := factors_pairwise_coprime N K)
  exact ⟨⟨q, r, hr, hf⟩⟩

def data (N K : ℕ) (f : ℚ[X]) : Decomposition N K f :=
  Classical.choice (decomposition_exists N K f)

theorem data_remainder_constant (N K : ℕ) (f : ℚ[X]) (a : ℕ)
    (ha : a ∈ Finset.Ico N K) :
    (data N K f).remainder a = C (((data N K f).remainder a).coeff 0) := by
  apply PartialFractions.polynomial_eq_C_of_degree_lt_one
  simpa only [Polynomial.degree_X_add_C] using (data N K f).remainder_degree a ha

theorem data_quotient_eq (N K : ℕ) (f : ℚ[X]) :
    (data N K f).quotient = f /ₘ tail N K := by
  classical
  let s := Finset.Ico N K
  let g : ℕ → ℚ[X] := fun a => X + C (oddSquare a)
  let fd := data N K f
  let rem : ℚ[X] := ∑ a ∈ s, fd.remainder a * ∏ b ∈ s.erase a, g b
  have hg (a : ℕ) : (g a).Monic := monic_X_add_C _
  have hmonic := tail_monic N K
  have hdegree : rem.degree < (tail N K).degree := by
    change (∑ a ∈ s, fd.remainder a * ∏ b ∈ s.erase a, g b).degree <
      (∏ a ∈ s, g a).degree
    refine (degree_sum_le _ _).trans_lt ((Finset.sup_lt_iff ?_).2 ?_)
    · rw [bot_lt_iff_ne_bot, degree_ne_bot]
      exact hmonic.ne_zero
    · intro a ha
      rw [← Finset.mul_prod_erase s g ha, mul_comm (g a), (hg a).degree_mul]
      refine (degree_mul_le _ _).trans_lt ?_
      have hnb : (∏ b ∈ s.erase a, g b).degree ≠ ⊥ := by
        rw [degree_ne_bot]
        exact (monic_prod_of_monic _ g (fun b _ => hg b)).ne_zero
      rw [add_comm, WithBot.add_lt_add_iff_left hnb]
      exact fd.remainder_degree a ha
  have hidentity : rem + tail N K * fd.quotient = f := by
    rw [fd.numerator_eq]
    change rem + tail N K * fd.quotient = fd.quotient * tail N K + rem
    ring
  exact (div_modByMonic_unique fd.quotient rem hmonic ⟨hidentity, hdegree⟩).1.symm

theorem residue_eq_formula (N K : ℕ) (f : ℚ[X]) (a : ℕ)
    (ha : a ∈ Finset.Ico N K) :
    ((data N K f).remainder a).coeff 0 =
      f.eval (-oddSquare a) / (derivative (tail N K)).eval (-oddSquare a) := by
  classical
  let s := Finset.Ico N K
  let x : ℚ := -oddSquare a
  have ht : (tail N K).eval x = 0 := by
    unfold tail
    rw [eval_prod]
    apply Finset.prod_eq_zero ha
    simp [x]
  have hp (b : ℕ) :
      (∏ c ∈ s.erase b, (X + C (oddSquare c))).eval x =
        ∏ c ∈ s.erase b, (oddSquare c - oddSquare a) := by
    rw [eval_prod]
    apply Finset.prod_congr rfl
    intro c hc
    simp [x, sub_eq_add_neg, add_comm]
  have he : f.eval x = ∑ b ∈ s,
      ((data N K f).remainder b * ∏ c ∈ s.erase b, (X + C (oddSquare c))).eval x := by
    have h := congrArg (Polynomial.eval x) (data N K f).numerator_eq
    rw [eval_add, eval_mul, ht] at h
    simpa only [mul_zero, zero_add, eval_finsetSum] using h
  have hs : (∑ b ∈ s,
      ((data N K f).remainder b * ∏ c ∈ s.erase b, (X + C (oddSquare c))).eval x) =
      ((data N K f).remainder a).coeff 0 *
        ∏ c ∈ s.erase a, (oddSquare c - oddSquare a) := by
    rw [Finset.sum_eq_single a]
    · rw [eval_mul, data_remainder_constant N K f a ha, eval_C, hp a]
    · intro b hb hba
      rw [eval_mul, hp b]
      apply mul_eq_zero.mpr
      right
      apply Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨Ne.symm hba, ha⟩)
      simp
    · exact fun hn => (hn ha).elim
  rw [hs] at he
  rw [tail_derivative_eval N K a ha]
  have hd : (∏ c ∈ s.erase a, (oddSquare c - oddSquare a)) ≠ 0 := by
    rw [← tail_derivative_eval N K a ha]
    exact tail_derivative_ne_zero N K a ha
  exact (eq_div_iff hd).mpr he.symm

/-- The quotient and every residue in the beta matrix are exactly those
of the literal canceled rational kernel. -/
theorem numerator_decomposition (N K m i j : ℕ) :
    numerator N m i j = quotient N K m i j * tail N K +
      ∑ a ∈ Finset.Ico N K, C (residueCoefficient N K m i j a) *
        ∏ b ∈ (Finset.Ico N K).erase a, (X + C (oddSquare b)) := by
  classical
  rw [(data N K (numerator N m i j)).numerator_eq, data_quotient_eq]
  congr 1
  apply Finset.sum_congr rfl
  intro a ha
  rw [data_remainder_constant N K (numerator N m i j) a ha,
    residue_eq_formula N K (numerator N m i j) a ha]
  rfl

/-- Clearing the original denominator recovers the uncanceled manuscript
kernel, including its exact exponent. -/
theorem original_kernel_cross_multiply (N K m i j : ℕ)
    (hNK : N ≤ K) (hm : 1 ≤ m) :
    numerator N m i j * oddPrefix K =
      (oddPrefix N ^ (2 * m) * X ^ (i + j)) * tail N K := by
  rw [oddPrefix_factorization N K hNK]
  have he : 2 * m = (2 * m - 1) + 1 := by omega
  rw [he, pow_succ]
  dsimp [numerator]
  ring

end ManuscriptChain.BetaOddPartialFractions

#print axioms ManuscriptChain.BetaOddPartialFractions.numerator_decomposition
#print axioms ManuscriptChain.BetaOddPartialFractions.original_kernel_cross_multiply
