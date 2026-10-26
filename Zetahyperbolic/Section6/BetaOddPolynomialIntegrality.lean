import Zetahyperbolic.Section6.BetaOddPartialFractions
import Mathlib.NumberTheory.Padics.PadicNumbers

/-! The polynomial-quotient contribution in Theorem 6.5 is integral at
every odd prime. This is proved for the actual Euler moments and actual
monic quotient; it is not an assumed matrix-entry integrality premise. -/

noncomputable section
open scoped BigOperators
open Polynomial
namespace ManuscriptChain.BetaOddPolynomialIntegrality
open BetaOddResidueSigns BetaOddPencil

def integerPrefix (N : ℕ) : ℤ[X] :=
  ∏ j ∈ Finset.range N, (X + C ((2 * (j : ℤ) + 1) ^ 2))

def integerTail (N K : ℕ) : ℤ[X] :=
  ∏ j ∈ Finset.Ico N K, (X + C ((2 * (j : ℤ) + 1) ^ 2))

def integerNumerator (N m i j : ℕ) : ℤ[X] :=
  integerPrefix N ^ (2 * m - 1) * X ^ (i + j)

def integerQuotient (N K m i j : ℕ) : ℤ[X] :=
  integerNumerator N m i j /ₘ integerTail N K

theorem integerPrefix_map (N : ℕ) :
    (integerPrefix N).map (Int.castRingHom ℚ) = oddPrefix N := by
  simp [integerPrefix, oddPrefix, oddSquare, Polynomial.map_prod]

theorem integerTail_map (N K : ℕ) :
    (integerTail N K).map (Int.castRingHom ℚ) = tail N K := by
  simp [integerTail, tail, oddSquare, Polynomial.map_prod]

theorem integerNumerator_map (N m i j : ℕ) :
    (integerNumerator N m i j).map (Int.castRingHom ℚ) = numerator N m i j := by
  simp [integerNumerator, numerator, integerPrefix_map]

theorem integerQuotient_map (N K m i j : ℕ) :
    (integerQuotient N K m i j).map (Int.castRingHom ℚ) = quotient N K m i j := by
  have hm : (integerTail N K).Monic :=
    Polynomial.monic_prod_of_monic _ _ (fun _ _ => monic_X_add_C _)
  rw [integerQuotient, Polynomial.map_divByMonic _ hm,
    integerNumerator_map, integerTail_map]
  rfl

theorem quotient_coeff_integer (N K m i j e : ℕ) :
    (quotient N K m i j).coeff e =
      ((integerQuotient N K m i j).coeff e : ℚ) := by
  rw [← integerQuotient_map, Polynomial.coeff_map]
  rfl

theorem monomialMoment_norm_le_one (p e : ℕ) [Fact p.Prime] (hp : 3 ≤ p) :
    ‖(monomialMoment e : ℚ_[p])‖ ≤ 1 := by
  have hnd : ¬p ∣ 2 := Nat.not_dvd_of_pos_of_lt (by norm_num) (by omega)
  have hc : p.Coprime 4 := by
    have htwo : p.Coprime 2 := (Fact.out : p.Prime).coprime_iff_not_dvd.mpr hnd
    simpa using htwo.pow_right 2
  have hfour : ‖(4 : ℚ_[p])‖ = 1 := by
    exact Padic.norm_natCast_eq_one_iff.mpr hc
  have hE : ‖(eulerEven e : ℚ_[p])‖ ≤ 1 := Padic.norm_int_le_one _
  have hC : ‖(Nat.choose (2 * e + 3) 3 : ℚ_[p])‖ ≤ 1 := by
    simpa using Padic.norm_int_le_one (p := p) (Nat.choose (2 * e + 3) 3 : ℤ)
  simp only [monomialMoment, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_one, Rat.cast_intCast, Rat.cast_natCast, Rat.cast_ofNat,
    norm_mul, norm_div, norm_pow, norm_neg, norm_one, one_pow,
    one_mul, hfour, div_one]
  exact mul_le_one₀ hE (norm_nonneg _) hC

private theorem finite_sum_norm_le_one (p : ℕ) [Fact p.Prime]
    {ι : Type*} (S : Finset ι) (f : ι → ℚ_[p])
    (hf : ∀ i ∈ S, ‖f i‖ ≤ 1) : ‖∑ i ∈ S, f i‖ ≤ 1 := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
    rw [Finset.sum_insert ha]
    exact (Padic.nonarchimedean _ _).trans (max_le
      (hf a (Finset.mem_insert_self a S))
      (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))))

theorem polynomialMoment_map_integer_norm_le_one (p : ℕ) [Fact p.Prime]
    (hp : 3 ≤ p) (Q : ℤ[X]) :
    ‖(polynomialMoment (Q.map (Int.castRingHom ℚ)) : ℚ_[p])‖ ≤ 1 := by
  rw [polynomialMoment, Polynomial.sum_def]
  push_cast
  apply finite_sum_norm_le_one p
  intro e he
  rw [Polynomial.coeff_map]
  change ‖((Q.coeff e : ℚ) : ℚ_[p]) * (monomialMoment e : ℚ_[p])‖ ≤ 1
  rw [norm_mul]
  apply mul_le_one₀
  · simpa using Padic.norm_int_le_one (p := p) (Q.coeff e)
  · exact norm_nonneg _
  · exact monomialMoment_norm_le_one p e hp

/-- No odd-prime denominator enters through the polynomial quotient in
the literal beta(4) matrix, for every size and exponent. -/
theorem quotientMoment_norm_le_one (p N K m i j : ℕ) [Fact p.Prime]
    (hp : 3 ≤ p) :
    ‖(polynomialMoment (quotient N K m i j) : ℚ_[p])‖ ≤ 1 := by
  rw [← integerQuotient_map]
  exact polynomialMoment_map_integer_norm_le_one p hp _

end ManuscriptChain.BetaOddPolynomialIntegrality

#print axioms ManuscriptChain.BetaOddPolynomialIntegrality.integerQuotient_map
#print axioms ManuscriptChain.BetaOddPolynomialIntegrality.quotientMoment_norm_le_one
