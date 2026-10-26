import Zetahyperbolic.Section6.BetaOddPencil
import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
# An odd-prime nonunit among the displayed scaled beta moments

Theorem 6.14(1) says every displayed monomial moment has valuation zero
at every odd prime. Its own formula at r=1,e=2 is -25/256, of valuation
two at p=5. Odd-prime integrality does not imply the claimed unit property.
This counterexample is independent of the separate scaling-normalization
conflict in the same theorem.
-/
namespace ManuscriptChain.BetaScaledUnitObstruction

/-- The literal displayed moment in 6.14(1), using the Euler recurrence. -/
def displayedMoment (r e : ℕ) : ℚ :=
  (-1:ℚ)^(r+e) * (BetaOddPencil.eulerEven e : ℚ) / 16^e *
    (Nat.choose (2*e+2*r-1) (2*r-1) : ℚ)

theorem displayed_moment_one_two : displayedMoment 1 2 = -(25:ℚ)/256 := by
  have he : BetaOddPencil.eulerEven 2 = 5 := BetaOddPencil.eulerEven_first_four.2.2.1
  norm_num [displayedMoment, he]

theorem five_unit_denominator : padicValRat 5 (256:ℚ) = 0 := by
  rw [padicValRat.of_nat (p := 5) (n := 256),
    padicValNat.eq_zero_of_not_dvd (by norm_num : ¬5∣256)]
  norm_num

theorem displayed_moment_five_valuation : padicValRat 5 (displayedMoment 1 2) = 2 := by
  letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  rw [displayed_moment_one_two,
    padicValRat.div (by norm_num : -(25:ℚ) ≠ 0) (by norm_num : (256:ℚ) ≠ 0),
    padicValRat.neg, five_unit_denominator]
  rw [show (25:ℚ) = (5:ℚ)^2 by norm_num, padicValRat.pow,
    padicValRat.self (p := 5) (by norm_num)]
  norm_num

theorem printed_odd_prime_unit_claim_false :
    ¬ (∀ r e p : ℕ, 1 ≤ r → Nat.Prime p → 3 ≤ p →
      padicValRat p (displayedMoment r e) = 0) := by
  intro h
  have he := h 1 2 5 (by norm_num) (by norm_num) (by norm_num)
  rw [displayed_moment_five_valuation] at he
  norm_num at he

end ManuscriptChain.BetaScaledUnitObstruction
