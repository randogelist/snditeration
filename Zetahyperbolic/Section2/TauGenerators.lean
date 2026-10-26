import Zetahyperbolic.Section2.Moments
import Mathlib.Tactic

/-!
# Lemmas 2.2 and 2.3: exact generator identities

The monomial/pole values below are those of Definition 2.1 in `Real`.
The pullback, reflection and difference conclusions are equalities on the
specified generators and their finite coefficient sums. This file does not
construct the full rational-function domain or prove representation invariance.

The reflection proof handles Bernoulli index 1 separately; the manuscript's
claim that only odd monomial degrees contribute is false at degree `2*k`.
-/

noncomputable section
open scoped BigOperators
open Polynomial

namespace ManuscriptChain.Tau

lemma harmonic_succ (s j : ℕ) :
    Real.harmonic s (j + 1) =
      Real.harmonic s j + (((j + 1 : ℕ) : ℚ) ^ s)⁻¹ := by
  simp [Real.harmonic, Finset.sum_range_succ]

/-- The affine pole value from Definition 2.1, with the existing constants. -/
def muPolePoly (k j : ℕ) : ℚ[X] :=
  C ((j : ℚ) ^ (2 * k)) *
      (X - C (Real.harmonic (2 * k + 1) j)) +
    C (1 / (2 * (j : ℚ)) - 1 / (2 * (k : ℚ)))

theorem muPolePoly_eq_existing (k j : ℕ) :
    muPolePoly k j = C (Real.poleConstant k j) + C ((j : ℚ) ^ (2 * k)) * X := by
  simp only [muPolePoly, Real.poleConstant, map_sub, map_add, map_mul, map_neg]
  ring

/-- Auxiliary index map `d(r)` for `r ∈ ℤ`: `d(r) = r` if `r ≥ 0`, and `-r - 1` if `r < 0`. -/
def dIndex (r : ℤ) : ℕ :=
  if 0 ≤ r then r.toNat else (-r - 1).toNat

/-- Reflection invariance of `d(r)`: `d(-1 - r) = d(r)` for all `r ∈ ℤ` (used in Lemma 2.3). -/
lemma dIndex_reflect (r : ℤ) : dIndex (-1 - r) = dIndex r := by
  unfold dIndex
  split_ifs with h1 h2 h2
  · omega
  · rcases le_iff_eq_or_lt.mp h1 with h1eq | h1lt
    · omega
    · omega
  · omega
  · omega

/-- Full binomial convolution of Bernoulli numbers. The exceptional index
n = 1 is handled explicitly because bernoulli 1 = -1/2 while
bernoulli' 1 = 1/2. -/
lemma bernoulli_binomial_sum (n : ℕ) :
    (∑ i ∈ Finset.range (n + 1),
      (Nat.choose n i : ℚ) * bernoulli i) = bernoulli' n := by
  rw [Finset.sum_range_succ, sum_bernoulli]
  by_cases hn : n = 1
  · subst n
    norm_num [bernoulli_one, bernoulli'_one]
  · simp [hn, bernoulli_eq_bernoulli'_of_ne_one hn]

/-- Equation (2.4): Monomial action of the one-variable pullback functional `τ_X^{(2k+1)}(x^d)`. -/
def tauMonomial (k d : ℕ) : ℚ :=
  if 2 * k - 1 ≤ d then
    ((Nat.factorial d : ℚ) /
      ((Nat.factorial (d - (2 * k - 1)) : ℚ) * (Nat.factorial (2 * k) : ℚ))) *
        bernoulli (d - (2 * k - 1))
  else 0

/-- Factorial form of the Bernoulli monomial weight, rewritten using a
binomial coefficient. This is the convolution-ready form of equation (2.4). -/
lemma tauMonomial_eq_choose (k d : ℕ) (hk : 1 ≤ k) :
    tauMonomial k d =
      if 2 * k - 1 ≤ d then
        ((Nat.choose d (2 * k - 1) : ℚ) / (2 * k : ℚ)) *
          bernoulli (d - (2 * k - 1))
      else 0 := by
  unfold tauMonomial
  split_ifs with hd
  · have hfacNat : Nat.factorial (2 * k) =
        (2 * k) * Nat.factorial (2 * k - 1) := by
      rw [show 2 * k = (2 * k - 1) + 1 by omega, Nat.factorial_succ]
      simp
    have hfac : (Nat.factorial (2 * k) : ℚ) =
        (2 * k : ℚ) * (Nat.factorial (2 * k - 1) : ℚ) := by
      exact_mod_cast hfacNat
    have hchoose :
        (Nat.choose d (2 * k - 1) : ℚ) *
            (Nat.factorial (2 * k - 1) : ℚ) *
            (Nat.factorial (d - (2 * k - 1)) : ℚ) =
          (Nat.factorial d : ℚ) := by
      exact_mod_cast Nat.choose_mul_factorial_mul_factorial hd
    rw [hfac, ← hchoose]
    have h2k : (2 * k : ℚ) ≠ 0 := by positivity
    have hfr : (Nat.factorial (2 * k - 1) : ℚ) ≠ 0 := by positivity
    have hfd : (Nat.factorial (d - (2 * k - 1)) : ℚ) ≠ 0 := by positivity
    field_simp [h2k, hfr, hfd] <;> ring
  · rfl

/-- Binomial convolution of the monomial weights reduces to a single
Bernoulli number at the shifted index. This is the main algebraic reduction
needed for the monomial reflection identity. -/
lemma tauMonomial_binomial_convolution (k d : ℕ) (hk : 1 ≤ k)
    (hd : 2 * k - 1 ≤ d) :
    (∑ i ∈ Finset.range (d + 1),
      (Nat.choose d i : ℚ) * tauMonomial k i) =
      ((Nat.choose d (2 * k - 1) : ℚ) / (2 * k : ℚ)) *
        bernoulli' (d - (2 * k - 1)) := by
  have hsubset : Finset.Ico (2 * k - 1) (d + 1) ⊆ Finset.range (d + 1) := by
    intro i hi
    simp only [Finset.mem_Ico, Finset.mem_range] at hi ⊢
    omega
  have hzero : ∀ i ∈ Finset.range (d + 1),
      i ∉ Finset.Ico (2 * k - 1) (d + 1) →
      (Nat.choose d i : ℚ) * tauMonomial k i = 0 := by
    intro i hi hnot
    have hiLt : i < 2 * k - 1 := by
      have hiBound : i < d + 1 := Finset.mem_range.mp hi
      by_contra h
      have hir : 2 * k - 1 ≤ i := by omega
      exact hnot (Finset.mem_Ico.mpr ⟨hir, hiBound⟩)
    simp [tauMonomial, Nat.not_le_of_gt hiLt]
  rw [← Finset.sum_subset hsubset hzero]
  rw [Finset.sum_Ico_eq_sum_range]
  have hlen : d + 1 - (2 * k - 1) = d - (2 * k - 1) + 1 := by omega
  rw [hlen]
  calc
    (∑ i ∈ Finset.range (d - (2 * k - 1) + 1),
        (Nat.choose d ((2 * k - 1) + i) : ℚ) *
          tauMonomial k ((2 * k - 1) + i)) =
      ∑ i ∈ Finset.range (d - (2 * k - 1) + 1),
        ((Nat.choose d (2 * k - 1) : ℚ) / (2 * k : ℚ)) *
          ((Nat.choose (d - (2 * k - 1)) i : ℚ) * bernoulli i) := by
      apply Finset.sum_congr rfl
      intro i hi
      have hwt := tauMonomial_eq_choose k ((2 * k - 1) + i) hk
      have hbound : 2 * k - 1 ≤ (2 * k - 1) + i := by omega
      rw [hwt, if_pos hbound]
      have hidx : (2 * k - 1) + i - (2 * k - 1) = i := by omega
      rw [hidx]
      have hchoose :
          Nat.choose d ((2 * k - 1) + i) *
              Nat.choose ((2 * k - 1) + i) (2 * k - 1) =
            Nat.choose d (2 * k - 1) *
              Nat.choose (d - (2 * k - 1)) i := by
        have h := Nat.choose_mul (n := d) (k := (2 * k - 1) + i)
          (s := 2 * k - 1) (by omega)
        rw [hidx] at h
        exact h
      have hchooseQ :
          (Nat.choose d ((2 * k - 1) + i) : ℚ) *
              (Nat.choose ((2 * k - 1) + i) (2 * k - 1) : ℚ) =
            (Nat.choose d (2 * k - 1) : ℚ) *
              (Nat.choose (d - (2 * k - 1)) i : ℚ) := by
        exact_mod_cast hchoose
      calc
        (Nat.choose d ((2 * k - 1) + i) : ℚ) *
            ((Nat.choose ((2 * k - 1) + i) (2 * k - 1) : ℚ) /
              (2 * k : ℚ) * bernoulli i) =
          (((Nat.choose d ((2 * k - 1) + i) : ℚ) *
            (Nat.choose ((2 * k - 1) + i) (2 * k - 1) : ℚ)) /
              (2 * k : ℚ)) * bernoulli i := by ring
        _ = (((Nat.choose d (2 * k - 1) : ℚ) *
            (Nat.choose (d - (2 * k - 1)) i : ℚ)) /
              (2 * k : ℚ)) * bernoulli i := by rw [hchooseQ]
        _ = ((Nat.choose d (2 * k - 1) : ℚ) / (2 * k : ℚ)) *
            ((Nat.choose (d - (2 * k - 1)) i : ℚ) * bernoulli i) := by ring
    _ = ((Nat.choose d (2 * k - 1) : ℚ) / (2 * k : ℚ)) *
        bernoulli' (d - (2 * k - 1)) := by
      rw [← Finset.mul_sum, bernoulli_binomial_sum]

/-- Simple-pole action of `τ_X^{(2k+1)}((x - r)^{-1}) = H_{d(r)}^{(2k+1)} - X` in `ℚ[X]`. -/
noncomputable def tauPolePoly (k : ℕ) (r : ℤ) : ℚ[X] :=
  Polynomial.C (Real.harmonic (2 * k + 1) (dIndex r)) - Polynomial.X

/-- The simple-pole values are invariant under the reflected integer index.
Together with the sign from substituting x ↦ -1-x, this supplies the pole part
of the Section 2 reflection identity. -/
lemma tauPolePoly_reflect (k : ℕ) (r : ℤ) :
    tauPolePoly k (-1 - r) = tauPolePoly k r := by
  simp [tauPolePoly, dIndex_reflect]

/-- Lemma 2.2 (Pullback identity) on monomials `R(t) = t^e`:
`μ_X^{(s)}(t^e) = τ_X^{(s)}((-1)^e x^{2e + 2k + 1})`. -/
theorem pullback_identity_monomial (k e : ℕ) (hk : 1 ≤ k) :
    Real.monomialMoment k e = (-1 : ℚ) ^ e * tauMonomial k (2 * e + 2 * k + 1) := by
  unfold Real.monomialMoment tauMonomial
  have hcut : 2 * k - 1 ≤ 2 * e + 2 * k + 1 := by omega
  rw [if_pos hcut]
  have hsub : 2 * e + 2 * k + 1 - (2 * k - 1) = 2 * e + 2 := by omega
  rw [hsub]
  ring

lemma affinePoleLeft (a b c : ℚ) :
    Polynomial.C a * (Polynomial.X - Polynomial.C b) + Polynomial.C c =
      Polynomial.C a * Polynomial.X + Polynomial.C (c - a * b) := by
  calc
    _ = Polynomial.C a * Polynomial.X - Polynomial.C (a * b) + Polynomial.C c := by
      rw [mul_sub, Polynomial.C_mul]
    _ = Polynomial.C a * Polynomial.X + (Polynomial.C c - Polynomial.C (a * b)) := by ring
    _ = Polynomial.C a * Polynomial.X + Polynomial.C (c - a * b) := by
      rw [Polynomial.C_sub]

lemma affinePoleRight (a b c : ℚ) :
    Polynomial.C a - Polynomial.C b *
      (Polynomial.C c - Polynomial.X - Polynomial.X) =
      Polynomial.C (2 * b) * Polynomial.X + Polynomial.C (a - b * c) := by
  calc
    _ = Polynomial.C a -
        (Polynomial.C (b * c) - Polynomial.C b * Polynomial.X -
          Polynomial.C b * Polynomial.X) := by
            rw [mul_sub, mul_sub, Polynomial.C_mul]
    _ = Polynomial.C a - Polynomial.C (b * c) +
        Polynomial.C b * Polynomial.X + Polynomial.C b * Polynomial.X := by ring
    _ = Polynomial.C (a - b * c) +
        Polynomial.C b * Polynomial.X + Polynomial.C b * Polynomial.X := by
          rw [Polynomial.C_sub]
    _ = (Polynomial.C b + Polynomial.C b) * Polynomial.X +
        Polynomial.C (a - b * c) := by ring
    _ = Polynomial.C (b + b) * Polynomial.X +
        Polynomial.C (a - b * c) := by rw [Polynomial.C_add]
    _ = Polynomial.C (2 * b) * Polynomial.X +
        Polynomial.C (a - b * c) := by congr 1 <;> ring

/-- Lemma 2.2 (Pullback identity) on simple poles `R(t) = (t + j^2)^{-1}` (`j ≥ 1`):
`μ_X^{(2k+1)}((t + j^2)^{-1}) = -τ_X^{(2k+1)}(x^{2k-1}) - (j^{2k}/2)(τ_X((x-j)^{-1}) + τ_X((x+j)^{-1}))`. -/
theorem pullback_identity_pole (k j : ℕ) (hk : 1 ≤ k) (hj : 1 ≤ j) :
    muPolePoly k j =
      Polynomial.C (-tauMonomial k (2 * k - 1)) -
        Polynomial.C ((j : ℚ) ^ (2 * k) / 2) *
          (tauPolePoly k (j : ℤ) + tauPolePoly k (-(j : ℤ))) := by
  have hjq : (j : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 1) hj))
  have h2kq : (2 * (k : ℚ)) ≠ 0 := by positivity
  have hdpos : dIndex (j : ℤ) = j := by
    simp [dIndex, Int.toNat_of_nonneg (by omega : (0 : ℤ) ≤ (j : ℤ))]
  have hdneg : dIndex (-(j : ℤ)) = j - 1 := by
    have hneg : ¬ (0 : ℤ) ≤ -(j : ℤ) := by omega
    unfold dIndex
    rw [if_neg hneg]
    have hcast : -(-(j : ℤ)) - 1 = ((j - 1 : ℕ) : ℤ) := by omega
    rw [hcast]
    simp
  have hidx : j - 1 + 1 = j := by omega
  have hrec : Real.harmonic (2 * k + 1) j =
      Real.harmonic (2 * k + 1) (j - 1) + (((j : ℚ) ^ (2 * k + 1))⁻¹) := by
    have hs := harmonic_succ (2 * k + 1) (j - 1)
    rw [hidx] at hs
    exact hs
  have htm : tauMonomial k (2 * k - 1) = (1 : ℚ) / (2 * k) := by
    rw [tauMonomial_eq_choose k (2 * k - 1) hk]
    simp
  have hpow : (j : ℚ) ^ (2 * k + 1) =
      (j : ℚ) ^ (2 * k) * (j : ℚ) := by
    rw [show 2 * k + 1 = (2 * k) + 1 by omega, pow_succ]
  have hsum :
      tauPolePoly k (j : ℤ) + tauPolePoly k (-(j : ℤ)) =
        Polynomial.C (Real.harmonic (2 * k + 1) j +
          Real.harmonic (2 * k + 1) (j - 1)) -
          Polynomial.X - Polynomial.X := by
    unfold tauPolePoly
    rw [hdpos, hdneg]
    calc
      (Polynomial.C (Real.harmonic (2 * k + 1) j) - Polynomial.X) +
          (Polynomial.C (Real.harmonic (2 * k + 1) (j - 1)) - Polynomial.X) =
        (Polynomial.C (Real.harmonic (2 * k + 1) j) +
          Polynomial.C (Real.harmonic (2 * k + 1) (j - 1))) -
          Polynomial.X - Polynomial.X := by ring
      _ = _ := by rw [Polynomial.C_add]
  have hIntercept :
      1 / (2 * (j : ℚ)) - 1 / (2 * (k : ℚ)) -
          (j : ℚ) ^ (2 * k) * Real.harmonic (2 * k + 1) j =
        -1 / (2 * (k : ℚ)) -
          ((j : ℚ) ^ (2 * k) / 2) *
            (Real.harmonic (2 * k + 1) j +
              Real.harmonic (2 * k + 1) (j - 1)) := by
    rw [hrec, hpow]
    field_simp [hjq, h2kq, pow_ne_zero _ hjq] <;> ring
  unfold muPolePoly
  rw [hsum, htm, affinePoleLeft, affinePoleRight]
  have hslope : 2 * ((j : ℚ) ^ (2 * k) / 2) = (j : ℚ) ^ (2 * k) := by
    field_simp
  rw [hslope, hIntercept]
  congr 1 <;> ring

/-- Lemma 2.3 (1) (Reflection identity for `τ_X^{(s)}` on simple poles):
`τ_X^{(s)}((-1 - x - r)^{-1}) = -τ_X^{(s)}((x - r)^{-1})`. -/
theorem tau_reflection_pole (k : ℕ) (r : ℤ) :
    -tauPolePoly k (-1 - r) = -tauPolePoly k r := by
  unfold tauPolePoly
  rw [dIndex_reflect]

/-- Lemma 2.3 (1) (Reflection identity for `τ_X^{(s)}` on monomials):
For `s = 2k + 1 ≥ 3`, `∑_{i=0}^d C(d,i) (-1)^d τ_X^{(s)}(x^i) = -τ_X^{(s)}(x^d)`. -/
theorem tau_reflection_monomial (k d : ℕ) (hk : 1 ≤ k) :
    (-1 : ℚ) ^ d * (∑ i ∈ Finset.range (d + 1), (Nat.choose d i : ℚ) * tauMonomial k i) =
      -tauMonomial k d := by
  by_cases hd : 2 * k - 1 ≤ d
  · rw [tauMonomial_binomial_convolution k d hk hd]
    rw [tauMonomial_eq_choose k d hk, if_pos hd]
    let n := d - (2 * k - 1)
    have hdn : d - (2 * k - 1) = n := rfl
    rw [hdn]
    by_cases hn0 : n = 0
    · have hdEq : d = 2 * k - 1 := by dsimp [n] at hn0; omega
      rw [hdEq, hn0]
      have hodd : Odd (2 * k - 1) := by
        refine ⟨k - 1, ?_⟩
        omega
      have hpow : (-1 : ℚ) ^ (2 * k - 1) = -1 := hodd.neg_one_pow
      simp [hpow, bernoulli_zero, bernoulli'_zero] <;> ring
    · by_cases hn1 : n = 1
      · have hdEq : d = 2 * k := by dsimp [n] at hn1; omega
        rw [hdEq, hn1]
        have heven : Even (2 * k) := ⟨k, by omega⟩
        have hpow : (-1 : ℚ) ^ (2 * k) = 1 := heven.neg_one_pow
        simp [hpow, bernoulli_one, bernoulli'_one] <;> ring
      · have hBern : bernoulli' n = bernoulli n :=
          (bernoulli_eq_bernoulli'_of_ne_one hn1).symm
        by_cases hodd : Odd n
        · have hB : bernoulli n = 0 :=
            bernoulli_eq_zero_of_odd hodd (by omega)
          have hBp : bernoulli' n = 0 :=
            bernoulli'_eq_zero_of_odd hodd (by omega)
          simp [hB, hBp]
        · have heven : Even n := Nat.not_odd_iff_even.mp hodd
          have hpow : (-1 : ℚ) ^ d = -1 := by
            have hdOdd : Odd d := by
              have hrOdd : Odd (2 * k - 1) := by
                refine ⟨k - 1, ?_⟩
                omega
              have hsum : Odd ((2 * k - 1) + n) := by
                rcases hrOdd with ⟨a, ha⟩
                rcases heven with ⟨b, hb⟩
                refine ⟨a + b, ?_⟩
                omega
              have hdEq : d = (2 * k - 1) + n := by dsimp [n]; omega
              rw [hdEq]
              exact hsum
            exact hdOdd.neg_one_pow
          rw [hBern, hpow]
          ring
  · have hzero : ∀ i ∈ Finset.range (d + 1), tauMonomial k i = 0 := by
      intro i hi
      have hiLt : i < 2 * k - 1 := by
        have hiLe : i ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        omega
      simp [tauMonomial, Nat.not_le_of_gt hiLt]
    have hsum :
        (∑ i ∈ Finset.range (d + 1),
          (Nat.choose d i : ℚ) * tauMonomial k i) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      simp [hzero i hi]
    have hweight : tauMonomial k d = 0 := by
      simp [tauMonomial, hd]
    simp [hsum, hweight]

/-- Lemma 2.3 (2) (Difference identity for `τ_X^{(s)}`):
For `h(x) = (x - r)^{-1}` with `r ≠ 0` (including `r = 1`),
`τ_X^{(2k+1)}((x - (r - 1))^{-1}) - τ_X^{(2k+1)}((x - r)^{-1}) = -(r : ℚ)^{-(2k+1)}`. -/
theorem tau_difference_pole (k : ℕ) (r : ℤ) (hr0 : r ≠ 0) :
    tauPolePoly k (r - 1) - tauPolePoly k r =
      Polynomial.C (-((r : ℚ) ^ (2 * k + 1))⁻¹) := by
  have hcases : r ≤ -1 ∨ 1 ≤ r := by omega
  rcases hcases with hneg | hpos
  · have hidx : dIndex (r - 1) = dIndex r + 1 := by
      have hnot1 : ¬ (0 : ℤ) ≤ r - 1 := by omega
      have hnot : ¬ (0 : ℤ) ≤ r := by omega
      have hidxInt : ((dIndex (r - 1) : ℕ) : ℤ) =
          (dIndex r : ℕ) + 1 := by
        unfold dIndex
        simp only [if_neg hnot1, if_neg hnot]
        have harg : -(r - 1) - 1 = -r := by omega
        rw [harg]
        have hneg0 : (0 : ℤ) ≤ -r := by omega
        have hneg1 : (0 : ℤ) ≤ -r - 1 := by omega
        rw [Int.toNat_of_nonneg hneg0, Int.toNat_of_nonneg hneg1]
        omega
      exact_mod_cast hidxInt
    have hrec := harmonic_succ (2 * k + 1) (dIndex r)
    unfold tauPolePoly
    rw [hidx]
    have hrec' : Real.harmonic (2 * k + 1) (dIndex r + 1) =
        Real.harmonic (2 * k + 1) (dIndex r) +
          (((dIndex r + 1 : ℕ) : ℚ) ^ (2 * k + 1))⁻¹ := hrec
    rw [hrec']
    have hdm : dIndex (r - 1) = (-r).toNat := by
      unfold dIndex
      rw [if_neg (by omega : ¬ (0 : ℤ) ≤ r - 1)]
      have harg : -(r - 1) - 1 = -r := by omega
      rw [harg]
    have hidxNat : dIndex r + 1 = (-r).toNat := by
      rw [← hidx, hdm]
    have hcastInt : ((dIndex r + 1 : ℕ) : ℤ) = -r := by
      rw [hidxNat]
      exact Int.toNat_of_nonneg (by omega)
    have hcast : ((dIndex r + 1 : ℕ) : ℚ) = -(r : ℚ) := by
      exact_mod_cast hcastInt
    rw [hcast]
    rw [neg_pow]
    have hpow : (-1 : ℚ) ^ (2 * k + 1) = -1 := by
      have hodd : Odd (2 * k + 1) := ⟨k, by omega⟩
      exact hodd.neg_one_pow
    rw [hpow]
    simp only [Polynomial.C_add, Polynomial.C_sub, Polynomial.C_neg, neg_one_mul, inv_neg]
    ring
  · have hidx : dIndex (r - 1) + 1 = dIndex r := by
      have hrnonneg : (0 : ℤ) ≤ r := by omega
      have hrprev : (0 : ℤ) ≤ r - 1 := by omega
      have hidxInt : ((dIndex (r - 1) : ℕ) : ℤ) + 1 =
          (dIndex r : ℕ) := by
        unfold dIndex
        simp only [if_pos hrprev, if_pos hrnonneg]
        rw [Int.toNat_of_nonneg hrprev, Int.toNat_of_nonneg hrnonneg]
        omega
      exact_mod_cast hidxInt
    unfold tauPolePoly
    rw [← hidx]
    have hrec := harmonic_succ (2 * k + 1) (dIndex (r - 1))
    rw [hrec]
    have hcastInt : ((dIndex (r - 1) + 1 : ℕ) : ℤ) = r := by
      rw [hidx]
      unfold dIndex
      simp only [if_pos (by omega : (0 : ℤ) ≤ r)]
      exact Int.toNat_of_nonneg (by omega)
    have hcast : ((dIndex (r - 1) + 1 : ℕ) : ℚ) = (r : ℚ) := by
      exact_mod_cast hcastInt
    rw [hcast]
    simp only [Polynomial.C_add, Polynomial.C_sub, Polynomial.C_neg]
    ring


/-- Polynomial part of the auxiliary functional, as an actual linear map. -/
def tauPolynomial (k : ℕ) : ℚ[X] →ₗ[ℚ] ℚ :=
  Polynomial.lsum fun d => tauMonomial k d • LinearMap.id

@[simp] theorem tauPolynomial_monomial (k d : ℕ) (a : ℚ) :
    tauPolynomial k (Polynomial.monomial d a) = a * tauMonomial k d := by
  simp [tauPolynomial, Polynomial.lsum, mul_comm]

@[simp] theorem tauPolynomial_X_pow (k d : ℕ) :
    tauPolynomial k ((X : ℚ[X]) ^ d) = tauMonomial k d := by
  rw [← Polynomial.monomial_one_right_eq_X_pow]
  simp

lemma tauPolynomial_one_add_X_pow (k d : ℕ) :
    tauPolynomial k ((1 + X : ℚ[X]) ^ d) =
      ∑ i ∈ Finset.range (d + 1), (Nat.choose d i : ℚ) * tauMonomial k i := by
  rw [add_comm (1 : ℚ[X]), add_pow, map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [one_pow, mul_one]
  rw [show (Nat.choose d i : ℚ[X]) = C (Nat.choose d i : ℚ) by simp,
    mul_comm, C_mul_X_pow_eq_monomial, tauPolynomial_monomial]

/-- Reflection holds on the full polynomial part, including the B₁ exception. -/
theorem tauPolynomial_reflection (k : ℕ) (hk : 1 ≤ k) (p : ℚ[X]) :
    tauPolynomial k (p.comp (-1 - X)) = -tauPolynomial k p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [Polynomial.add_comp, hp, hq, add_comm]
  | monomial d a =>
    rw [Polynomial.monomial_comp, ← Polynomial.smul_eq_C_mul, map_smul,
      tauPolynomial_monomial]
    have hpow : (-1 - X : ℚ[X]) ^ d =
        (-1 : ℚ) ^ d • (1 + X : ℚ[X]) ^ d := by
      rw [Polynomial.smul_eq_C_mul, map_pow]
      simp only [map_neg, map_one]
      rw [← mul_pow]
      congr 1
      ring
    rw [hpow, map_smul, tauPolynomial_one_add_X_pow]
    change a * ((-1 : ℚ) ^ d * _) = -(a * tauMonomial k d)
    rw [tau_reflection_monomial k d hk]
    ring

/-- The existing polynomial moment formula, packaged as a linear map. -/
def muPolynomial (k : ℕ) : ℚ[X] →ₗ[ℚ] ℚ :=
  Polynomial.lsum fun d => Real.monomialMoment k d • LinearMap.id

@[simp] theorem muPolynomial_apply (k : ℕ) (p : ℚ[X]) :
    muPolynomial k p = Real.polynomialMoment k p := by
  simp [muPolynomial, Polynomial.lsum, Polynomial.sum, Real.polynomialMoment, mul_comm]

@[simp] theorem muPolynomial_monomial (k d : ℕ) (a : ℚ) :
    muPolynomial k (Polynomial.monomial d a) = a * Real.monomialMoment k d := by
  simp [muPolynomial, Polynomial.lsum, mul_comm]

/-- Exact polynomial substitution underlying the monomial pullback. -/
lemma monomial_pullback_polynomial (k e : ℕ) (a : ℚ) :
    (X : ℚ[X]) ^ (2 * k + 1) * (Polynomial.monomial e a).comp (-X ^ 2) =
      Polynomial.monomial (2 * e + 2 * k + 1) (a * (-1) ^ e) := by
  have hneg : (-X ^ 2 : ℚ[X]) ^ e = C ((-1 : ℚ) ^ e) * X ^ (2 * e) := by
    calc
      _ = ((-1 : ℚ[X]) * X ^ 2) ^ e := by congr 1; ring
      _ = (-1 : ℚ[X]) ^ e * (X ^ 2) ^ e := mul_pow _ _ _
      _ = _ := by simp only [map_pow, map_neg, map_one, pow_mul]
  rw [Polynomial.monomial_comp, hneg, ← Polynomial.C_mul_X_pow_eq_monomial, map_mul]
  calc
    _ = (C a * C ((-1 : ℚ) ^ e)) * (X ^ (2 * k + 1) * X ^ (2 * e)) := by ring
    _ = _ := by rw [← pow_add]; congr 2 <;> omega

/-- Lemma 2.2 on every actual polynomial, using Definition 2.1's moments. -/
theorem pullback_identity_polynomial (k : ℕ) (hk : 1 ≤ k) (p : ℚ[X]) :
    tauPolynomial k (X ^ (2 * k + 1) * p.comp (-X ^ 2)) =
      Real.polynomialMoment k p := by
  rw [← muPolynomial_apply]
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [Polynomial.add_comp, mul_add, map_add, hp, hq]
  | monomial e a =>
    rw [monomial_pullback_polynomial, tauPolynomial_monomial, muPolynomial_monomial,
      pullback_identity_monomial k e hk]
    ring

end ManuscriptChain.Tau
