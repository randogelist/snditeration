import Zetahyperbolic.Section2.PoleDiagonalization
import Mathlib.Data.Sign.Basic
import Mathlib.Algebra.Group.Nat.Even

/-!
# Actual alternating signs of the pole diagonal

Theorem 3.3(3), algebraic sign input: the coefficient at the pole `-a²`
has sign `(-1)^(a-1)`, independently of the odd weight and the positive
multiplicity parameter. No spectral inertia conclusion is assumed here.
-/

noncomputable section
open scoped BigOperators
open Polynomial SignType

namespace ManuscriptChain.PoleDiagonalization

theorem D_eval_sign (N a : ℕ) (ha : N < a) :
    sign ((Real.D N).eval (-(a : ℚ) ^ 2)) = (-1 : SignType) ^ N := by
  simp only [Real.D, Polynomial.eval_prod, Polynomial.eval_add,
    Polynomial.eval_X, Polynomial.eval_C]
  change signHom (∏ j ∈ Finset.range N, (-(a : ℚ) ^ 2 + ((j + 1 : ℕ) : ℚ) ^ 2)) = _
  rw [map_prod]
  have hsign (j : ℕ) (hj : j ∈ Finset.range N) :
      signHom (-(a : ℚ) ^ 2 + ((j + 1 : ℕ) : ℚ) ^ 2) = (-1 : SignType) := by
    apply sign_neg
    have hjN : j < N := Finset.mem_range.mp hj
    have hja : ((j + 1 : ℕ) : ℚ) < a := by exact_mod_cast (show j + 1 < a by omega)
    have hj0 : (0 : ℚ) ≤ ((j + 1 : ℕ) : ℚ) := by positivity
    nlinarith
  rw [Finset.prod_congr rfl hsign]
  simp

theorem tailD_derivative_eval_sign (p : Real.Parameters) (a : ℕ)
    (ha : a ∈ Finset.Icc (p.N + 1) p.K) :
    sign ((derivative (Real.tailD p)).eval (-(a : ℚ) ^ 2)) =
      (-1 : SignType) ^ (a - (p.N + 1)) := by
  rw [tailD_derivative_eval p a ha]
  change signHom (∏ b ∈ (Finset.Icc (p.N + 1) p.K).erase a,
    ((b : ℚ) ^ 2 - (a : ℚ) ^ 2)) = _
  rw [map_prod]
  have hsign (b : ℕ) (hb : b ∈ (Finset.Icc (p.N + 1) p.K).erase a) :
      signHom ((b : ℚ) ^ 2 - (a : ℚ) ^ 2) =
        (if b < a then (-1 : SignType) else 1) := by
    have hne : b ≠ a := (Finset.mem_erase.mp hb).1
    by_cases hba : b < a
    · rw [if_pos hba]
      apply sign_neg
      have hbaR : (b : ℚ) < a := by exact_mod_cast hba
      have hb0 : (0 : ℚ) ≤ b := by positivity
      nlinarith
    · rw [if_neg hba]
      apply sign_pos
      have hab : a < b := by omega
      have habR : (a : ℚ) < b := by exact_mod_cast hab
      have ha0 : (0 : ℚ) ≤ a := by positivity
      nlinarith
  rw [Finset.prod_congr rfl hsign, Finset.prod_ite]
  have hfilter : {b ∈ (Finset.Icc (p.N + 1) p.K).erase a | b < a} =
      Finset.Ico (p.N + 1) a := by
    ext b
    have hbounds := Finset.mem_Icc.mp ha
    simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_Icc, Finset.mem_Ico]
    omega
  rw [hfilter]
  simp

/-- Exact signs of the actual manuscript residues. -/
theorem poleWeight_sign (p : Real.Parameters) (hm : 0 < p.m) (i : Fin p.h) :
    sign (poleWeight p i) = (-1 : SignType) ^ (poleIndex p i - 1) := by
  have hmem := poleIndex_mem p i
  have hlt : p.N < poleIndex p i := by
    have h := (Finset.mem_Icc.mp hmem).1
    omega
  have hodd : Odd (2 * p.m - 1) := ⟨p.m - 1, by omega⟩
  have hpos : 0 < (poleIndex p i : ℚ) ^ (2 * p.k) :=
    pow_pos (by exact_mod_cast poleIndex_pos p i) _
  unfold poleWeight poleNode
  rw [sign_mul, sign_pos hpos, mul_one]
  change signHom (_ / _) = _
  rw [map_div₀, signHom_apply, sign_pow, D_eval_sign _ _ hlt,
    SignType.pow_odd _ hodd, tailD_derivative_eval_sign p _ hmem]
  change (-1 : SignType) ^ p.N * (-1 : SignType) ^ (poleIndex p i - (p.N + 1)) = _
  rw [← pow_add]
  congr 1
  omega

/-- In zero-based pole order the signs alternate, starting with `(-1)^N`. -/
theorem poleWeight_sign_index (p : Real.Parameters) (hm : 0 < p.m) (i : Fin p.h) :
    sign (poleWeight p i) = (-1 : SignType) ^ (p.N + i.val) := by
  rw [poleWeight_sign p hm i]
  congr 1
  simp [poleIndex]

/-- Positive diagonal coefficients are exactly the even-parity positions. -/
theorem poleWeight_pos_iff (p : Real.Parameters) (hm : 0 < p.m) (i : Fin p.h) :
    0 < poleWeight p i ↔ Even (p.N + i.val) := by
  rw [← sign_eq_one_iff, poleWeight_sign_index p hm i]
  exact neg_one_pow_eq_one_iff_even (by decide)

/-- Negative diagonal coefficients are exactly the odd-parity positions. -/
theorem poleWeight_neg_iff (p : Real.Parameters) (hm : 0 < p.m) (i : Fin p.h) :
    poleWeight p i < 0 ↔ Odd (p.N + i.val) := by
  rw [← sign_eq_neg_one_iff, poleWeight_sign_index p hm i]
  exact neg_one_pow_eq_neg_one_iff_odd (by decide)

/-- The leading sign for all dimensions, before the paper's weight-5 specialization. -/
theorem rationalDerivativeMatrix_det_sign (p : Real.Parameters) (hm : 0 < p.m) :
    sign (rationalDerivativeMatrix p).det =
      (-1 : SignType) ^ (p.h * p.N + p.h * (p.h - 1) / 2) := by
  rw [rationalDerivativeMatrix_det, sign_mul]
  have hs : sign ((poleVandermonde p).det ^ 2) = 1 :=
    sign_pos (sq_pos_of_ne_zero (poleVandermonde_det_ne_zero p))
  rw [hs, one_mul]
  change signHom (∏ i : Fin p.h, poleWeight p i) = _
  rw [map_prod]
  simp only [signHom_apply, poleWeight_sign_index p hm]
  rw [Finset.prod_pow_eq_pow_sum]
  congr 1
  rw [Fin.sum_univ_eq_sum_range]
  rw [Finset.sum_add_distrib, Finset.sum_range_id]
  simp [mul_comm]

/-- Exact leading coefficient sign of the actual rational Hankel determinant. -/
theorem delta_leadingCoeff_sign (p : Real.Parameters) (hm : 0 < p.m) :
    sign (Real.delta p).leadingCoeff =
      (-1 : SignType) ^ (p.h * p.N + p.h * (p.h - 1) / 2) := by
  rw [delta_leadingCoeff, rationalDerivativeMatrix_det_sign p hm]

theorem weight5_sign_exponent (n : ℕ) :
    (27 * n) * (3 * n) + (27 * n) * (27 * n - 1) / 2 =
      891 * (n * (n - 1) / 2) + 432 * n := by
  by_cases hn : n = 0
  · simp [hn]
  have hsub : n - 1 + 1 = n := by omega
  have hsub27 : 27 * n - 1 + 1 = 27 * n := by omega
  have hpair := Nat.div_two_mul_two_of_even (Nat.even_mul_pred_self n)
  have hpair27 := Nat.div_two_mul_two_of_even (Nat.even_mul_pred_self (27 * n))
  nlinarith

theorem weight5_sign_parity (n : ℕ) :
    (-1 : SignType) ^ ((27*n)*(3*n) + (27*n)*(27*n-1)/2) =
      (-1 : SignType) ^ (n*(n-1)/2) := by
  rw [weight5_sign_exponent, pow_add, pow_mul, pow_mul,
    (show Odd (891 : ℕ) by decide).neg_one_pow,
    (show Even (432 : ℕ) by decide).neg_one_pow, one_pow, mul_one]

/-- The paper's weight-five family: K=30n, N=3n, and 2m=6. -/
def weightFiveParameters (n : ℕ) : Real.Parameters := ⟨2, 3, 3 * n, 30 * n⟩

theorem weightFiveParameters_dimension (n : ℕ) :
    (weightFiveParameters n).h = 27 * n := by
  simp only [weightFiveParameters, Real.Parameters.h]
  omega

/-- Theorem 3.3(2): exact sign of the rational determinant's leading coefficient. -/
theorem weightFive_delta_leadingCoeff_sign (n : ℕ) :
    sign (Real.delta (weightFiveParameters n)).leadingCoeff =
      (-1 : SignType) ^ (n * (n - 1) / 2) := by
  rw [delta_leadingCoeff_sign _ (by norm_num [weightFiveParameters]),
    weightFiveParameters_dimension]
  exact weight5_sign_parity n

end ManuscriptChain.PoleDiagonalization

namespace ManuscriptChain.BasisInvariance

/-- Positive rational normalization preserves the integer leading sign. -/
theorem PrimitiveNormalization.leadingCoeff_sign {f : ℚ[X]}
    (n : PrimitiveNormalization f) :
    sign n.polynomial.leadingCoeff = sign f.leadingCoeff := by
  have hid := congrArg Polynomial.leadingCoeff n.identity
  rw [Polynomial.leadingCoeff_map_of_injective (Int.cast_injective :
    Function.Injective (Int.castRingHom ℚ)), Polynomial.leadingCoeff_mul,
    Polynomial.leadingCoeff_C] at hid
  have hsign := congrArg SignType.sign hid
  change sign (n.polynomial.leadingCoeff : ℚ) = sign (n.scale * f.leadingCoeff) at hsign
  simpa only [sign_intCast, sign_mul,
    sign_pos n.scale_pos, one_mul] using hsign

/-- Leading-sign formula for any primitive normalization of the actual pencil. -/
theorem primitive_delta_leadingCoeff_sign (p : Real.Parameters) (hm : 0 < p.m)
    (n : PrimitiveNormalization (Real.delta p)) :
    sign n.polynomial.leadingCoeff =
      (-1 : SignType) ^ (p.h * p.N + p.h * (p.h - 1) / 2) := by
  rw [n.leadingCoeff_sign, PoleDiagonalization.delta_leadingCoeff_sign p hm]

/-- Theorem 3.3(2) for the constructed primitive integer polynomial. -/
theorem weightFive_primitive_leadingCoeff_sign (n : ℕ) :
    sign (primitiveNormalization
      (Real.delta (PoleDiagonalization.weightFiveParameters n))
      (PoleDiagonalization.delta_ne_zero _)).polynomial.leadingCoeff =
      (-1 : SignType) ^ (n * (n - 1) / 2) := by
  rw [PrimitiveNormalization.leadingCoeff_sign,
    PoleDiagonalization.weightFive_delta_leadingCoeff_sign]

end ManuscriptChain.BasisInvariance
