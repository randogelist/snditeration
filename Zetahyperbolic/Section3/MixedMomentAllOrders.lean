import Zetahyperbolic.Section3.ShiftedMomentPositivity
import Mathlib.Algebra.Polynomial.RuleOfSigns
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Data.Fin.Tuple.Sort

/-!
# Sparse monomials form a Chebyshev system on the positive half-line

This proves all-order nonsingularity of generalized Vandermonde matrices for
arbitrary distinct natural exponents and distinct positive nodes, using
Descartes' rule of signs. It is a prerequisite for arbitrary mixed-minor
positivity, not a replacement for the missing determinant-sign and integral
identity arguments. No positivity of a mixed moment determinant is assumed.
-/

noncomputable section
open scoped BigOperators
open Polynomial Matrix

namespace ManuscriptChain.MixedMomentAllOrders

/-- The number of coefficient sign variations is strictly smaller than the
number of nonzero monomials, without a bound on the degree. -/
theorem signVariations_lt_support_card (P : ℝ[X]) (hP : P ≠ 0) :
    P.signVariations < P.support.card := by
  classical
  generalize hn : P.support.card = n
  induction n using Nat.strong_induction_on generalizing P with
  | h n ih =>
    by_cases he : P.eraseLead = 0
    · have hc := Polynomial.card_support_eq_one_of_eraseLead_eq_zero hP he
      have hs : SignType.sign P.leadingCoeff ≠ 0 := by
        exact _root_.sign_ne_zero.mpr (Polynomial.leadingCoeff_ne_zero.mpr hP)
      rw [Polynomial.signVariations_eq_eraseLead_add_ite hP]
      have hn1 : n = 1 := by omega
      simpa [he, hs, hn1]
    · have hlt := Polynomial.eraseLead_support_card_lt hP
      have hc := Polynomial.card_support_eraseLead_add_one hP
      have hv := ih P.eraseLead.support.card (by omega) P.eraseLead he rfl
      have hb := Polynomial.signVariations_le_eraseLead_succ P
      omega

/-- Descartes' bound in sparse-support form, counting positive roots with
multiplicity. In particular it is independent of the largest exponent. -/
theorem positive_roots_lt_support_card (P : ℝ[X]) (hP : P ≠ 0) :
    P.roots.countP (0 < ·) < P.support.card :=
  (Polynomial.roots_countP_pos_le_signVariations P).trans_lt
    (signVariations_lt_support_card P hP)

/-- A polynomial supported on at most n monomials cannot vanish at n distinct
positive nodes unless it is the zero polynomial. -/
theorem eq_zero_of_sparse_positive_roots {n : ℕ} (P : ℝ[X])
    (hs : P.support.card ≤ n) (x : Fin n → ℝ)
    (hx : Function.Injective x) (hpos : ∀ i, 0 < x i)
    (hroot : ∀ i, P.eval (x i) = 0) : P = 0 := by
  classical
  by_contra hP
  let S : Finset ℝ := Finset.univ.image x
  have hcard : S.card = n := by
    simp only [S, Finset.card_image_of_injective _ hx, Finset.card_univ, Fintype.card_fin]
  have hsub : S ⊆ (P.roots.filter (0 < ·)).toFinset := by
    intro y hy
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hy
    simp only [Multiset.mem_toFinset, Multiset.mem_filter]
    exact ⟨(Polynomial.mem_roots hP).2 (hroot i), hpos i⟩
  have hle := (Finset.card_le_card hsub).trans (Multiset.toFinset_card_le _)
  rw [hcard, ← Multiset.countP_eq_card_filter] at hle
  have hlt := positive_roots_lt_support_card P hP
  omega

/-- The exact sparse polynomial represented by a coefficient vector. -/
def sparsePolynomial {n : ℕ} (e : Fin n → ℕ) (c : Fin n → ℝ) : ℝ[X] :=
  ∑ i, Polynomial.monomial (e i) (c i)

theorem sparsePolynomial_eval {n : ℕ} (e : Fin n → ℕ) (c : Fin n → ℝ) (x : ℝ) :
    (sparsePolynomial e c).eval x = ∑ i, c i * x ^ e i := by
  simp only [sparsePolynomial, Polynomial.eval_finsetSum, Polynomial.eval_monomial]

theorem sparsePolynomial_coeff {n : ℕ} (e : Fin n → ℕ)
    (he : Function.Injective e) (c : Fin n → ℝ) (i : Fin n) :
    (sparsePolynomial e c).coeff (e i) = c i := by
  classical
  simp only [sparsePolynomial, Polynomial.finset_sum_coeff, Polynomial.coeff_monomial]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp only [if_neg (fun h => hji (he h))]
  · simp

theorem sparsePolynomial_support_card_le {n : ℕ} (e : Fin n → ℕ) (c : Fin n → ℝ) :
    (sparsePolynomial e c).support.card ≤ n := by
  classical
  have hs : (sparsePolynomial e c).support ⊆ Finset.univ.image e := by
    intro d hd
    by_contra hmem
    have hall : ∀ i : Fin n, e i ≠ d := by
      intro i hi
      exact hmem (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hi⟩)
    have hz : (sparsePolynomial e c).coeff d = 0 := by
      simp only [sparsePolynomial, Polynomial.finset_sum_coeff, Polynomial.coeff_monomial]
      simp only [hall, if_false, Finset.sum_const_zero]
    exact (Polynomial.mem_support_iff.mp hd) hz
  exact (Finset.card_le_card hs).trans (by
    simpa only [Finset.card_univ, Fintype.card_fin] using
      Finset.card_image_le (s := (Finset.univ : Finset (Fin n))) (f := e))

/-- Unisolvence of arbitrary sparse monomials on distinct positive nodes. -/
theorem sparse_coefficients_eq_zero {n : ℕ} (e : Fin n → ℕ)
    (he : Function.Injective e) (x : Fin n → ℝ)
    (hx : Function.Injective x) (hpos : ∀ i, 0 < x i) (c : Fin n → ℝ)
    (hc : ∀ i, ∑ j, c j * x i ^ e j = 0) : c = 0 := by
  have hz : sparsePolynomial e c = 0 :=
    eq_zero_of_sparse_positive_roots _ (sparsePolynomial_support_card_le e c)
      x hx hpos (by simpa only [sparsePolynomial_eval] using hc)
  funext i
  have hi := congrArg (fun P : ℝ[X] => P.coeff (e i)) hz
  simpa only [sparsePolynomial_coeff e he, Polynomial.coeff_zero, Pi.zero_apply] using hi

/-- Generalized Vandermonde nonsingularity in every order. The ordering of the
nodes and exponents is unrestricted; their orientation controls the sign, which
is deliberately not claimed by this theorem. -/
theorem generalized_vandermonde_det_ne_zero {n : ℕ} (e : Fin n → ℕ)
    (he : Function.Injective e) (x : Fin n → ℝ)
    (hx : Function.Injective x) (hpos : ∀ i, 0 < x i) :
    Matrix.det (fun i j : Fin n => x i ^ e j) ≠ 0 := by
  let A : Matrix (Fin n) (Fin n) ℝ := fun i j => x i ^ e j
  have hi : Function.Injective A.mulVec := by
    intro c d hcd
    have hz : c - d = 0 := by
      apply sparse_coefficients_eq_zero e he x hx hpos
      intro i
      have h := congrFun hcd i
      change (∑ j, x i ^ e j * c j) = ∑ j, x i ^ e j * d j at h
      simp only [Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
      apply sub_eq_zero.mpr
      simpa only [mul_comm] using h
    exact sub_eq_zero.mp hz
  exact ((Matrix.isUnit_iff_isUnit_det A).mp
    (Matrix.mulVec_injective_iff_isUnit.mp hi)).ne_zero

/-- The geometric node vector makes the generalized determinant the transpose
of an ordinary Vandermonde determinant in the exponentiated exponents. -/
theorem geometric_vandermonde_det_pos {n : ℕ} (e : Fin n → ℕ)
    (he : StrictMono e) :
    0 < Matrix.det (fun i j : Fin n => ((2 : ℝ) ^ i.val) ^ e j) := by
  have hm : (fun i j : Fin n => ((2 : ℝ) ^ i.val) ^ e j) =
      (Matrix.vandermonde (fun j : Fin n => (2 : ℝ) ^ e j)).transpose := by
    ext i j
    simp only [Matrix.transpose_apply, Matrix.vandermonde_apply]
    rw [← pow_mul, ← pow_mul, Nat.mul_comm]
  rw [hm, Matrix.det_transpose, Matrix.det_vandermonde]
  apply Finset.prod_pos
  intro i _
  apply Finset.prod_pos
  intro j hj
  apply sub_pos.mpr
  exact pow_lt_pow_right₀ (by norm_num : (1 : ℝ) < 2) (he (Finset.mem_Ioi.mp hj))

/-- A convex interpolation of two strictly increasing positive node vectors
is again strictly increasing and positive, including both endpoints. -/
theorem interpolated_nodes {n : ℕ} (x y : Fin n → ℝ)
    (hx : StrictMono x) (hy : StrictMono y)
    (hxp : ∀ i, 0 < x i) (hyp : ∀ i, 0 < y i)
    {t : ℝ} (ht : t ∈ Set.Icc 0 1) :
    StrictMono (fun i => (1-t) * x i + t * y i) ∧
      ∀ i, 0 < (1-t) * x i + t * y i := by
  constructor
  · intro i j hij
    have h₁ := hx hij
    have h₂ := hy hij
    have ha : 0 ≤ (1-t) * (x j-x i) := mul_nonneg (by linarith [ht.2]) (sub_nonneg.mpr h₁.le)
    have hb : 0 ≤ t * (y j-y i) := mul_nonneg ht.1 (sub_nonneg.mpr h₂.le)
    by_cases ht0 : t = 0
    · simpa [ht0] using h₁
    · have hh := mul_pos (lt_of_le_of_ne ht.1 (Ne.symm ht0)) (sub_pos.mpr h₂)
      nlinarith
  · intro i
    have ha := mul_nonneg (show 0 ≤ 1-t by linarith [ht.2]) (hxp i).le
    by_cases ht0 : t = 0
    · simpa [ht0] using hxp i
    · have hh := mul_pos (lt_of_le_of_ne ht.1 (Ne.symm ht0)) (hyp i)
      linarith

/-- Strict positivity of the generalized Vandermonde determinant in every
order, for arbitrary increasing natural exponents and positive increasing
nodes. The sign is transported from geometric nodes along a convex segment;
nonsingularity prevents a zero crossing. -/
theorem generalized_vandermonde_det_pos {n : ℕ} (e : Fin n → ℕ)
    (he : StrictMono e) (x : Fin n → ℝ)
    (hx : StrictMono x) (hpos : ∀ i, 0 < x i) :
    0 < Matrix.det (fun i j : Fin n => x i ^ e j) := by
  let y : Fin n → ℝ := fun i => (2 : ℝ) ^ i.val
  have hy : StrictMono y := by
    intro i j hij
    exact pow_lt_pow_right₀ (by norm_num : (1 : ℝ) < 2) hij
  have hyp (i : Fin n) : 0 < y i := pow_pos (by norm_num) _
  let F : ℝ → ℝ := fun t =>
    Matrix.det (fun i j : Fin n => ((1-t) * y i + t * x i) ^ e j)
  have hF : Continuous F := by
    apply Continuous.matrix_det
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    fun_prop
  have h0 : 0 < F 0 := by
    simpa only [F, sub_zero, one_mul, zero_mul, add_zero, y] using
      geometric_vandermonde_det_pos e he
  have h1 : F 1 = Matrix.det (fun i j : Fin n => x i ^ e j) := by
    simp only [F, sub_self, zero_mul, one_mul, zero_add]
  have hnz (t : ℝ) (ht : t ∈ Set.Icc 0 1) : F t ≠ 0 := by
    obtain ⟨hm, hp⟩ := interpolated_nodes y x hy hx hyp hpos ht
    exact generalized_vandermonde_det_ne_zero e he.injective _ hm.injective hp
  by_contra hnot
  have hnonpos : F 1 ≤ 0 := by rw [h1]; exact le_of_not_gt hnot
  obtain ⟨t, ht, hz⟩ := intermediate_value_Icc' (by norm_num : (0 : ℝ) ≤ 1)
    hF.continuousOn (show (0 : ℝ) ∈ Set.Icc (F 1) (F 0) from ⟨hnonpos, h0.le⟩)
  exact hnz t ht hz

/-- The two determinants in Andréief's integrand have the same orientation.
Sorting the nodes multiplies both determinants by the same permutation sign,
which cancels in their product. -/
theorem generalized_vandermonde_product_pos {n : ℕ} (e f : Fin n → ℕ)
    (he : StrictMono e) (hf : StrictMono f) (x : Fin n → ℝ)
    (hx : Function.Injective x) (hpos : ∀ i, 0 < x i) :
    0 < Matrix.det (fun i j : Fin n => x i ^ e j) *
      Matrix.det (fun i j : Fin n => x i ^ f j) := by
  classical
  let σ := Tuple.sort x
  have hs : StrictMono (x ∘ σ) :=
    (Tuple.monotone_sort x).strictMono_of_injective (hx.comp σ.injective)
  have hsp (i : Fin n) : 0 < (x ∘ σ) i := hpos (σ i)
  have hp := mul_pos (generalized_vandermonde_det_pos e he (x ∘ σ) hs hsp)
    (generalized_vandermonde_det_pos f hf (x ∘ σ) hs hsp)
  have hde : Matrix.det (fun i j : Fin n => (x ∘ σ) i ^ e j) =
      (Equiv.Perm.sign σ : ℝ) * Matrix.det (fun i j : Fin n => x i ^ e j) := by
    have hm : Matrix.submatrix (fun i j : Fin n => x i ^ e j) σ id =
        (fun i j : Fin n => (x ∘ σ) i ^ e j) := by
      ext i j
      rfl
    rw [← hm]
    exact Matrix.det_permute σ (fun i j : Fin n => x i ^ e j)
  have hdf : Matrix.det (fun i j : Fin n => (x ∘ σ) i ^ f j) =
      (Equiv.Perm.sign σ : ℝ) * Matrix.det (fun i j : Fin n => x i ^ f j) := by
    have hm : Matrix.submatrix (fun i j : Fin n => x i ^ f j) σ id =
        (fun i j : Fin n => (x ∘ σ) i ^ f j) := by
      ext i j
      rfl
    rw [← hm]
    exact Matrix.det_permute σ (fun i j : Fin n => x i ^ f j)
  rw [hde, hdf] at hp
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hsign | hsign
  · simpa [hsign] using hp
  · simpa [hsign] using hp

/-- Nonnegative Andréief integrand for all positive nodes, including collisions.
At a collision a repeated matrix row makes the product zero. -/
theorem generalized_vandermonde_product_nonneg {n : ℕ} (e f : Fin n → ℕ)
    (he : StrictMono e) (hf : StrictMono f) (x : Fin n → ℝ)
    (hpos : ∀ i, 0 < x i) :
    0 ≤ Matrix.det (fun i j : Fin n => x i ^ e j) *
      Matrix.det (fun i j : Fin n => x i ^ f j) := by
  classical
  by_cases hx : Function.Injective x
  · exact (generalized_vandermonde_product_pos e f he hf x hx hpos).le
  · obtain ⟨i, j, hij, hne⟩ := Function.not_injective_iff.mp hx
    have hz : Matrix.det (fun i j : Fin n => x i ^ e j) = 0 := by
      apply Matrix.det_zero_of_row_eq hne
      funext k
      rw [hij]
    rw [hz, zero_mul]

end ManuscriptChain.MixedMomentAllOrders
