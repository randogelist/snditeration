import Zetahyperbolic.Section6.OuterPrimePencilIdentification
import Zetahyperbolic.Section6.OuterPrimePadicReduction
import Zetahyperbolic.Section6.PadicDeterminantDominance

/-! The exact paired-monomial matrix in manuscript 6.3(1).  Its entries
are the four actual Beukers monomial entries belonging to x^r+x^(r+p).
The proof below uses every residue class, not just one two-by-two block. -/

noncomputable section
open scoped BigOperators Matrix
open MeasureTheory
namespace ManuscriptChain.Beukers

private lemma rational_norm_le_prime_pow (p s : ℕ) [Fact p.Prime]
    (q : ℚ) (hq : -(s : ℤ) ≤ padicValRat p q) :
    ‖(q : ℚ_[p])‖ ≤ (p : ℝ)^s := by
  by_cases hn : q = 0
  · simp [hn]
  rw [Padic.eq_padicNorm, padicNorm.eq_zpow_of_nonzero hn]
  have hp : (1 : ℚ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).one_le
  exact_mod_cast (zpow_le_zpow_right₀ hp (show -padicValRat p q ≤ (s : ℤ) by omega))

private lemma rational_norm_le_one (p : ℕ) [Fact p.Prime]
    (q : ℚ) (hq : 0 ≤ padicValRat p q) : ‖(q : ℚ_[p])‖ ≤ 1 := by
  simpa using rational_norm_le_prime_pow p 0 q (by simpa using hq)

private lemma natural_small_unit (p n : ℕ) [Fact p.Prime]
    (hn : 0 < n) (hnp : n < p) : ‖(n : ℚ_[p])‖ = 1 := by
  rw [Padic.norm_natCast_eq_one_iff]
  exact (Fact.out : p.Prime).coprime_iff_not_dvd.mpr
    (Nat.not_dvd_of_pos_of_lt hn hnp)

private lemma six_unit (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) :
    ‖(6 : ℚ_[p])‖ = 1 := by
  change ‖((6 : ℕ) : ℚ_[p])‖ = 1
  rw [Padic.norm_natCast_eq_one_iff]
  apply (Fact.out : p.Prime).coprime_iff_not_dvd.mpr
  intro hd
  have hp : p.Prime := Fact.out
  rw [show (6 : ℕ) = 2*3 by norm_num, hp.dvd_mul] at hd
  rcases hd with hd | hd
  · have := Nat.le_of_dvd (by norm_num : 0 < 2) hd
    omega
  · have := Nat.le_of_dvd (by norm_num : 0 < 3) hd
    omega

private lemma small_power_mul' (p : ℕ) [Fact p.Prime]
    (n : ℕ) (hn : n ≠ 0) (a : ℚ_[p]) (ha : ‖a‖ ≤ 1) :
    ‖(p : ℚ_[p])^n * a‖ < 1 := by
  rw [norm_mul, norm_pow]
  calc
    _ ≤ ‖(p : ℚ_[p])‖^n * 1 := mul_le_mul_of_nonneg_left ha (by positivity)
    _ < 1 := by
      rw [mul_one]
      exact pow_lt_one₀ (norm_nonneg _) (Padic.norm_p_lt_one (p := p)) hn

private lemma small_add (p : ℕ) [Fact p.Prime] (a b : ℚ_[p])
    (ha : ‖a‖ < 1) (hb : ‖b‖ < 1) : ‖a+b‖ < 1 :=
  (Padic.nonarchimedean a b).trans_lt (max_lt ha hb)

/-- The leading local congruence holds already for every prime at least five. -/
theorem padicLocalMatrix_scaled_reduction_five (p r : ℕ) [Fact p.Prime]
    (hp5 : 5 ≤ p) (hr : r < p) (X : ℚ_[p]) (hX : ‖X‖ ≤ 1) :
    ∀ i j, ‖(p : ℚ_[p])^7 * padicLocalMatrix p r X i j -
      padicLeadingMatrix p i j‖ < 1 := by
  let E (s : ℕ) : ℚ := Real.harmonic s (r+p) - Real.harmonic s r - 1/(p : ℚ)^s
  have hE (s : ℕ) : ‖(E s : ℚ_[p])‖ ≤ 1 :=
    rational_norm_le_one p (E s) (harmonic_outer_regular_valuation_nonneg p r s hr)
  have hp : p.Prime := Fact.out
  have hpn : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hsix : (6 : ℚ_[p]) ≠ 0 := by norm_num
  have hlow := padicLocalMatrix_low_norm p r hr X hX
  have hhigherror : ‖(X - (Real.harmonic 7 r : ℚ_[p])) - (E 7 : ℚ_[p])‖ ≤ 1 := by
    simpa only [sub_eq_add_neg] using
      (Padic.nonarchimedean (X - (Real.harmonic 7 r : ℚ_[p])) (-(E 7 : ℚ_[p]))).trans
        (max_le hlow (by simpa only [norm_neg] using hE 7))
  have hdiag : ‖(p : ℚ_[p])^7 * (X - (Real.harmonic 7 (r+p) : ℚ_[p])) + 1‖ < 1 := by
    have he : (p : ℚ_[p])^7 * (X - (Real.harmonic 7 (r+p) : ℚ_[p])) + 1 =
        (p : ℚ_[p])^7 * ((X - (Real.harmonic 7 r : ℚ_[p])) - (E 7 : ℚ_[p])) := by
      dsimp [E]
      push_cast
      field_simp [hpn]
      <;> ring
    rw [he]
    exact small_power_mul' p 7 (by norm_num) _ hhigherror
  have hoff : ‖(p : ℚ_[p])^7 * (Real.dualConstant 7 r (r+p) : ℚ_[p]) -
      (6 : ℚ_[p])⁻¹‖ < 1 := by
    have hne : r ≠ r+p := by omega
    have he : (p : ℚ_[p])^7 * (Real.dualConstant 7 r (r+p) : ℚ_[p]) -
        (6 : ℚ_[p])⁻¹ = (p : ℚ_[p])^6 * ((E 6 : ℚ_[p]) / 6) := by
      simp only [Real.dualConstant, if_neg hne]
      norm_num only [Nat.reduceSub, Nat.cast_ofNat]
      dsimp [E]
      push_cast
      field_simp [hpn, hsix]
      <;> ring
    rw [he]
    apply small_power_mul' p 6 (by norm_num)
    simpa only [norm_div, six_unit p hp5, div_one] using hE 6
  intro i j
  fin_cases i <;> fin_cases j
  · simpa [padicLocalMatrix, padicLeadingMatrix] using
      small_power_mul' p 7 (by norm_num) _ hlow
  · simpa [padicLocalMatrix, padicLeadingMatrix] using hoff
  · simpa [padicLocalMatrix, padicLeadingMatrix] using hoff
  · simpa [padicLocalMatrix, padicLeadingMatrix] using hdiag

/-- Four actual monomial entries for the printed basis x^r+x^(r+p). -/
def pairedMonomialMatrix (p : ℕ) (X : ℚ) : Matrix (Fin p) (Fin p) ℚ :=
  fun r s => ∑ i : Fin 2, ∑ j : Fin 2,
    (Real.dualConstant 7 (r.val+i.val*p) (s.val+j.val*p) +
      if r.val+i.val*p = s.val+j.val*p then X else 0)

def pairedMonomialPadicMatrix (p : ℕ) [Fact p.Prime] (X : ℚ_[p]) :
    Matrix (Fin p) (Fin p) ℚ_[p] :=
  fun r s => ∑ i : Fin 2, ∑ j : Fin 2,
    ((Real.dualConstant 7 (r.val+i.val*p) (s.val+j.val*p) : ℚ_[p]) +
      if r.val+i.val*p = s.val+j.val*p then X else 0)

theorem pairedMonomialMatrix_cast (p : ℕ) [Fact p.Prime] (X : ℚ) :
    (pairedMonomialMatrix p X).map (Rat.castHom ℚ_[p]) =
      pairedMonomialPadicMatrix p (X : ℚ_[p]) := by
  ext r s
  simp [pairedMonomialMatrix, pairedMonomialPadicMatrix, Matrix.map_apply]

theorem pairedMonomialPadicMatrix_diagonal (p : ℕ) [Fact p.Prime]
    (X : ℚ_[p]) (r : Fin p) :
    pairedMonomialPadicMatrix p X r r =
      ∑ i : Fin 2, ∑ j : Fin 2, padicLocalMatrix p r.val X i j := by
  rw [padicLocalMatrix_eq_monomial_pencil]
  have hp : 0 < p := (Fact.out : p.Prime).pos
  simp only [pairedMonomialPadicMatrix, Fin.sum_univ_two]
  simp only [Fin.val_zero, Fin.val_one, zero_mul, one_mul, add_zero]
  have hn : r.val ≠ r.val+p := by omega
  simp [hn, Ne.symm hn]

/-- Each paired diagonal has residue -2/3 after multiplication by p^7. -/
theorem pairedMonomial_scaled_diagonal_reduction (p : ℕ) [Fact p.Prime]
    (hp5 : 5 ≤ p) (X : ℚ_[p]) (hX : ‖X‖ ≤ 1) (r : Fin p) :
    ‖(p : ℚ_[p])^7 * pairedMonomialPadicMatrix p X r r - (-2/3)‖ < 1 := by
  have h := padicLocalMatrix_scaled_reduction_five p r.val hp5 r.isLt X hX
  have hs := small_add p _ _ (small_add p _ _ (h 0 0) (h 0 1))
    (small_add p _ _ (h 1 0) (h 1 1))
  rw [pairedMonomialPadicMatrix_diagonal]
  have he : (p : ℚ_[p])^7 * (∑ i : Fin 2, ∑ j : Fin 2, padicLocalMatrix p r.val X i j) - (-2/3) =
      ((p : ℚ_[p])^7 * padicLocalMatrix p r.val X 0 0 - padicLeadingMatrix p 0 0 +
       ((p : ℚ_[p])^7 * padicLocalMatrix p r.val X 0 1 - padicLeadingMatrix p 0 1)) +
      ((p : ℚ_[p])^7 * padicLocalMatrix p r.val X 1 0 - padicLeadingMatrix p 1 0 +
       ((p : ℚ_[p])^7 * padicLocalMatrix p r.val X 1 1 - padicLeadingMatrix p 1 1)) := by
    simp only [Fin.sum_univ_two, padicLeadingMatrix]
    norm_num
    ring
  rw [he]
  exact hs

private lemma residue_difference_unit (p : ℕ) [Fact p.Prime]
    (r s : Fin p) (hrs : r ≠ s) (i j : Fin 2) :
    ‖((r.val+i.val*p : ℕ) : ℚ_[p]) - ((s.val+j.val*p : ℕ) : ℚ_[p])‖ = 1 := by
  have hnd : ¬ (p : ℤ) ∣ ((r.val+i.val*p : ℕ) : ℤ) - ((s.val+j.val*p : ℕ) : ℤ) := by
    intro hd
    have he := (Int.modEq_iff_dvd.mpr hd).eq
    simp only [Nat.cast_add, Nat.cast_mul, Int.add_emod, Int.mul_emod,
      Int.emod_self, mul_zero, Int.zero_emod, add_zero, Int.emod_emod] at he
    rw [Int.emod_eq_of_lt (by positivity) (by exact_mod_cast s.isLt),
      Int.emod_eq_of_lt (by positivity) (by exact_mod_cast r.isLt)] at he
    apply hrs
    apply Fin.ext
    exact_mod_cast he.symm
  have hh := (padicNorm.int_eq_one_iff (p := p) _).mpr hnd
  have he : ((r.val+i.val*p : ℕ) : ℚ_[p]) - ((s.val+j.val*p : ℕ) : ℚ_[p]) =
      ((((r.val+i.val*p : ℕ) : ℤ) - ((s.val+j.val*p : ℕ) : ℤ) : ℤ) : ℚ) := by
    push_cast
    rfl
  rw [he, Padic.eq_padicNorm]
  exact_mod_cast hh

private lemma cross_entry_small (p : ℕ) [Fact p.Prime]
    (hp5 : 5 ≤ p) (r s : Fin p) (hrs : r ≠ s) (i j : Fin 2) :
    ‖(p : ℚ_[p])^7 *
      (Real.dualConstant 7 (r.val+i.val*p) (s.val+j.val*p) : ℚ_[p])‖ < 1 := by
  let a := r.val+i.val*p
  let b := s.val+j.val*p
  have hab : a ≠ b := by
    intro he
    have hm := congrArg (fun n : ℕ => n % p) he
    have hre : r.val % p = r.val := Nat.mod_eq_of_lt r.isLt
    have hse : s.val % p = s.val := Nat.mod_eq_of_lt s.isLt
    simp [a, b, Nat.add_mod, hre, hse] at hm
    exact hrs (Fin.ext hm)
  have ha : a < 2*p := by
    have hr := r.isLt
    fin_cases i <;> dsimp [a] <;> omega
  have hb : b < 2*p := by
    have hs := s.isLt
    fin_cases j <;> dsimp [b] <;> omega
  have hA := rational_norm_le_prime_pow p 6 (Real.harmonic 6 a)
    (harmonic_outer_valuation_lower p 6 a ha)
  have hB := rational_norm_le_prime_pow p 6 (Real.harmonic 6 b)
    (harmonic_outer_valuation_lower p 6 b hb)
  have hsub : ‖(Real.harmonic 6 a : ℚ_[p]) - (Real.harmonic 6 b : ℚ_[p])‖ ≤ (p : ℝ)^6 := by
    simpa only [sub_eq_add_neg, norm_neg] using
      (Padic.nonarchimedean (Real.harmonic 6 a : ℚ_[p]) (-(Real.harmonic 6 b : ℚ_[p]))).trans
        (max_le hA (by simpa using hB))
  have hunit : ‖(a : ℚ_[p]) - (b : ℚ_[p])‖ = 1 :=
    residue_difference_unit p r s hrs i j
  have hentry : ‖(Real.dualConstant 7 a b : ℚ_[p])‖ ≤ (p : ℝ)^6 := by
    simp only [Real.dualConstant, if_neg hab]
    norm_num only [Nat.reduceSub, Nat.cast_ofNat]
    push_cast
    rw [norm_div, norm_mul, six_unit p hp5, hunit, one_mul, div_one]
    exact hsub
  rw [norm_mul, norm_pow]
  calc
    _ ≤ ‖(p : ℚ_[p])‖^7 * (p : ℝ)^6 := mul_le_mul_of_nonneg_left hentry (by positivity)
    _ = (p : ℝ)⁻¹ := by
      rw [Padic.norm_p]
      have hn : (p : ℝ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
      field_simp [hn]
      <;> ring
    _ < 1 := inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt)

/-- Different residue classes vanish after scaling and reduction. -/
theorem pairedMonomial_scaled_offdiagonal (p : ℕ) [Fact p.Prime]
    (hp5 : 5 ≤ p) (X : ℚ_[p]) (r s : Fin p) (hrs : r ≠ s) :
    ‖(p : ℚ_[p])^7 * pairedMonomialPadicMatrix p X r s‖ < 1 := by
  have hne (i j : Fin 2) : r.val+i.val*p ≠ s.val+j.val*p := by
    intro he
    have hm := congrArg (fun n : ℕ => n % p) he
    simp [Nat.add_mod, Nat.mod_eq_of_lt r.isLt, Nat.mod_eq_of_lt s.isLt] at hm
    exact hrs (Fin.ext hm)
  simp only [pairedMonomialPadicMatrix, if_neg (hne _ _), add_zero, Finset.mul_sum]
  simp only [Fin.sum_univ_two]
  exact small_add p _ _
    (small_add p _ _ (cross_entry_small p hp5 r s hrs 0 0) (cross_entry_small p hp5 r s hrs 0 1))
    (small_add p _ _ (cross_entry_small p hp5 r s hrs 1 0) (cross_entry_small p hp5 r s hrs 1 1))

/-- The full q-dimensional scaled determinant is a unit, at every integral
q-adic evaluation, including zero. -/
theorem pairedMonomial_scaled_determinant_norm (p : ℕ) [Fact p.Prime]
    (hp5 : 5 ≤ p) (X : ℚ_[p]) (hX : ‖X‖ ≤ 1) :
    ‖(((p : ℚ_[p])^7) • pairedMonomialPadicMatrix p X).det‖ = 1 := by
  apply padic_det_norm_eq_one_of_diagonal_dominant
  · intro r
    have hu : ‖(-2/3 : ℚ_[p])‖ = 1 := by
      rw [norm_div, norm_neg]
      have htwo := natural_small_unit p 2 (by norm_num) (by omega)
      have hthree := natural_small_unit p 3 (by norm_num) (by omega)
      norm_num only [Nat.cast_ofNat] at htwo hthree
      rw [htwo, hthree, div_self one_ne_zero]
    have h := pairedMonomial_scaled_diagonal_reduction p hp5 X hX r
    change ‖(p : ℚ_[p])^7 * pairedMonomialPadicMatrix p X r r‖ = 1
    rw [← hu]
    exact Padic.norm_eq_of_norm_sub_lt_right (by simpa only [hu] using h)
  · intro r s hrs
    exact pairedMonomial_scaled_offdiagonal p hp5 X r s hrs


/-- Exact determinant norm for the full printed paired basis. -/
theorem pairedMonomial_determinant_norm (p : ℕ) [Fact p.Prime]
    (hp5 : 5 ≤ p) (X : ℚ_[p]) (hX : ‖X‖ ≤ 1) :
    ‖(pairedMonomialPadicMatrix p X).det‖ = (p : ℝ)^(7*p) := by
  have h := pairedMonomial_scaled_determinant_norm p hp5 X hX
  rw [Matrix.det_smul, norm_mul, norm_pow, norm_pow, Padic.norm_p,
    Fintype.card_fin] at h
  have he : ((p : ℝ)^(7*p))⁻¹ * ‖(pairedMonomialPadicMatrix p X).det‖ = 1 := by
    simpa only [inv_pow, ← pow_mul] using h
  have hn : (p : ℝ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  exact ((inv_mul_eq_one₀ (pow_ne_zero _ hn)).mp he).symm

/-- The pencil derivative is exactly twice the identity for this basis. -/
theorem pairedMonomialMatrix_affine (p : ℕ) (X : ℚ) :
    pairedMonomialMatrix p X = pairedMonomialMatrix p 0 + (2*X) • (1 : Matrix (Fin p) (Fin p) ℚ) := by
  ext r s
  have hcross₁ : r.val ≠ s.val+p := by have := r.isLt; omega
  have hcross₂ : r.val+p ≠ s.val := by have := s.isLt; omega
  simp only [pairedMonomialMatrix, Fin.sum_univ_two, Fin.val_zero, Fin.val_one,
    zero_mul, one_mul, add_zero, ite_self, Matrix.add_apply, Matrix.smul_apply,
    smul_eq_mul, Matrix.one_apply]
  by_cases hrs : r = s
  · subst s
    simp [hcross₁, hcross₂]
    ring
  · have hvs : r.val ≠ s.val := fun he => hrs (Fin.ext he)
    have hvs' : r.val+p ≠ s.val+p := by omega
    simp [hrs, hvs, hvs', hcross₁, hcross₂]

/-- The original 6.3(1) valuation, for every p-integral rational evaluation. -/
theorem theorem_6_3_part_one (p : ℕ) [Fact p.Prime]
    (hp5 : 5 ≤ p) (X : ℚ) (hX : 0 ≤ padicValRat p X) :
    padicValRat p (pairedMonomialMatrix p X).det = -7*(p : ℤ) ∧
      (pairedMonomialMatrix p X).det ≠ 0 := by
  have hnorm : ‖((pairedMonomialMatrix p X).det : ℚ_[p])‖ = (p : ℝ)^(7*p) := by
    have he := (Rat.castHom ℚ_[p]).map_det (pairedMonomialMatrix p X)
    change ((pairedMonomialMatrix p X).det : ℚ_[p]) =
      ((pairedMonomialMatrix p X).map (Rat.castHom ℚ_[p])).det at he
    rw [he, pairedMonomialMatrix_cast]
    exact pairedMonomial_determinant_norm p hp5 (X : ℚ_[p])
      (rational_norm_le_one p X hX)
  have hv := rational_valuation_of_prime_power_norm p (7*p)
    (pairedMonomialMatrix p X).det hnorm
  have hv' : padicValRat p (pairedMonomialMatrix p X).det = -7*(p : ℤ) := by
    simpa using hv
  refine ⟨hv', ?_⟩
  intro hz
  rw [hz, padicValRat.zero] at hv'
  have hp : 0 < p := (Fact.out : p.Prime).pos
  omega

/-- In particular the rational determinant at zero is nonzero, with exactly
seven p-poles per basis element. -/
theorem theorem_6_3_at_zero (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) :
    padicValRat p (pairedMonomialMatrix p 0).det = -7*(p : ℤ) ∧
      (pairedMonomialMatrix p 0).det ≠ 0 :=
  theorem_6_3_part_one p hp5 0 (by simp)

/-- The actual polynomial corresponding to the r-th row. -/
def pairedMonomialValue (p r : ℕ) (x : ℝ) : ℝ := x^r + x^(r+p)

/-- Direct identification with the actual Beukers integral. This verifies
the matrix is the manuscript polynomial pencil, not a formal surrogate. -/
theorem pairedMonomial_actual_integral (p : ℕ) [Fact p.Prime] (r s : Fin p) :
    (∫ z, pairedMonomialValue p r.val z.1 * pairedMonomialValue p s.val z.2
      ∂beukersMeasure) =
    ((pairedMonomialMatrix p 0 r s : ℚ) : ℝ) +
      if r = s then 2 * Real.zeta 7 else 0 := by
  have hm (a b : ℕ) : (∫ z, z.1^a * z.2^b ∂beukersMeasure) =
      (Real.dualConstant 7 a b : ℝ) + if a=b then Real.zeta 7 else 0 := by
    rw [integral_beukersMeasure, moment_eq_dualConstant]
  have hi (a b : ℕ) := monomial_integrable_beukersMeasure a b
  have he : (fun z : ℝ × ℝ => pairedMonomialValue p r.val z.1 * pairedMonomialValue p s.val z.2) =
      (fun z => (z.1^r.val * z.2^s.val + z.1^r.val * z.2^(s.val+p)) +
        (z.1^(r.val+p) * z.2^s.val + z.1^(r.val+p) * z.2^(s.val+p))) := by
    funext z
    dsimp [pairedMonomialValue]
    ring
  rw [he, integral_add ((hi _ _).add (hi _ _)) ((hi _ _).add (hi _ _)),
    integral_add (hi _ _) (hi _ _), integral_add (hi _ _) (hi _ _)]
  simp only [hm]
  simp only [pairedMonomialMatrix, Fin.sum_univ_two, Fin.val_zero, Fin.val_one,
    zero_mul, one_mul, add_zero, ite_self, Rat.cast_add]
  have hcross₁ : r.val ≠ s.val+p := by have := r.isLt; omega
  have hcross₂ : r.val+p ≠ s.val := by have := s.isLt; omega
  by_cases hrs : r = s
  · subst s
    simp [hcross₁, hcross₂]
    ring
  · have hvs : r.val ≠ s.val := fun he => hrs (Fin.ext he)
    have hvs' : r.val+p ≠ s.val+p := by omega
    simp [hrs, hvs, hvs', hcross₁, hcross₂]


/-- The denominator formulation printed in 6.3(1), with an integer numerator
and any denominator prime to p. -/
theorem theorem_6_3_rational_denominator (p : ℕ) [Fact p.Prime]
    (hp5 : 5 ≤ p) (a : ℤ) (b : ℕ) (hb : ¬ p ∣ b) :
    padicValRat p (pairedMonomialMatrix p ((a : ℚ)/b)).det = -7*(p : ℤ) ∧
      (pairedMonomialMatrix p ((a : ℚ)/b)).det ≠ 0 := by
  apply theorem_6_3_part_one p hp5
  by_cases ha : a = 0
  · simp [ha]
  have hb0 : b ≠ 0 := by
    intro he
    apply hb
    simp [he]
  rw [padicValRat.div (Int.cast_ne_zero.mpr ha) (Nat.cast_ne_zero.mpr hb0),
    padicValRat.of_int, padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd hb]
  simp

end ManuscriptChain.Beukers
