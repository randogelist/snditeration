import Zetahyperbolic.Section3.ShiftedMomentPositivity

/-!
# Strict mixed two-by-two Hankel minors

Strict logarithmic convexity makes every consecutive moment quotient strictly
increasing. Products of these quotients give the corresponding result at every
positive gap, proving positivity of arbitrary mixed two-by-two minors.
-/

noncomputable section
open MeasureTheory Matrix

namespace ManuscriptChain.ConcreteMoment

def momentValue (p : Real.Parameters) (a : ℕ) : ℝ :=
  ∫ t, t ^ a ∂momentMeasure p

theorem momentValue_pos (p : Real.Parameters) (a : ℕ) : 0 < momentValue p a := by
  simpa [Matrix.det_fin_one, momentValue] using solid_moment_det_pos p a 0 1

theorem momentValue_strict_logConvex (p : Real.Parameters) (a : ℕ) :
    momentValue p (a + 1) ^ 2 < momentValue p a * momentValue p (a + 2) := by
  have h := solid_moment_det_pos p a 0 2
  simp only [Matrix.det_fin_two, Fin.val_zero, Fin.val_one, Nat.add_zero,
    Nat.zero_add, Nat.add_assoc] at h
  change 0 < momentValue p a * momentValue p (a + 2) -
    momentValue p (a + 1) * momentValue p (a + 1) at h
  nlinarith

theorem momentRatio_strictMono (p : Real.Parameters) :
    StrictMono (fun a => momentValue p (a + 1) / momentValue p a) := by
  apply strictMono_nat_of_lt_succ
  intro a
  apply (div_lt_div_iff₀ (momentValue_pos p a) (momentValue_pos p (a + 1))).2
  have h := momentValue_strict_logConvex p a
  nlinarith

theorem momentGapRatio_pos (p : Real.Parameters) (d a : ℕ) :
    0 < momentValue p (a + d) / momentValue p a :=
  div_pos (momentValue_pos p _) (momentValue_pos p _)

theorem momentGapRatio_succ (p : Real.Parameters) (d a : ℕ) :
    momentValue p (a + (d + 1)) / momentValue p a =
      (momentValue p (a + d) / momentValue p a) *
        (momentValue p ((a + d) + 1) / momentValue p (a + d)) := by
  rw [← Nat.add_assoc]
  field_simp [(momentValue_pos p a).ne', (momentValue_pos p (a + d)).ne']

/-- Moment quotients increase strictly at every positive index gap. -/
theorem momentGapRatio_strictMono (p : Real.Parameters) {d : ℕ} (hd : 0 < d) :
    StrictMono (fun a => momentValue p (a + d) / momentValue p a) := by
  induction d with
  | zero => omega
  | succ d ih =>
      by_cases hd0 : d = 0
      · subst d
        exact momentRatio_strictMono p
      · have hprev := ih (Nat.pos_of_ne_zero hd0)
        intro a b hab
        rw [momentGapRatio_succ, momentGapRatio_succ]
        exact mul_lt_mul (hprev hab)
          (le_of_lt (momentRatio_strictMono p (Nat.add_lt_add_right hab d)))
          (momentGapRatio_pos p 1 (a + d))
          (momentGapRatio_pos p d b).le

/-- Strict positivity for arbitrary row and column gaps, not only adjacent
two-by-two submatrices. -/
theorem mixed_moment_two_pos (p : Real.Parameters) (i₀ i₁ j₀ j₁ : ℕ)
    (hi : i₀ < i₁) (hj : j₀ < j₁) :
    0 < momentValue p (i₀ + j₀) * momentValue p (i₁ + j₁) -
      momentValue p (i₀ + j₁) * momentValue p (i₁ + j₀) := by
  have h := momentGapRatio_strictMono p (Nat.sub_pos_of_lt hj)
    (Nat.add_lt_add_right hi j₀)
  have he₀ : i₀ + j₀ + (j₁ - j₀) = i₀ + j₁ := by omega
  have he₁ : i₁ + j₀ + (j₁ - j₀) = i₁ + j₁ := by omega
  rw [he₀, he₁] at h
  have hcross := (div_lt_div_iff₀
    (momentValue_pos p (i₀ + j₀)) (momentValue_pos p (i₁ + j₀))).1 h
  nlinarith

end ManuscriptChain.ConcreteMoment

namespace ManuscriptChain

/-- Every actual two-by-two minor selected by increasing row and column
indices has strictly positive determinant. -/
theorem GRAM_MIXED_TWO_MINOR_POSITIVE (p : Real.Parameters) (hp : Real.Admissible p)
    (rows cols : Fin 2 → Fin p.h) (hrows : StrictMono rows) (hcols : StrictMono cols) :
    0 < Matrix.det ((Real.gram p (Real.zeta p.weight)).submatrix rows cols) := by
  rw [Matrix.det_fin_two]
  simp only [Matrix.submatrix_apply, gram_eq_moment p hp]
  exact ConcreteMoment.mixed_moment_two_pos p (rows 0).val (rows 1).val
    (cols 0).val (cols 1).val (hrows (by decide)) (hcols (by decide))

end ManuscriptChain

