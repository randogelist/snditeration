import Zetahyperbolic.Section3.RootFactorization

/-!
# Root location and strict zero-free disks from finite spectral factors

Given constructed nonzero real beta_i, all complex roots lie on ℝ
and avoid the center. A uniform bound on |beta_i| gives a disk.
-/

noncomputable section
open scoped BigOperators
open Polynomial

namespace ManuscriptChain.Spectral.RootFactorization

variable {n : ℕ} {p : SymmetricAffinePencil n} (c : RootFactorization p)

include c

theorem eval_eq_zero_iff (x : ℝ) :
    p.detPolynomial.eval x = 0 ↔ ∃ i, x = c.root i := by
  rw [c.eval_eq, mul_eq_zero]
  simp only [c.base_det_ne_zero, false_or, Finset.prod_eq_zero_iff, Finset.mem_univ,
    true_and]
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨i, (linear_factor_eq_zero_iff p.center (c.beta i) x (c.beta_ne_zero i)).mp hi⟩
  · rintro ⟨i, hi⟩
    exact ⟨i, (linear_factor_eq_zero_iff p.center (c.beta i) x (c.beta_ne_zero i)).mpr hi⟩

theorem eval_root (i : Fin n) : p.detPolynomial.eval (c.root i) = 0 :=
  (c.eval_eq_zero_iff _).mpr ⟨i, rfl⟩

theorem root_ne_center (i : Fin n) : c.root i ≠ p.center := by
  intro h
  exact c.center_nonvanishing (h ▸ c.eval_root i)

theorem complex_root_location (z : ℂ)
    (hz : Polynomial.eval₂ (algebraMap ℝ ℂ) z p.detPolynomial = 0) :
    ∃ i, z = (c.root i : ℂ) := by
  have heval : Polynomial.eval₂ (algebraMap ℝ ℂ) z p.detPolynomial =
      ((Matrix.det p.base : ℝ) : ℂ) * ∏ i, (1 + (z - (p.center : ℂ)) * (c.beta i : ℂ)) := by
    rw [c.factorization]
    simp [spectralFactor, Polynomial.eval₂_finsetProd]
  rw [heval] at hz
  have hd : ((Matrix.det p.base : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr c.base_det_ne_zero
  have hp := (mul_eq_zero.mp hz).resolve_left hd
  obtain ⟨i, _, hi⟩ := Finset.prod_eq_zero_iff.mp hp
  refine ⟨i, ?_⟩
  have hb : (c.beta i : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (c.beta_ne_zero i)
  have hx := (linear_factor_eq_zero_iff (p.center : ℂ) (c.beta i : ℂ) z hb).mp hi
  simpa [root] using hx

theorem complex_root_im_zero (z : ℂ)
    (hz : Polynomial.eval₂ (algebraMap ℝ ℂ) z p.detPolynomial = 0) : z.im = 0 := by
  obtain ⟨i, rfl⟩ := c.complex_root_location z hz
  simp

theorem root_distance (i : Fin n) : |c.root i - p.center| = 1 / |c.beta i| := by
  have heq : c.root i - p.center = -((c.beta i)⁻¹) := by
    simp only [root]
    ring
  rw [heq, abs_neg, abs_inv, one_div]

theorem root_distance_lower_bound (bound : ℝ)
    (hbound : ∀ i, |c.beta i| ≤ bound) (i : Fin n) :
    1 / bound ≤ |c.root i - p.center| := by
  rw [c.root_distance]
  exact one_div_le_one_div_of_le (abs_pos.mpr (c.beta_ne_zero i)) (hbound i)

theorem eval_ne_zero_of_distance_lt (bound x : ℝ)
    (hbound : ∀ i, |c.beta i| ≤ bound)
    (hx : |x - p.center| < 1 / bound) : p.detPolynomial.eval x ≠ 0 := by
  intro hz
  obtain ⟨i, rfl⟩ := (c.eval_eq_zero_iff x).mp hz
  exact (not_lt_of_ge (c.root_distance_lower_bound bound hbound i)) hx

end ManuscriptChain.Spectral.RootFactorization

namespace ManuscriptChain.Real

theorem delta_real_natDegree (p : Parameters)
    (c : Spectral.RootFactorization (manuscriptPencil p)) :
    (realPolynomial (delta p)).natDegree = p.h := by
  rw [← manuscriptPencil_detPolynomial]
  exact c.natDegree_eq

end ManuscriptChain.Real
