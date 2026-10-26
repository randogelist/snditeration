import Zetahyperbolic.Section3.GeneralRootCore

/-!
# General odd-weight Hankel theorem: sharp finite zero-free radius

The spectral-radius statement follows from an actual constructed factorization.
Positive definiteness of the concrete Gram matrix remains a separate endpoint.
Pairwise distinct roots are not asserted.
-/

noncomputable section
open scoped BigOperators
open Polynomial

namespace ManuscriptChain.General

theorem indices_nonempty (p : Real.Parameters) (hp : Real.Admissible p) :
    (Finset.univ : Finset (Fin p.h)).Nonempty := by
  exact ⟨⟨0, Nat.sub_pos_of_lt hp.N_lt_K⟩, Finset.mem_univ _⟩

def spectralRadius (p : Real.Parameters) (hp : Real.Admissible p)
    (positive : GramPositive p) : ℝ :=
  Finset.univ.sup' (indices_nonempty p hp)
    (fun i => |(factorization p positive).beta i|)

theorem beta_abs_le (p : Real.Parameters) (hp : Real.Admissible p)
    (positive : GramPositive p) (i : Fin p.h) :
    |(factorization p positive).beta i| ≤ spectralRadius p hp positive := by
  unfold spectralRadius
  exact Finset.le_sup' (fun j => |(factorization p positive).beta j|)
    (Finset.mem_univ i)

theorem spectralRadius_pos (p : Real.Parameters) (hp : Real.Admissible p)
    (positive : GramPositive p) : 0 < spectralRadius p hp positive := by
  let i : Fin p.h := ⟨0, Nat.sub_pos_of_lt hp.N_lt_K⟩
  exact lt_of_lt_of_le
    (abs_pos.mpr ((factorization p positive).beta_ne_zero i))
    (beta_abs_le p hp positive i)

def zeroFreeRadius (p : Real.Parameters) (hp : Real.Admissible p)
    (positive : GramPositive p) : ℝ := 1 / spectralRadius p hp positive

theorem zeroFreeRadius_pos (p : Real.Parameters) (hp : Real.Admissible p)
    (positive : GramPositive p) : 0 < zeroFreeRadius p hp positive := by
  exact one_div_pos.mpr (spectralRadius_pos p hp positive)

theorem complex_root_distance (p : Real.Parameters) (hp : Real.Admissible p)
    (positive : GramPositive p) (z : ℂ) (hz : ComplexRoot p z) :
    zeroFreeRadius p hp positive ≤ ‖z - (Real.zeta p.weight : ℂ)‖ := by
  obtain ⟨i, rfl⟩ := (complex_root_iff p positive z).mp hz
  have h := (factorization p positive).root_distance_lower_bound
    (spectralRadius p hp positive) (beta_abs_le p hp positive) i
  simpa [zeroFreeRadius, ← Complex.ofReal_sub] using h

theorem complex_zero_free_disk (p : Real.Parameters) (hp : Real.Admissible p)
    (positive : GramPositive p) (z : ℂ)
    (hz : ‖z - (Real.zeta p.weight : ℂ)‖ < zeroFreeRadius p hp positive) :
    ¬ ComplexRoot p z := by
  intro hroot
  exact (not_lt_of_ge (complex_root_distance p hp positive z hroot)) hz

theorem zeroFreeRadius_attained (p : Real.Parameters) (hp : Real.Admissible p)
    (positive : GramPositive p) :
    ∃ i, |(factorization p positive).root i - Real.zeta p.weight| =
      zeroFreeRadius p hp positive := by
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup' (indices_nonempty p hp)
    (fun i => |(factorization p positive).beta i|)
  refine ⟨i, ?_⟩
  simpa only [zeroFreeRadius, spectralRadius, hi, Real.manuscriptPencil_center] using
    (factorization p positive).root_distance i

theorem complex_root_on_boundary (p : Real.Parameters) (hp : Real.Admissible p)
    (positive : GramPositive p) :
    ∃ z : ℂ, ComplexRoot p z ∧
      ‖z - (Real.zeta p.weight : ℂ)‖ = zeroFreeRadius p hp positive := by
  obtain ⟨i, hi⟩ := zeroFreeRadius_attained p hp positive
  refine ⟨((factorization p positive).root i : ℂ),
    (complex_root_iff p positive _).mpr ⟨i, rfl⟩, ?_⟩
  simpa [← Complex.ofReal_sub] using hi

theorem center_eq_riemannZeta (p : Real.Parameters) (hp : Real.Admissible p) :
    Real.zeta p.weight = (riemannZeta (p.weight : ℂ)).re := by
  apply Real.zeta_eq_riemannZeta_re
  unfold Real.Parameters.weight
  have hk := hp.k_pos
  omega

def GeneralStatement (p : Real.Parameters) : Prop :=
  (Real.delta p).natDegree = p.h ∧
  (Real.derivativeMatrix p).det ≠ 0 ∧
  Real.zeta p.weight = (riemannZeta (p.weight : ℂ)).re ∧
  ∃ (c : Spectral.RootFactorization (Real.manuscriptPencil p)) (radius : ℝ),
    0 < radius ∧
    (∀ z : ℂ, ComplexRoot p z ↔ ∃ i, z = (c.root i : ℂ)) ∧
    (∀ i, c.root i ≠ Real.zeta p.weight) ∧
    (∀ z : ℂ, ComplexRoot p z → z.im = 0) ∧
    (∀ z : ℂ, ‖z - (Real.zeta p.weight : ℂ)‖ < radius → ¬ ComplexRoot p z)

theorem theorem_3_1_general (p : Real.Parameters) (hp : Real.Admissible p)
    (positive : GramPositive p) : GeneralStatement p := by
  refine ⟨delta_degree p, derivative_nonsingular p, center_eq_riemannZeta p hp,
    factorization p positive, zeroFreeRadius p hp positive,
    zeroFreeRadius_pos p hp positive, ?_, ?_, ?_, ?_⟩
  · exact complex_root_iff p positive
  · exact roots_avoid_center p positive
  · exact roots_real p positive
  · exact complex_zero_free_disk p hp positive

end ManuscriptChain.General
