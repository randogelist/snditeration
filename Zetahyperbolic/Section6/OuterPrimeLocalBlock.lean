import Zetahyperbolic.Section6.BeukersOuterValuation
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.Tactic

/-!
# Corrected local obstruction in Theorem 6.1(3)

The printed endpoint excludes every nonzero integral coefficient vector. That
is too strong: a vector divisible by p has zero reduction. The valid endpoint
excludes primitive vectors. The exact leading matrix and its residue-field
kernel are proved here, together with a transfer for any integral matrix whose
reduction is the leading matrix. The actual moment reduction is a separate
obligation; the transfer does not assume that obligation has been discharged.
-/

noncomputable section
open scoped Matrix BigOperators

namespace ManuscriptChain.Beukers

def localLeadingMatrix (p : ℕ) : Matrix (Fin 2) (Fin 2) (ZMod p) :=
  !![0, (6 : ZMod p)⁻¹; (6 : ZMod p)⁻¹, -1]

lemma six_ne_zero_mod (p : ℕ) (hp : 11 ≤ p) : (6 : ZMod p) ≠ 0 := by
  change ((6 : ℕ) : ZMod p) ≠ 0
  intro hz
  exact (Nat.not_dvd_of_pos_of_lt (by norm_num : 0 < 6) (by omega : 6 < p))
    ((ZMod.natCast_eq_zero_iff 6 p).mp hz)

theorem localLeadingMatrix_det (p : ℕ) :
    (localLeadingMatrix p).det = -(6 : ZMod p)⁻¹ ^ 2 := by
  simp [localLeadingMatrix, Matrix.det_fin_two, pow_two]

theorem localLeadingMatrix_det_ne_zero (p : ℕ) [Fact p.Prime] (hp : 11 ≤ p) :
    (localLeadingMatrix p).det ≠ 0 := by
  rw [localLeadingMatrix_det]
  exact neg_ne_zero.mpr (pow_ne_zero _ (inv_ne_zero (six_ne_zero_mod p hp)))

/-- The local leading matrix has no nonzero residue-field kernel. -/
theorem localLeadingMatrix_kernel (p : ℕ) [Fact p.Prime] (hp : 11 ≤ p)
    (c : Fin 2 → ZMod p) :
    (localLeadingMatrix p).mulVec c = 0 ↔ c = 0 := by
  constructor
  · intro h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    simp [localLeadingMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h0 h1
    have hc1 : c 1 = 0 := h0.resolve_left (six_ne_zero_mod p hp)
    have hc0 : c 0 = 0 := by
      simp only [hc1, neg_zero, add_zero] at h1
      exact (mul_eq_zero.mp h1).resolve_left (inv_ne_zero (six_ne_zero_mod p hp))
    funext i
    fin_cases i <;> assumption
  · rintro rfl
    simp

/-- Exact integral transfer: zero reduced output forces zero reduced input.
The matrix-reduction premise must be proved for the actual scaled moments. -/
theorem integral_local_kernel_iff (p : ℕ) [Fact p.Prime] (hp : 11 ≤ p)
    (A : Matrix (Fin 2) (Fin 2) ℤ_[p])
    (hA : A.map PadicInt.toZMod = localLeadingMatrix p)
    (c : Fin 2 → ℤ_[p]) :
    (∀ i, PadicInt.toZMod (A.mulVec c i) = 0) ↔
      (∀ i, PadicInt.toZMod (c i) = 0) := by
  have he : (fun i => PadicInt.toZMod (A.mulVec c i)) =
      (localLeadingMatrix p).mulVec (fun i => PadicInt.toZMod (c i)) := by
    rw [← hA]
    funext i
    simp [Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply]
  constructor
  · intro h
    have hz : (localLeadingMatrix p).mulVec (fun i => PadicInt.toZMod (c i)) = 0 := by
      rw [← he]
      funext i
      exact h i
    have hc := (localLeadingMatrix_kernel p hp _).mp hz
    exact fun i => congrFun hc i
  · intro h i
    have hc : (fun i => PadicInt.toZMod (c i)) = 0 := funext h
    have hz := (localLeadingMatrix_kernel p hp _).mpr hc
    rw [← he] at hz
    exact congrFun hz i

/-- A nonzero integral vector can have zero reduction: the literal printed
nonzero-vector conclusion must be replaced by a primitive-vector conclusion. -/
theorem nonzero_integral_vector_can_reduce_to_zero (p : ℕ) [Fact p.Prime] :
    ∃ c : Fin 2 → ℤ_[p], c ≠ 0 ∧ ∀ i, PadicInt.toZMod (c i) = 0 := by
  refine ⟨fun _ => (p : ℤ_[p]), ?_, ?_⟩
  · intro h
    have hp0 : (p : ℤ_[p]) = 0 := congrFun h 0
    have hn : p ≠ 0 := (Fact.out : p.Prime).ne_zero
    exact (Nat.cast_ne_zero.mpr hn) hp0
  · intro i
    simp

end ManuscriptChain.Beukers
