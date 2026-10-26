import Mathlib

/-! Positive, distinct tuples for finite products of atomless moment measures. -/
noncomputable section
open MeasureTheory Filter Set
open scoped BigOperators

namespace ManuscriptChain.MomentProductSupport

variable (μ : Measure ℝ) [SigmaFinite μ]

theorem pi_ae_pos (n : ℕ) (hμ : ∀ᵐ t ∂μ, 0 < t) :
    ∀ᵐ x : Fin n → ℝ ∂Measure.pi (fun _ : Fin n => μ), ∀ i, 0 < x i := by
  exact ae_all_iff.mpr (fun i =>
    (Measure.quasiMeasurePreserving_eval (fun _ : Fin n => μ) i).ae hμ)

theorem pi_ne_zero (n : ℕ) (hμ : μ ≠ 0) :
    Measure.pi (fun _ : Fin n => μ) ≠ 0 := by
  have hu : μ Set.univ ≠ 0 := Measure.measure_univ_ne_zero.mpr hμ
  intro hz
  have hv := congrArg (fun ν : Measure (Fin n → ℝ) => ν Set.univ) hz
  have hp : (∏ _i : Fin n, μ Set.univ) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun _ _ => hu)
  apply hp
  simpa [Measure.pi_univ] using hv

theorem pi_ae_injective [NullSingletonClass μ] (n : ℕ) :
    ∀ᵐ x : Fin n → ℝ ∂Measure.pi (fun _ : Fin n => μ), Function.Injective x := by
  induction n with
  | zero =>
    exact Eventually.of_forall (fun x i => Fin.elim0 i)
  | succ n ih =>
    let P : ℝ × (Fin n → ℝ) → Prop := fun z => Function.Injective (Fin.cons z.1 z.2)
    have hm : MeasurableSet {z | P z} := by
      simp only [P, Fin.cons_injective_iff, Set.mem_range, not_exists, Function.Injective]
      measurability
    have hp : ∀ᵐ z ∂μ.prod (Measure.pi (fun _ : Fin n => μ)), P z := by
      apply (Measure.ae_prod_iff_ae_ae hm).mpr
      apply Eventually.of_forall
      intro t
      have havoid : ∀ᵐ x : Fin n → ℝ ∂Measure.pi (fun _ : Fin n => μ),
          ∀ i, x i ≠ t := ae_all_iff.mpr (fun i =>
            Measure.ae_eval_ne (fun _ : Fin n => μ) i t)
      filter_upwards [havoid, ih] with x hx hix
      apply Fin.cons_injective_iff.mpr
      refine ⟨?_, hix⟩
      rintro ⟨i, hi⟩
      exact hx i hi
    have h := (measurePreserving_piFinSuccAbove
      (fun _ : Fin (n+1) => μ) 0).quasiMeasurePreserving.ae hp
    filter_upwards [h] with x hx
    change Function.Injective (Fin.cons (x 0) (fun i => x (Fin.succAbove 0 i))) at hx
    simp only [Fin.zero_succAbove] at hx
    change Function.Injective (Fin.cons (x 0) (Fin.tail x)) at hx
    simpa only [Fin.cons_self_tail] using hx

end ManuscriptChain.MomentProductSupport
