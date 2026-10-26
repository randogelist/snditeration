import Zetahyperbolic.Section3.RationalIntegralBridge
import Zetahyperbolic.Section3.GeneralRootGap

/-!
Theorem 3.1 on the actual rational Hankel pencil. Every analytic obligation
is discharged by the concrete hyperbolic measure and its generator integrals.
Only the manuscript's structural parameter conditions remain as inputs.
This theorem concerns polynomial roots; it is not a zeta irrationality result.
-/

noncomputable section

namespace ManuscriptChain

def REALIZATION (p : Real.Parameters) (hp : Real.Admissible p) :
    Real.PositiveMomentRealization p :=
  ConcreteMoment.realization p (Hyperbolic.gram_eq_weighted_integral p hp)

theorem GRAM_POSITIVE (p : Real.Parameters) (hp : Real.Admissible p) :
    General.GramPositive p :=
  (REALIZATION p hp).gram_posDef

theorem MAIN_CHAIN_UNCONDITIONAL (p : Real.Parameters) (hp : Real.Admissible p) :
    General.GeneralStatement p :=
  General.theorem_3_1_general p hp (GRAM_POSITIVE p hp)

theorem EXACT_ZERO_FREE_DISK (p : Real.Parameters) (hp : Real.Admissible p) :
    ∃ radius : ℝ, 0 < radius ∧
      (∀ z : ℂ, ‖z - (Real.zeta p.weight : ℂ)‖ < radius →
        ¬ General.ComplexRoot p z) ∧
      (∃ z : ℂ, General.ComplexRoot p z ∧
        ‖z - (Real.zeta p.weight : ℂ)‖ = radius) := by
  let positive := GRAM_POSITIVE p hp
  exact ⟨General.zeroFreeRadius p hp positive,
    General.zeroFreeRadius_pos p hp positive,
    General.complex_zero_free_disk p hp positive,
    General.complex_root_on_boundary p hp positive⟩

theorem ROOTS_REAL (p : Real.Parameters) (hp : Real.Admissible p)
    (z : ℂ) (hz : General.ComplexRoot p z) : z.im = 0 :=
  General.roots_real p (GRAM_POSITIVE p hp) z hz

theorem CENTER_NONVANISHING (p : Real.Parameters) (hp : Real.Admissible p) :
    Real.evalQ (Real.delta p) (Real.zeta p.weight) ≠ 0 :=
  General.center_nonvanishing p (GRAM_POSITIVE p hp)

end ManuscriptChain
