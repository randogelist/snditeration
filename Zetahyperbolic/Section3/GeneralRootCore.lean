import Zetahyperbolic.Section3.HermitianFactorization

/-!
# General odd-weight Hankel theorem: factorization over the actual pencil

The actual Gram positivity hypothesis is explicit. Finite pole algebra
proves nonzero slope and exact degree without any analytic hypothesis.
-/

noncomputable section
open scoped BigOperators
open Polynomial

namespace ManuscriptChain.General

def GramPositive (p : Real.Parameters) : Prop :=
  (Real.gram p (Real.zeta p.weight)).PosDef

theorem delta_degree (p : Real.Parameters) : (Real.delta p).natDegree = p.h :=
  PoleDiagonalization.delta_natDegree p

theorem delta_nonzero (p : Real.Parameters) : Real.delta p ≠ 0 :=
  PoleDiagonalization.delta_ne_zero p

theorem derivative_nonsingular (p : Real.Parameters) :
    (Real.derivativeMatrix p).det ≠ 0 :=
  PoleDiagonalization.derivativeMatrix_det_ne_zero p

def factorization (p : Real.Parameters) (positive : GramPositive p) :
    Spectral.RootFactorization (Real.manuscriptPencil p) :=
  Spectral.rootFactorizationOfPosDef (Real.manuscriptPencil p) positive
    (derivative_nonsingular p)

def ComplexRoot (p : Real.Parameters) (z : ℂ) : Prop :=
  Polynomial.eval₂ (algebraMap ℚ ℂ) z (Real.delta p) = 0

theorem complex_eval_transport (p : Real.Parameters) (z : ℂ) :
    Polynomial.eval₂ (algebraMap ℝ ℂ) z
        (Real.manuscriptPencil p).detPolynomial =
      Polynomial.eval₂ (algebraMap ℚ ℂ) z (Real.delta p) := by
  rw [Real.manuscriptPencil_detPolynomial, Real.realPolynomial, Polynomial.eval₂_map]
  congr 1

theorem complex_root_iff (p : Real.Parameters) (positive : GramPositive p) (z : ℂ) :
    ComplexRoot p z ↔ ∃ i, z = ((factorization p positive).root i : ℂ) := by
  constructor
  · intro hz
    apply (factorization p positive).complex_root_location z
    rw [complex_eval_transport]
    exact hz
  · rintro ⟨i, rfl⟩
    unfold ComplexRoot
    rw [← complex_eval_transport]
    have he := Polynomial.eval₂_at_apply (algebraMap ℝ ℂ)
      ((factorization p positive).root i)
      (p := (Real.manuscriptPencil p).detPolynomial)
    simpa only [Complex.coe_algebraMap, (factorization p positive).eval_root,
      map_zero] using he

theorem roots_real (p : Real.Parameters) (positive : GramPositive p) (z : ℂ)
    (hz : ComplexRoot p z) : z.im = 0 := by
  obtain ⟨i, rfl⟩ := (complex_root_iff p positive z).mp hz
  simp

theorem roots_avoid_center (p : Real.Parameters) (positive : GramPositive p)
    (i : Fin p.h) : (factorization p positive).root i ≠ Real.zeta p.weight :=
  (factorization p positive).root_ne_center i

theorem center_nonvanishing (p : Real.Parameters) (positive : GramPositive p) :
    Real.evalQ (Real.delta p) (Real.zeta p.weight) ≠ 0 :=
  Real.delta_nonzero_of_positive p positive

end ManuscriptChain.General
