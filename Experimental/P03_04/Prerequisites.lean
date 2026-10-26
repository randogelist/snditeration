import Zetahyperbolic

/-! SOURCE_ONLY_UNCOMPILED. The original finite-root indexing is not assumed.
The input below is an upstream shifted-inertia identity for actual principal
matrices, retaining zero eigenvalues. -/
noncomputable section
namespace Experimental.P03_04
open ManuscriptChain

axiom actualPrincipalShiftedInertia (p : Real.Parameters)
    (hp : Real.Admissible p) (r : ℕ) (choose : Fin r → Fin p.h)
    (hchoose : Function.Injective choose) (t : ℝ) :
  QuadraticForm.sigPos
      (((Principal.manuscriptPrincipalPencil p choose).direction -
        t • (Principal.manuscriptPrincipalPencil p choose).base).toQuadraticForm') =
    {i : Fin r |
      t < Spectral.actualEigenvalues (Principal.manuscriptPrincipalPencil p choose) i}.ncard

theorem existingPrincipalGramInput (p : Real.Parameters)
    (hp : Real.Admissible p) (r : ℕ) (choose : Fin r → Fin p.h)
    (hchoose : Function.Injective choose) :
    (Principal.manuscriptPrincipalPencil p choose).base.PosDef :=
  Principal.principal_base_posDef p hp choose hchoose

end Experimental.P03_04
