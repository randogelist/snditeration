import Zetahyperbolic

/-!
Experimental prerequisite ledger for printed Theorem 5.2.
SOURCE_ONLY_UNCOMPILED. The axiom below is a named analytic prerequisite,
not a proof of the Krein identity, the cone statement, or the whole target.
The literal fixed-K cone assertion is a repair gate; it is NOT axiomatized.
-/
noncomputable section
open MeasureTheory
namespace Experimental.P05_02

/-- Missing Hilbert-Schmidt input for the actual printed Beukers kernel.
Discharge by a genuine unit-square logarithmic integrability estimate. -/
axiom actual_density_memLp_two :
  MemLp ManuscriptChain.Beukers.density (2 : ENNReal)
    ManuscriptChain.Beukers.squareMeasure

-- Available proved inputs are imported, not re-assumed:
-- ManuscriptChain.Beukers.theorem_5_1_exact_moments
-- ManuscriptChain.Beukers.actual_monomial_krein_bilinear
-- ManuscriptChain.Beukers.polynomialMomentForm_eq_krein
-- ManuscriptChain.Section5DualSpectrum.actual_dual_degree
-- ManuscriptChain.Section5DualSpectrum.actual_dual_zeros_real

end Experimental.P05_02
