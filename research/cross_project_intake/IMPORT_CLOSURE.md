# Import-closure and semantic adapters

The source tree snapshots are incomplete by design: upstream import closures may need additional files not present under companion/. All are inert .lean.txt, not executable Lean imports.

| Group | Prerequisites | Critical semantic mismatch |
|---|---|---|
| Lemma 2.3 / Theorem 5.4 | Section2DifferenceDerivative -> Section2RatFuncTranslation -> Section2TauLinear -> Section2PoleLinearSpace -> Section2RationalDomains -> Section2TauRepresentation. Other dependencies: Section2FiniteDifference, Section2RepresentationIndependence, Rebuild.PartialFractionsQuotient and their imports. | Destination has its own Tau/Real.Parameters/SimplePole coordinate types; prove actual defeq or explicit transport. |
| Proposition 4.3 | ComplexPadicDisk -> IsometricExtension -> PadicDisk -> pinned Mathlib. | Treat p-adic polynomial center nonzero and radius as stated; no input ζp valuation is provided. |
| Theorem 5.2 finite | Section5DualSpectrum -> PositiveSlopeSpectrum and SelectedMonomial; DualNullspace -> DualRowSeparation. | Finite coefficient arrays only, no actual 2-variable integral or infinite mode tail. |
| Theorem 5.2 algebraic Krein | KreinIdentity -> DualAffineAlgebra. | Infinite-mode equality requires an explicit Summable input; no Fubini for actual measure. |
| Theorem 4.1 / 4.7 | Section4ComplexComparison -> SpectralIrrationalityMeasureCriterion; Section4ManuscriptBridge -> finite 4.6/4.7/p-adic sources. | Full complex root gap or average/cap are required assumptions, not inferred. |
| Theorem 3.7 | ConsecutiveDerivativeZeros -> NormalizedNewton. | No-two-consecutive-zero does not imply each coefficient nonzero. |
| UnitLogMoments | Mathlib Gamma and improper integral modules. | Best independent first build; separate from double Beukers Fubini. |

Next handoff: P0-C (small p-adic 3 modules) then P0-A+P0-B shared rational domain, P1-A analytic primitive, P1-B dual polynomial algebra. Keep each GitHub PR small enough for a green integration receipt.
