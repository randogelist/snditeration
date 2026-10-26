# Independent integration — corrected continuous real-weight density and moment measure

Scope: support for the **corrected** Proposition 3.2 only, not the complete printed continuous-pencil theorem.

Donor: frozen failing combined PR #15 (`0cee4ea2e32b1f476488f92b476c4eb224285160`). Two modules individually built successfully in its CI: `ContinuousDensity` (`✔ [8740/8809]`) and `ContinuousMeasure` (`✔ [8767/8809]`), although downstream `ContinuousPencil` failed.

Exact unchanged donor files and Git blob SHA:
- `Zetahyperbolic/Section3/ContinuousDensity.lean`: `2f8e26b23d80cf34228ba024386047920ab34f7e`
- `Zetahyperbolic/Section3/ContinuousMeasure.lean`: `5fd5a4b6987136fc1ef92a5890ed38271a7a2652`

**Mathematical certified target:** Corrected real-s normalization `2 (2π)^(s-1)/Γ(s)`; the *printed prefactor* is larger by a factor `π/2`. Real-s kernel density positivity, monomial moment integrability/evaluation and positive actual rational-weighted measure with its moments. The derivations use the existing `HyperbolicMomentBernoulli` and `ConcreteMomentMeasure` on the destination.

**Not proved:** The full continuously parametrized spectral pencil with all-root realness, actual odd-s alignment and spectral determinant degree. The donor's `ContinuousPencil` failed; it is not imported here. Do not certify original printed 3.2 without correcting the stated normalization.

**Admission conditions:** pinned Lean 4.33/Mathlib full root build PASS, eight declared `#print axioms` checks only standard axioms, scanner PASS, exact source checksum match and SHA-leased PR merge. Following merge, main CI PASS and specific subclaim update to the 45/64 tracker. Preserve all parallel other-agent derivation branches and unrelated open PRs.
