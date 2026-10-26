# Merge of main into continuation branch — 26 October 2026

First parent (original continuation): `0cee4ea2e32b1f476488f92b476c4eb224285160`
Second parent (verified main): `7bb7c4081f0b105fd0e196024e4933b87d9a8360`

## Resolved overlapping files
Main wins for `Zetahyperbolic.lean`, `Zetahyperbolic/Audit.lean`, `Zetahyperbolic/Section2/RationalTaylor.lean`, `Zetahyperbolic/Section3/ContinuousPencil.lean`, `Zetahyperbolic/Section5/BeukersMomentSeries.lean`, `Zetahyperbolic/Section6/CoefficientGramGrowth.lean`, `docs/FORMALIZATION_LEDGER.md` and `docs/NEXT_ENDPOINT.md`.

Main's formal root and imports remain the branch's active compiled proof graph. Later repaired, axiom-audited modules on main supersede older versions. These are explicit conflict choices, not certificates for older donor drafts.

## Preserved branch-only source
The original 17 candidate Lean modules and `docs/CONTINUATION_20261025.md` remain in their original paths and original Git blobs. These draft modules are **not imported by the main root**. Some were known to fail in the earlier bulk CI for PR #15. Their presence must not be counted as compilation, full theorem completion, or admission. To activate any of them, repair, import, compile and axiom-audit each exact declaration separately.

Both original histories are retained in this two-parent merge commit. Main itself was not modified.
