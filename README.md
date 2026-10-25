# Zetahyperbolic — Lean 4.33.0 formalization

Formalization of *Spectral Theory and Diophantine Bounds for Hankel Determinants
of Odd Zeta Values* (21 October 2026), using Lean 4.33.0 and Mathlib commit
`db584cd6d46c92f209a44c0f1c829460d327499d`.

Workflow: `YOU_ARE_GOODWORKFLOWFRONTIER`, mode `A_TIER_EXECUTION`.
Historical ZIP checkpoints remain unchanged. The directly importable project
is in `Zetahyperbolic/`; archived theorem names are not proof certificates.

## Build and audit

With the pinned dependencies already provisioned:

```sh
lake build Zetahyperbolic
lake env lean Zetahyperbolic/Audit.lean
```

On Windows, run `run.cmd` using the installed Lean/Lake and compatible cached
Mathlib. Lake's dependency traces reuse unchanged project artifacts. A new
platform, compiler or changed dependency requires a compatible build; Windows
and Linux proof receipts are not silently treated as interchangeable.

For first-time provisioning only, `lake update` and `lake exe cache get`
resolve the pinned dependencies and retrieve Mathlib's cache. Normal verification
does not change the Mathlib revision.

## Proof scope

The current development constructs the actual hyperbolic moment measure,
identifies its integrals with the rational Hankel pencil, and discharges the
positive-definiteness input to the general odd-weight spectral theorem.
The exact compiled and audited boundary is recorded in
[the formalization ledger](docs/FORMALIZATION_LEDGER.md).

The main endpoints include `ManuscriptChain.MAIN_CHAIN_UNCONDITIONAL` and
`ManuscriptChain.ACTUAL_OPERATOR_ZERO_FREE_DISK`: exact degree, real roots avoiding
ζ(2k+1), and the sharp radius 1/‖B‖₂ attained by a root, for every
admissible tuple. The primitive integer polynomial inherits these results.
No assumption of pairwise distinct roots is inserted.

Section 2 proves full-domain pullback/reflection identities on actual simple-pole
rational-function domains. Section 3 also records the exact alternating pole
signs. Sections 4–6 retain open arithmetic and quantitative endpoints;
this repository does not establish irrationality of ζ(5) or ζ(7).

Some printed corollaries require corrections. See
[the manuscript repair notes](docs/MANUSCRIPT_REPAIRS.md) before attempting
those endpoints. A proof of a corrected statement is not reported as a proof
of the original false statement.
