# Alternative chain — manuscript 3.5

Role: ALT. Stage: construction. Status: DOCUMENTATION_ONLY_CANDIDATE.

[Original proposed chain](https://github.com/randogelist/snditeration/tree/experiment/zetahyperbolic-p03-05_prop_construction) · [Verbatim original and repair gates](https://github.com/randogelist/snditeration/blob/9b1900bd9effd5d660061d3d4ce356acbda72342/Experimental/P03_05/Target.md)

## Selected alternative target

Replace the printed fraction by the resolvent fraction for I+tB, t=X−ζ(s): diagonal entries 1+t a_i and squared off-diagonal terms t²b_i². Relate it to the actual principal determinant ratio with its Gram-determinant normalization. Work on the cyclic Krylov subspace; require cyclicity only for a full-length fraction.

Relation to original: **corrected**.

Correct scaling, normalization and continued-fraction orientation; allow early Lanczos termination. Exponential edge convergence is a separate conditional statement.

## Candidate upstream inputs

3.1. These are clause-selection tasks, not new axioms or certified dependency edges.

## Remaining obligations

- Construct the actual Lanczos/Krylov basis and prove the rational-function resolvent identity.
- Prove nonvanishing for numerical evaluations; identify any full-length cyclic vector.
- Establish an independent spectral-edge rate before attaching convergence.

Correction gate: Use a rational-function identity or explicit nested denominator conditions; do not infer cyclicity merely from a generic distinct-spectrum claim.

## Dual-chain input and acceptance rules

PROP preserves the original manuscript target. ALT records a separately named corrected, restricted, conditional or alternate-route target; it is not a proof of the original and is not presumed to repair every downstream claim.

Prerequisite item numbers below are candidate input locations, not blanket assumptions of entire printed theorems. For each one, select the exact source clause and track its hypotheses, definitions and evidence. If that input has a correction, use only the compatible corrected clause. A downstream consumer must prove that the selected ALT output supplies its exact required input, or explicitly revise its own target. Weaker statements do not automatically replace stronger ones. No cycle, known-false predecessor or own-target axiom is admissible proof progress.

This ALT branch is based on the main source snapshot and adds documentation only. It does not import or copy the PROP experiment's prerequisite axioms. No ALT Prerequisites.lean, Work.lean, target declaration or compiler receipt is created by this step. Constructing those typed interfaces remains work to do. The main snapshot's historical proofs keep their own immutable evidence; candidate and unimported files receive no new certification.

Before integration: fix the exact formal target and input clauses, prove any compatibility bridge, discharge custom axioms or expose them as explicit conditional hypotheses, then inspect the complete relevant compiler and transitive axiom evidence on the authorized target. No local Lean, workflow dispatch, proof-tier promotion or new theorem certification occurs in this publication.

## Immutable source locations

- [Experimental/P03_05/Prerequisites.lean](https://github.com/randogelist/snditeration/blob/9b1900bd9effd5d660061d3d4ce356acbda72342/Experimental/P03_05/Prerequisites.lean)
- [Experimental/P03_05/Target.md](https://github.com/randogelist/snditeration/blob/9b1900bd9effd5d660061d3d4ce356acbda72342/Experimental/P03_05/Target.md)
