# Alternative chain — manuscript 3.8

Role: ALT. Stage: construction. Status: DOCUMENTATION_ONLY_CANDIDATE.

[Original proposed chain](https://github.com/randogelist/snditeration/tree/experiment/zetahyperbolic-p03-08_prop_construction) · [Verbatim original and repair gates](https://github.com/randogelist/snditeration/blob/8588dce972ddd7ef61906202066965fc1c01d56d/Experimental/P03_08/Target.md)

## Selected alternative target

First formulate the pole-kernel spectral identity directly with the inverse of the actual finite Gram matrix. Separately prove the matrix-curve identity d(log det Gτ)/dτ=tr(Gτ⁻¹Gτ′) under differentiability and positive definiteness, then identify Gτ′ by dominated differentiation of the actual Laplace density.

Relation to original: **alternative_proof_route**.

Separate finite matrix identities from orthogonal-polynomial and analytic realization layers; keep X=ξ fixed.

## Candidate upstream inputs

2.5, 3.1. These are clause-selection tasks, not new axioms or certified dependency edges.

## Remaining obligations

- Actual monic orthogonal-polynomial kernel identification.
- τ=1 density identification and all-order domination/differentiation.
- Integral and trace interchange on the actual parameter family.

Correction gate: An arbitrary matrix-curve theorem does not certify the manuscript Laplace family without the identification maps.

## Dual-chain input and acceptance rules

PROP preserves the original manuscript target. ALT records a separately named corrected, restricted, conditional or alternate-route target; it is not a proof of the original and is not presumed to repair every downstream claim.

Prerequisite item numbers below are candidate input locations, not blanket assumptions of entire printed theorems. For each one, select the exact source clause and track its hypotheses, definitions and evidence. If that input has a correction, use only the compatible corrected clause. A downstream consumer must prove that the selected ALT output supplies its exact required input, or explicitly revise its own target. Weaker statements do not automatically replace stronger ones. No cycle, known-false predecessor or own-target axiom is admissible proof progress.

This ALT branch is based on the main source snapshot and adds documentation only. It does not import or copy the PROP experiment's prerequisite axioms. No ALT Prerequisites.lean, Work.lean, target declaration or compiler receipt is created by this step. Constructing those typed interfaces remains work to do. The main snapshot's historical proofs keep their own immutable evidence; candidate and unimported files receive no new certification.

Before integration: fix the exact formal target and input clauses, prove any compatibility bridge, discharge custom axioms or expose them as explicit conditional hypotheses, then inspect the complete relevant compiler and transitive axiom evidence on the authorized target. No local Lean, workflow dispatch, proof-tier promotion or new theorem certification occurs in this publication.

## Immutable source locations

- [Experimental/P03_08/Prerequisites.lean](https://github.com/randogelist/snditeration/blob/8588dce972ddd7ef61906202066965fc1c01d56d/Experimental/P03_08/Prerequisites.lean)
- [Experimental/P03_08/Target.md](https://github.com/randogelist/snditeration/blob/8588dce972ddd7ef61906202066965fc1c01d56d/Experimental/P03_08/Target.md)
