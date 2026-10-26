# Alternative chain — manuscript 6.6

Role: ALT. Stage: construction. Status: DOCUMENTATION_ONLY_CANDIDATE.

[Original proposed chain](https://github.com/randogelist/snditeration/tree/experiment/zetahyperbolic-p06-06_prop_construction) · [Verbatim original and repair gates](https://github.com/randogelist/snditeration/blob/08ecc99cf133d6f5c1a9398ecffd07605b2b6269/Experimental/P06_06/Target.md)

## Selected alternative target

For a fixed integer tuple a with a_k>0 and P_a(l)>0 for every integer l≥1, prove the actual coupled-weight moment identity and two-sided comparison c1·w_(2k+1)≤W_a≤c2·w_(2k+1), with c1>0 and c2 finite. Derive positive definiteness, actual affine-pencil identification and real roots with the explicit derivative nonsingularity condition; leave universal arithmetic multiplier rates out of this endpoint.

Relation to original: **restricted**.

Keep the analytic and spectral portion with its actual positivity cone; separate exact signature, optimal radius and arithmetic asymptotics.

## Candidate upstream inputs

2.2, 3.1. These are clause-selection tasks, not new axioms or certified dependency edges.

## Remaining obligations

- Prove coefficient-ratio convergence, series summability and shifted-functional calibration.
- Identify the derivative of the actual coupled pencil and prove nonsingularity.
- Exact signature, sharp radius and top-weight multiplier-rate preservation require separate transfers.

Correction gate: Every use of a corrected earlier functional requires equality with the actual shifted moment functional, not only a similar matrix shape.

## Dual-chain input and acceptance rules

PROP preserves the original manuscript target. ALT records a separately named corrected, restricted, conditional or alternate-route target; it is not a proof of the original and is not presumed to repair every downstream claim.

Prerequisite item numbers below are candidate input locations, not blanket assumptions of entire printed theorems. For each one, select the exact source clause and track its hypotheses, definitions and evidence. If that input has a correction, use only the compatible corrected clause. A downstream consumer must prove that the selected ALT output supplies its exact required input, or explicitly revise its own target. Weaker statements do not automatically replace stronger ones. No cycle, known-false predecessor or own-target axiom is admissible proof progress.

This ALT branch is based on the main source snapshot and adds documentation only. It does not import or copy the PROP experiment's prerequisite axioms. No ALT Prerequisites.lean, Work.lean, target declaration or compiler receipt is created by this step. Constructing those typed interfaces remains work to do. The main snapshot's historical proofs keep their own immutable evidence; candidate and unimported files receive no new certification.

Before integration: fix the exact formal target and input clauses, prove any compatibility bridge, discharge custom axioms or expose them as explicit conditional hypotheses, then inspect the complete relevant compiler and transitive axiom evidence on the authorized target. No local Lean, workflow dispatch, proof-tier promotion or new theorem certification occurs in this publication.

## Immutable source locations

- [Experimental/P06_06/Target.md](https://github.com/randogelist/snditeration/blob/08ecc99cf133d6f5c1a9398ecffd07605b2b6269/Experimental/P06_06/Target.md)
- [Experimental/P06_06/Assumptions.json](https://github.com/randogelist/snditeration/blob/08ecc99cf133d6f5c1a9398ecffd07605b2b6269/Experimental/P06_06/Assumptions.json)
- [Experimental/P06_06/Prerequisites.lean](https://github.com/randogelist/snditeration/blob/08ecc99cf133d6f5c1a9398ecffd07605b2b6269/Experimental/P06_06/Prerequisites.lean)
- [README.md](https://github.com/randogelist/snditeration/blob/a3904c2a97b47b0dc2af41dcc708ca41c968da96/README.md)
