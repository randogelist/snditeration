# Alternative chain — manuscript 6.15

Role: ALT. Stage: construction. Status: DOCUMENTATION_ONLY_CANDIDATE.

[Original proposed chain](https://github.com/randogelist/snditeration/tree/experiment/zetahyperbolic-p06-15_prop_construction) · [Verbatim original and repair gates](https://github.com/randogelist/snditeration/blob/70c77e8d18dfe091e5771b57beee867f474116d8/Experimental/P06_15/Target.md)

## Selected alternative target

For every k≥0 identify the actual odd Dirichlet beta value with its nonzero rational multiple of π^(2k+1), using the ordered-series/integral definition at β(1). Derive qualitative transcendence and the explicitly stated finite linear-independence consequences from an independently checked π-transcendence theorem. Separate all effective measures, rank-one Padé assertions and exterior asymptotics.

Relation to original: **restricted**.

Retain the qualitative arithmetic endpoint, repair the β(1) definition, and remove unproved numerical measure constants and exterior rates from the first endpoint.

## Candidate upstream inputs

. These are clause-selection tasks, not new axioms or certified dependency edges.

## Remaining obligations

- Identify the β(1) integral with the ordered alternating-series limit.
- Prove the all-k Euler-number evaluation and its nonzero coefficient.
- Import the checked π-transcendence source; specify the coefficient field for each independence claim.
- The Gram/rank-one construction, quantitative measure and corrected exterior asymptotic remain open.

Correction gate: Never identify β(1) with an unordered real tsum or infer a quantitative transcendence measure from qualitative π transcendence; use eta(1)=log 2 at the removable endpoint.

## Dual-chain input and acceptance rules

PROP preserves the original manuscript target. ALT records a separately named corrected, restricted, conditional or alternate-route target; it is not a proof of the original and is not presumed to repair every downstream claim.

Prerequisite item numbers below are candidate input locations, not blanket assumptions of entire printed theorems. For each one, select the exact source clause and track its hypotheses, definitions and evidence. If that input has a correction, use only the compatible corrected clause. A downstream consumer must prove that the selected ALT output supplies its exact required input, or explicitly revise its own target. Weaker statements do not automatically replace stronger ones. No cycle, known-false predecessor or own-target axiom is admissible proof progress.

This ALT branch is based on the main source snapshot and adds documentation only. It does not import or copy the PROP experiment's prerequisite axioms. No ALT Prerequisites.lean, Work.lean, target declaration or compiler receipt is created by this step. Constructing those typed interfaces remains work to do. The main snapshot's historical proofs keep their own immutable evidence; candidate and unimported files receive no new certification.

Before integration: fix the exact formal target and input clauses, prove any compatibility bridge, discharge custom axioms or expose them as explicit conditional hypotheses, then inspect the complete relevant compiler and transitive axiom evidence on the authorized target. No local Lean, workflow dispatch, proof-tier promotion or new theorem certification occurs in this publication.

## Immutable source locations

- [Experimental/P06_15/Target.md](https://github.com/randogelist/snditeration/blob/70c77e8d18dfe091e5771b57beee867f474116d8/Experimental/P06_15/Target.md)
- [Experimental/P06_15/Assumptions.json](https://github.com/randogelist/snditeration/blob/70c77e8d18dfe091e5771b57beee867f474116d8/Experimental/P06_15/Assumptions.json)
- [Experimental/P06_15/Prerequisites.lean](https://github.com/randogelist/snditeration/blob/70c77e8d18dfe091e5771b57beee867f474116d8/Experimental/P06_15/Prerequisites.lean)
- [README.md](https://github.com/randogelist/snditeration/blob/a3904c2a97b47b0dc2af41dcc708ca41c968da96/README.md)
