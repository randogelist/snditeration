# Alternative chain — manuscript 4.8

Role: ALT. Stage: construction. Status: DOCUMENTATION_ONLY_CANDIDATE.

[Original proposed chain](https://github.com/randogelist/snditeration/tree/experiment/zetahyperbolic-p04-08_prop_construction) · [Verbatim original and repair gates](https://github.com/randogelist/snditeration/blob/221ecd8f613ecf0f39ef7752af1386c4223ab110/Experimental/P04_08/Target.md)

## Selected alternative target

Restrict rational-root exclusion to roots independently known to lie in a specified upper-radius cluster, combined with an explicit rational-approximation lower bound. For actual polynomial factors, prove the finite factor-product degree inequalities with nonzero evaluation, leading coefficient and sign conditions explicit.

Relation to original: **corrected**.

Drop blanket small-denominator exclusion inferred from a lower spectral gap; introduce actual upper clustering only through an independently proved earlier result.

## Candidate upstream inputs

3.1, 4.4, 4.7. These are clause-selection tasks, not new axioms or certified dependency edges.

## Remaining obligations

- Exact upper-cluster membership for any root to which exclusion is applied.
- Finite factor-product/logarithm inequalities and multiplicity accounting.
- Discharge the actual zeta approximation lower bound.

Correction gate: The spectral cap gives a lower root-distance gap, never an upper cluster radius. No ex-falso use of the printed reversal.

## Dual-chain input and acceptance rules

PROP preserves the original manuscript target. ALT records a separately named corrected, restricted, conditional or alternate-route target; it is not a proof of the original and is not presumed to repair every downstream claim.

Prerequisite item numbers below are candidate input locations, not blanket assumptions of entire printed theorems. For each one, select the exact source clause and track its hypotheses, definitions and evidence. If that input has a correction, use only the compatible corrected clause. A downstream consumer must prove that the selected ALT output supplies its exact required input, or explicitly revise its own target. Weaker statements do not automatically replace stronger ones. No cycle, known-false predecessor or own-target axiom is admissible proof progress.

This ALT branch is based on the main source snapshot and adds documentation only. It does not import or copy the PROP experiment's prerequisite axioms. No ALT Prerequisites.lean, Work.lean, target declaration or compiler receipt is created by this step. Constructing those typed interfaces remains work to do. The main snapshot's historical proofs keep their own immutable evidence; candidate and unimported files receive no new certification.

Before integration: fix the exact formal target and input clauses, prove any compatibility bridge, discharge custom axioms or expose them as explicit conditional hypotheses, then inspect the complete relevant compiler and transitive axiom evidence on the authorized target. No local Lean, workflow dispatch, proof-tier promotion or new theorem certification occurs in this publication.

## Immutable source locations

- [Experimental/P04_08/Prerequisites.lean](https://github.com/randogelist/snditeration/blob/221ecd8f613ecf0f39ef7752af1386c4223ab110/Experimental/P04_08/Prerequisites.lean)
- [Experimental/P04_08/Target.md](https://github.com/randogelist/snditeration/blob/221ecd8f613ecf0f39ef7752af1386c4223ab110/Experimental/P04_08/Target.md)
