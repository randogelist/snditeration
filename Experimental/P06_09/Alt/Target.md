# Alternative chain — manuscript 6.9

Role: ALT. Stage: construction. Status: DOCUMENTATION_ONLY_CANDIDATE.

[Original proposed chain](https://github.com/randogelist/snditeration/tree/experiment/zetahyperbolic-p06-09_prop_construction) · [Verbatim original and repair gates](https://github.com/randogelist/snditeration/blob/c88ecbb039e08e8355065b5e9649183e1f934e2e/Experimental/P06_09/Target.md)

## Selected alternative target

For the displayed R_n^(3), n≥1 and rational P with deg P<6n, construct the actual partial fractions allowing zero Laurent coefficients, explicitly omit the cancelled pole at k=0, and identify the coefficients of ζ(s), ζ(s+1), ζ(s+2) in the residue-functional evaluation. Leave universal noncancellation and determinant valuations as separate strengthened targets over the recomputed nonzero pole set.

Relation to original: **corrected**.

Remove the false every-node nonzero triple-pole coefficient premise; use actual surviving poles and recomputed Laurent data.

## Candidate upstream inputs

2.5, 5.7. These are clause-selection tasks, not new axioms or certified dependency edges.

## Remaining obligations

- Prove cancellation and exact partial fractions for the actual rational function.
- Determine all surviving pole orders and the correct coefficient formulas.
- Construct the actual determinant, prove noncancellation on its polynomial space, and recompute mod-q blocks and exponents.

Correction gate: The j=1 numerator contributes t^6 while the denominator contributes t^3 at k=0. Neither the printed coefficient formula nor its downstream valuation may be retained without recomputation.

## Dual-chain input and acceptance rules

PROP preserves the original manuscript target. ALT records a separately named corrected, restricted, conditional or alternate-route target; it is not a proof of the original and is not presumed to repair every downstream claim.

Prerequisite item numbers below are candidate input locations, not blanket assumptions of entire printed theorems. For each one, select the exact source clause and track its hypotheses, definitions and evidence. If that input has a correction, use only the compatible corrected clause. A downstream consumer must prove that the selected ALT output supplies its exact required input, or explicitly revise its own target. Weaker statements do not automatically replace stronger ones. No cycle, known-false predecessor or own-target axiom is admissible proof progress.

This ALT branch is based on the main source snapshot and adds documentation only. It does not import or copy the PROP experiment's prerequisite axioms. No ALT Prerequisites.lean, Work.lean, target declaration or compiler receipt is created by this step. Constructing those typed interfaces remains work to do. The main snapshot's historical proofs keep their own immutable evidence; candidate and unimported files receive no new certification.

Before integration: fix the exact formal target and input clauses, prove any compatibility bridge, discharge custom axioms or expose them as explicit conditional hypotheses, then inspect the complete relevant compiler and transitive axiom evidence on the authorized target. No local Lean, workflow dispatch, proof-tier promotion or new theorem certification occurs in this publication.

## Immutable source locations

- [Experimental/P06_09/Target.md](https://github.com/randogelist/snditeration/blob/c88ecbb039e08e8355065b5e9649183e1f934e2e/Experimental/P06_09/Target.md)
- [Experimental/P06_09/Assumptions.json](https://github.com/randogelist/snditeration/blob/c88ecbb039e08e8355065b5e9649183e1f934e2e/Experimental/P06_09/Assumptions.json)
- [Experimental/P06_09/Prerequisites.lean](https://github.com/randogelist/snditeration/blob/c88ecbb039e08e8355065b5e9649183e1f934e2e/Experimental/P06_09/Prerequisites.lean)
- [README.md](https://github.com/randogelist/snditeration/blob/a3904c2a97b47b0dc2af41dcc708ca41c968da96/README.md)
