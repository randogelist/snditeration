# Alternative chain — manuscript 6.10

Role: ALT. Stage: construction. Status: DOCUMENTATION_ONLY_CANDIDATE.

[Original proposed chain](https://github.com/randogelist/snditeration/tree/experiment/zetahyperbolic-p06-10_prop_construction) · [Verbatim original and repair gates](https://github.com/randogelist/snditeration/blob/42275211433ab64ce66452b341ae210c90f391c8/Experimental/P06_10/Target.md)

## Selected alternative target

Keep the exact finite normalized-log determinant identity and the conditional rate identity when the named limits exist. For K∈N tending to infinity and integer coefficient matrices C_K∈M_{h(K)×(K+1)}(Z), assume h(K)≤K+1, full real row rank, and a fixed exponent A≥0 such that every entry satisfies |C_K(i,j)|≤(K+1)^A for every K. Target log det(C_K C_Kᵀ)/K²→0 using the available weaker finite upper bound. Omit strict equilibrium reweighting and the ratio >581 unless an explicit sufficient upper bound for the positive decay rate is proved.

Relation to original: **corrected**.

Separate finite/rate conservation from unproved equilibrium identification; replace the defective lower-decay argument and avoid claiming the exact printed finite Hadamard bound.

## Candidate upstream inputs

2.5, 3.1, 5.2. These are clause-selection tasks, not new axioms or certified dependency edges.

## Remaining obligations

- Prove the relevant limiting hypotheses for any concrete family.
- Identify actual pencil derivatives with C_K C_Kᵀ.
- Potential-energy identification and strict reweighting remain open; any numerical ratio needs the correct upper-decay premise.

Correction gate: The existing counterexample prevents deriving a lower bound on height/decay from only a lower bound on decay. Reuse compiled components only with their exact hypotheses and evidence.

## Dual-chain input and acceptance rules

PROP preserves the original manuscript target. ALT records a separately named corrected, restricted, conditional or alternate-route target; it is not a proof of the original and is not presumed to repair every downstream claim.

Prerequisite item numbers below are candidate input locations, not blanket assumptions of entire printed theorems. For each one, select the exact source clause and track its hypotheses, definitions and evidence. If that input has a correction, use only the compatible corrected clause. A downstream consumer must prove that the selected ALT output supplies its exact required input, or explicitly revise its own target. Weaker statements do not automatically replace stronger ones. No cycle, known-false predecessor or own-target axiom is admissible proof progress.

This ALT branch is based on the main source snapshot and adds documentation only. It does not import or copy the PROP experiment's prerequisite axioms. No ALT Prerequisites.lean, Work.lean, target declaration or compiler receipt is created by this step. Constructing those typed interfaces remains work to do. The main snapshot's historical proofs keep their own immutable evidence; candidate and unimported files receive no new certification.

Before integration: fix the exact formal target and input clauses, prove any compatibility bridge, discharge custom axioms or expose them as explicit conditional hypotheses, then inspect the complete relevant compiler and transitive axiom evidence on the authorized target. No local Lean, workflow dispatch, proof-tier promotion or new theorem certification occurs in this publication.

## Immutable source locations

- [Experimental/P06_10/Target.md](https://github.com/randogelist/snditeration/blob/42275211433ab64ce66452b341ae210c90f391c8/Experimental/P06_10/Target.md)
- [Experimental/P06_10/Assumptions.json](https://github.com/randogelist/snditeration/blob/42275211433ab64ce66452b341ae210c90f391c8/Experimental/P06_10/Assumptions.json)
- [Experimental/P06_10/Prerequisites.lean](https://github.com/randogelist/snditeration/blob/42275211433ab64ce66452b341ae210c90f391c8/Experimental/P06_10/Prerequisites.lean)
- [README.md](https://github.com/randogelist/snditeration/blob/a3904c2a97b47b0dc2af41dcc708ca41c968da96/README.md)
