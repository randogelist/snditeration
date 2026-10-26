# Dual-chain addendum — 26 October 2026

The original policy below describes the first publication snapshot. Current work uses paired `_prop_construction` and `_alt_construction` branches for each unfinished original item; the old `_construction` refs and receipts remain intact.

- PROP inherits the original typed scaffolds and assumptions unchanged and adds `Chain.md`.
- ALT starts from main and adds a separate `Alt/Target.md` and `Alt/Plan.json`. These are documentation plans, not new Lean interfaces, axioms or proofs. The historical list of Lean files below applies to the original/PROP scaffolds, not to ALT.
- Preserve exact original, corrected, restricted and conditional scopes separately. Corrected 3.2 keeps its existing historical certification; its false original does not inherit it.
- An ALT output may serve any PROP or ALT consumer only through an independently proved implication to that consumer's exact input contract. If that implication fails, revise and relabel the consumer rather than treating the substitution as automatic.
- Select exact predecessor clauses, not a blanket theorem label. No same-target axiom, known-false predecessor or mutually assumed dependency cycle supplies completion.
- Keep source/dependency/toolchain evidence and transitive axiom audits separate for each target. A new branch or source-only plan earns no new `!`, `!!`, `!!!` or `!!!!`.
- No local Lean execution, workflow dispatch, proof-source changes or certified-import changes are part of this publication.

## Historical prerequisite-scaffold policy

# Experimental prerequisite modules

Workflow: `YOU_ARE_GOODWORKFLOWFRONTIER` v1_0_25.
Authorization: the user permits explicit prerequisite axioms in isolated experimental branches.
Baseline: `randogelist/snditeration@00c635cf99744d9fd336369c2382aede5d6c1f99`.

## Scope and status

Each unfinished numbered proof item has one `experiment/zetahyperbolic-pXX-YY_construction` branch.
The nine exact original statements already certified on main are shared, not duplicated.
Definition 2.1, remarks and Conjecture 4.11 are not new proof-item branches.
The original statement is retained verbatim in each `Target.md`; corrections remain separately identified.
These are source-only experimental modules. No Lean compilation, theorem completion or new proof tier is claimed.

## Files in each branch

- `Experimental/PXX_YY/Prerequisites.lean`: precise typed inputs, named prerequisite axioms where needed, and reuse of existing proven facts where available.
- `Experimental/PXX_YY/Assumptions.json`: axiom names, mathematical scope, prerequisite item links and unresolved interface/discharge obligations.
- `Experimental/PXX_YY/Target.md`: original statement, exact work boundary, repair issues and integration requirements.
- `Experimental/PXX_YY/Work.lean`: isolated entry point for subsequent work; no fabricated target proof.
- `Experimental/PXX_YY/Audit.lean`: explicit `#print axioms` requests for the named assumption boundary; future target declarations must be added when constructed.
- `Experimental/PXX_YY/RECEIPT.json`: baseline, source fingerprints and explicit uncompiled/unproved status.

Some inputs are already proved and require no new axiom. Some advanced object layers are not yet formalized: those branches explicitly identify the part covered by the typed interface and the remaining definitions. Empty source models, arbitrary `Prop` placeholders and an axiom asserting the item's own target are not completion mechanisms.

## What local means in Lean

An `axiom` is a kernel assumption. A namespace alone does not make it logically local.
Isolation here comes from the separate branch and the `Experimental/` import boundary.
Neither `Zetahyperbolic.lean`, `Zetahyperbolic/Audit.lean`, the certified library configuration nor existing proof sources imports these modules.
Main contains only the experiment index and policy; the branch-specific Lean sources live on their respective branches.

The original theorem is never inserted as its own prerequisite. A stronger equivalent conclusion is not a valid shortcut. A known false printed predecessor must be repaired or omitted from the active assumptions; it must not be used to close downstream work by contradiction.

## Dependency and proof accounting

Paper references, genuine mathematical prerequisites and currently typed inputs are recorded separately.
An input may cover only one subpart. It does not certify the whole named predecessor.
Experimental branches may assume a separately stated upstream result, but the upstream item remains open until independently discharged.
Dependency cycles cannot supply a proof: mutually assumed endpoints remain mutually conditional.

An experimental compilation may succeed while `#print axioms` reports the named local assumptions. Record that as experimental compilation with assumptions, not `!!`, `!!!` or `!!!!` for the full paper item.
The existing nine exact original results and all earlier verified components retain their original evidence. No experimental source creation changes their status.

## Integration gate

1. Preserve the exact target, definitions, quantifiers and hypotheses. Resolve any stated repair gate explicitly.
2. Prove the target relative to its declared inputs and list every transitive assumption actually used. An unused prerequisite is not evidence of a dependency.
3. Replace each local axiom with an independently proved declaration of exactly its type, or expose it as an explicit hypothesis of a precisely labelled conditional theorem. The unconditional paper endpoint remains open until its premises are discharged.
4. Remove the axiom/import path from the destination proof graph. Do not merge experimental assumptions into the certified library.
5. Compile and audit on the already authorized execution target. No local Lean is run by this modularization task and no GitHub CI target switch or workflow dispatch is implied.
6. Reuse only compatible source/dependency/toolchain fingerprints with a prior PASS from that same target. Validate new/invalidated modules and the final transitive axiom set before promoting a result.

Expected foundational axioms for certified endpoints remain `propext`, `Classical.choice` and `Quot.sound`. An exact conditional theorem with explicit hypotheses may be certified as conditional; custom prerequisite axioms do not silently become discharged hypotheses.
