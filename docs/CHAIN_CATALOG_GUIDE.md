# Chain categorizer and repeated iterations

The catalog in [CHAIN_CATALOG.json](CHAIN_CATALOG.json) groups every numbered proof item by **chapter → item → part → role → iteration**. Its [generated table](CHAIN_CATALOG.md) is the browsable view. The [theorem register](../README.md) remains the mathematical status register; the [experiment manifest](EXPERIMENTS.json) retains immutable publication receipts.

## Identity and categories

| Field | Meaning |
| --- | --- |
| Item | Stable manuscript number, e.g. `3.4`; all 45 proof items are indexed. |
| Part | `whole` or a stable subpart key such as `part2`. Splitting work does not certify the whole item. |
| Role | `prop` for the original route; `alt` for a separately stated alternative. |
| Iteration | Monotone registration number within one item/part/role: `i0001`, `i0002`, … |
| Stage | `construction`, `subcritical`, `critical`, `soft_assertion`; an organizational label, never proof evidence. |
| Relation | Original, corrected, restricted, conditional or alternative proof route. |
| Work status | Documentation/source/build status of this attempt, independent of the original theorem's recorded status. |
| Lineage | Explicit parent and superseded attempt IDs. An unrelated competing route needs no invented parent. |
| Dependencies | Exact upstream attempt, required clause and compatibility-bridge status. Candidate item references alone are not admitted dependencies. |
| Evidence | Immutable source/run/audit records with exact scope. Empty evidence means no attempt-level evidence is recorded, not that historical results disappeared. |

For example, `P03_04.whole.alt.i0002` names the second registered whole-item alternative for 3.4. A separate `P03_04.part2.alt.i0001` begins work on that subpart. These are **naming examples**, not existing new attempts.

The initial 72 entries map the existing PROP/ALT branches to `i0001` without changing their names. This is a catalog registration convention, not a recovered historical iteration or Init sequence. The 36 older `_construction` branches remain provenance snapshots. The nine originally certified items are indexed with no new experimental attempt; attempts can be added later without altering their historical proof status.

## Branch naming for later attempts

Use a new branch for a new iteration:

```text
experiment/zetahyperbolic-p03-04_alt_i0002_construction
experiment/zetahyperbolic-p03-04_part2_alt_i0001_construction
```

Record the actual branch and exact commit in the catalog. Do not rename existing branches merely to fit this convention. An iteration may develop through ordinary commits; retain earlier evidence with its original source SHA. A materially revised target or competing construction gets a separate attempt so its hypotheses and evidence cannot silently replace another's.

## Use the categorizer

From a checkout of the repository, with Python 3 and no third-party dependencies:

```sh
python tools/chain_catalog.py list --item 3.4
python tools/chain_catalog.py list --role alt
python tools/chain_catalog.py validate
python tools/chain_catalog.py render
python tools/chain_catalog.py add --help
```

The `add` command registers an existing branch/commit and allocates the next iteration for its item, part and role. Supply its real target URL and relation, and optional parent IDs. It does not create a GitHub branch, contact GitHub, execute Lean, schedule a build or certify anything. Verify the remote branch/source first. Use `--dry-run` to inspect a proposed entry, then register and regenerate the table. The source JSON is authoritative; do not hand-edit the generated table.

## Selection, supersession and proof boundaries

Multiple iterations may remain active simultaneously. `selected_attempts` is an explicit editorial selection, initially empty; it grants no proof status. A newer number does not automatically select or supersede any attempt. Supersession is a work-planning relationship, not a logical implication and not permission to erase earlier evidence.

Keep parent/lineage links distinct from mathematical dependencies. When an alternative feeds any consumer, specify the exact needed clause and prove its compatibility bridge. If a weaker alternative does not supply that input, revise the consumer explicitly. An own-target axiom, a known-false predecessor or a mutually assumed dependency cycle never supplies completion.

The validator checks catalog structure, identities and graph consistency. It cannot check mathematics, verify GitHub source existence or certify compiler logs. A structurally valid record is not Lean PASS or `!!`. Historical original and corrected theorem evidence remains attached to its exact declaration and source. No mathematical status or original-item count changes with this categorizer.
