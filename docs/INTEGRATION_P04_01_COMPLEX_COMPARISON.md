# P04.01 — independent root comparison integration

Donor PR #15: `0cee4ea2e32b1f476488f92b476c4eb224285160`. Two previously built source modules are ported unchanged: `ComparisonRadius.lean` and `ComplexComparison.lean`.

Exact mathematical scope: an integer polynomial's evaluation is nonzero and within factor two of the center value when all complex roots are separated from the center and the evaluation point satisfies an explicit closeness bound. Separation is a hypothesis, not a new fact about the manuscript's particular parameter family.

This branch modifies only the two modules, root import, audit and this note. It does not alter the other agent's active branches. Merge only after full destination build, standard-only axiom audit, placeholder scan and source-identity checks.
