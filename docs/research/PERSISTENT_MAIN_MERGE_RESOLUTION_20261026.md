# Merge of verified main into persistent gap-tracker branch — 26 October 2026

First parent (tracker development history): `2de10d9222ccbb000867c8f0d7d7b22c997f3c48`
Second parent (verified main): `7bb7c4081f0b105fd0e196024e4933b87d9a8360`

Conflict resolution:
- Keep main's `README.md`, `Zetahyperbolic.lean`, `Zetahyperbolic/Audit.lean`, `docs/FORMALIZATION_LEDGER.md`, and `docs/NEXT_ENDPOINT.md`.
- Preserve the older 32 KB tracker-specific README exactly at `docs/research/PERSISTENT_TRACKER_README_PREMERGE_20261026.md` for provenance.
- Preserve all 18 tracker-only research documents and JSON inventories at their original paths, including the 45-item paper gap tracker and 64-obligation register.

The tracker documents are dated research records, not substitutes for the current active theorem ledger, nor evidence of additional Lean proof certification. Keep current pinned Lean 4.33 root and Mathlib setup. All historical branch commits remain reachable through the first parent of the merge.
