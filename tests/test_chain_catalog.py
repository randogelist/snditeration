"""Structural catalog tests. No Lean invocation or proof validation."""

import copy
import importlib.util
import json
from pathlib import Path
import tempfile
import unittest


SCRIPT = Path(__file__).resolve().parents[1] / "tools" / "chain_catalog.py"
SPEC = importlib.util.spec_from_file_location("chain_catalog", SCRIPT)
catalog_tool = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(catalog_tool)


def catalog():
    return {
        "schema_version": 1, "repository": "owner/repo", "source_snapshot_commit": "a" * 40,
        "items": [{"item_id": "3.4", "chapter": 3, "module_key": "P03_04",
                   "title": "Principal pencils", "original_status": "REPAIR",
                   "original_source_url": "https://example.org/register", "attempts": []}],
    }


def add(value, role="alt", part="whole", branch=None, parents=()):
    iteration = 1 + max((a["iteration"] for a in value["items"][0]["attempts"]
                         if a["role"] == role and a["part"] == part), default=0)
    part_suffix = "" if part == "whole" else f"_{part}"
    branch = branch or f"experiment/zetahyperbolic-p03-04{part_suffix}_{role}_i{iteration:04d}_construction"
    return catalog_tool.append_attempt(
        value, item_id="3.4", role=role, part=part, branch=branch,
        source_commit="b" * 40, target_url="https://github.com/owner/repo/blob/" + "b" * 40 + "/Target.md",
        relation="corrected", parents=list(parents))


class CatalogTests(unittest.TestCase):
    def test_iteration_scope_and_older_entries_unchanged(self):
        original = catalog()
        first, a1 = add(original)
        saved = copy.deepcopy(first)
        second, a2 = add(first, parents=[a1["attempt_id"]])
        third, p1 = add(second, role="prop")
        fourth, part1 = add(third, part="part2")
        self.assertEqual(a1["attempt_id"], "P03_04.whole.alt.i0001")
        self.assertEqual(a2["attempt_id"], "P03_04.whole.alt.i0002")
        self.assertEqual(p1["iteration"], 1)
        self.assertEqual(part1["iteration"], 1)
        self.assertEqual(first, saved)
        self.assertEqual(original["items"][0]["attempts"], [])
        self.assertEqual(fourth["items"][0]["original_status"], "REPAIR")
        self.assertEqual(a2["evidence"], [])
        self.assertIsNone(a2["new_proof_tier"])
        self.assertEqual(fourth["items"][0]["attempts"][0], a1)

    def test_duplicate_attempt_and_branch_rejected(self):
        first, a1 = add(catalog())
        duplicate = copy.deepcopy(first)
        duplicate["items"][0]["attempts"].append(copy.deepcopy(a1))
        with self.assertRaisesRegex(catalog_tool.CatalogError, "Duplicate attempt"):
            catalog_tool.validate(duplicate)
        duplicate["items"][0]["attempts"][1]["iteration"] = 2
        duplicate["items"][0]["attempts"][1]["attempt_id"] = "P03_04.whole.alt.i0002"
        with self.assertRaisesRegex(catalog_tool.CatalogError, "Duplicate branch"):
            catalog_tool.validate(duplicate)

    def test_unknown_and_self_references_rejected(self):
        first, a1 = add(catalog())
        with self.assertRaisesRegex(catalog_tool.CatalogError, "unknown reference"):
            add(first, parents=["P03_04.whole.alt.i9999"])
        first["items"][0]["attempts"][0]["supersedes"] = [a1["attempt_id"]]
        with self.assertRaisesRegex(catalog_tool.CatalogError, "cannot reference itself"):
            catalog_tool.validate(first)

    def test_dependency_cycle_rejected(self):
        first, a1 = add(catalog())
        second, a2 = add(first, parents=[a1["attempt_id"]])
        second["items"][0]["attempts"][0]["dependencies"] = [{
            "attempt_id": a2["attempt_id"], "required_clause": "exact finite input",
            "bridge_status": "OPEN", "evidence": [],
        }]
        with self.assertRaisesRegex(catalog_tool.CatalogError, "Cyclic"):
            catalog_tool.validate(second)

    def test_verified_bridge_requires_receipt_but_is_not_proof_audit(self):
        first, a1 = add(catalog())
        second, _ = add(first)
        dependency = {"attempt_id": a1["attempt_id"], "required_clause": "finite input",
                      "bridge_status": "VERIFIED", "evidence": []}
        second["items"][0]["attempts"][1]["dependencies"] = [dependency]
        with self.assertRaisesRegex(catalog_tool.CatalogError, "requires evidence"):
            catalog_tool.validate(second)
        dependency["evidence"] = [{"receipt_url": "https://example.org/receipt"}]
        self.assertEqual(len(catalog_tool.validate(second)), 2)

    def test_identity_and_source_commit_validated(self):
        first, _ = add(catalog())
        attempt = first["items"][0]["attempts"][0]
        attempt["iteration"] = 2
        with self.assertRaisesRegex(catalog_tool.CatalogError, "identity fields"):
            catalog_tool.validate(first)
        attempt["iteration"] = 1
        attempt["source_commit"] = "shortsha"
        with self.assertRaisesRegex(catalog_tool.CatalogError, "source_commit"):
            catalog_tool.validate(first)

    def test_render_contains_all_attempts_and_scope_warning(self):
        first, a1 = add(catalog())
        second, a2 = add(first)
        rendered = catalog_tool.render(second)
        self.assertIn(a1["attempt_id"], rendered)
        self.assertIn(a2["attempt_id"], rendered)
        self.assertIn("2 registered attempts", rendered)
        self.assertIn("does not grant", rendered)

    def test_dry_run_does_not_write(self):
        with tempfile.TemporaryDirectory() as folder:
            path = Path(folder) / "CHAIN_CATALOG.json"
            before = json.dumps(catalog())
            path.write_text(before, encoding="utf-8")
            args = ["add", "--catalog", str(path), "--item", "3.4", "--role", "alt",
                    "--branch", "experiment/zetahyperbolic-p03-04_alt_i0001_construction", "--commit", "b" * 40,
                    "--target-url", "https://github.com/owner/repo/blob/" + "b" * 40 + "/Target.md",
                    "--relation", "restricted", "--dry-run"]
            self.assertEqual(catalog_tool.main(args), 0)
            self.assertEqual(path.read_text(encoding="utf-8"), before)

    def test_selection_must_resolve_and_belong_to_item(self):
        first, a1 = add(catalog())
        first["items"][0]["selected_attempts"] = ["NONEXISTENT"]
        with self.assertRaisesRegex(catalog_tool.CatalogError, "unknown selected"):
            catalog_tool.validate(first)
        first["items"][0]["selected_attempts"] = [a1["attempt_id"]]
        other = copy.deepcopy(first["items"][0])
        other.update(item_id="3.5", module_key="P03_05", attempts=[])
        first["items"].append(other)
        with self.assertRaisesRegex(catalog_tool.CatalogError, "another item"):
            catalog_tool.validate(first)

    def test_mutable_target_and_unsupported_proof_claim_rejected(self):
        first, _ = add(catalog())
        attempt = first["items"][0]["attempts"][0]
        immutable = attempt["target_url"]
        attempt["target_url"] = "https://github.com/owner/repo/blob/main/Target.md"
        with self.assertRaisesRegex(catalog_tool.CatalogError, "exact source_commit"):
            catalog_tool.validate(first)
        attempt["target_url"] = immutable
        attempt["work_status"] = "FULLY_PROVED"
        attempt["new_proof_tier"] = "!!!!"
        with self.assertRaisesRegex(catalog_tool.CatalogError, "requires evidence"):
            catalog_tool.validate(first)

    def test_add_rejects_wrong_branch_ordinal_and_proof_status(self):
        first, _ = add(catalog())
        with self.assertRaisesRegex(catalog_tool.CatalogError, "i0002"):
            add(first, branch="experiment/zetahyperbolic-p03-04_alt_i0009_construction")
        with self.assertRaisesRegex(catalog_tool.CatalogError, "only accepts unverified"):
            catalog_tool.append_attempt(
                first, item_id="3.4", role="alt", part="whole",
                branch="experiment/zetahyperbolic-p03-04_alt_i0002_construction",
                source_commit="b" * 40,
                target_url="https://github.com/owner/repo/blob/" + "b" * 40 + "/Target.md",
                relation="corrected", parents=[], work_status="FULLY_PROVED")


if __name__ == "__main__":
    unittest.main()
