#!/usr/bin/env python3
"""Inspect and extend the manuscript attempt catalog without executing Lean.

Examples (from the repository root):
  python tools/chain_catalog.py list --item 3.4 --role alt
  python tools/chain_catalog.py validate
  python tools/chain_catalog.py render
  python tools/chain_catalog.py add --item 3.4 --role alt \
    --branch experiment/zetahyperbolic-p03-04_alt_i0002_construction \
    --commit <40-character-commit-sha> --target-url <immutable-target-url> \
    --relation corrected --parent P03_04.whole.alt.i0001 --dry-run

This is a local metadata tool. It does not create Git branches, execute builds,
validate mathematical proofs, or grant evidence tiers. Validation checks catalog
structure only; evidence receipts still require independent inspection.
"""

from __future__ import annotations

import argparse
import copy
import json
from pathlib import Path
import re
import sys
import tempfile


DEFAULT_CATALOG = Path(__file__).resolve().parents[1] / "docs" / "CHAIN_CATALOG.json"
ROLES = ("prop", "alt")
STAGES = ("construction", "subcritical", "critical", "soft_assertion")
UNVERIFIED_STATUSES = ("SOURCE_ONLY_UNCOMPILED", "DOCUMENTATION_ONLY_CANDIDATE", "SOURCE_ONLY_CANDIDATE")
SHA = re.compile(r"[0-9a-f]{40}\Z")
PART = re.compile(r"[a-z][a-z0-9_]*\Z")


class CatalogError(ValueError):
    """An invalid or inconsistent catalog entry."""


def require(condition: bool, message: str) -> None:
    if not condition:
        raise CatalogError(message)


def nonempty(value: object) -> bool:
    return isinstance(value, str) and bool(value.strip())


def identifier(module_key: str, part: str, role: str, iteration: int) -> str:
    return f"{module_key}.{part}.{role}.i{iteration:04d}"


def validate(catalog: dict) -> dict[str, tuple[dict, dict]]:
    """Check identity and reference integrity, never the truth of proof claims."""
    require(isinstance(catalog, dict), "Catalog must be an object")
    require(catalog.get("schema_version") == 1, "Unsupported schema_version")
    require(nonempty(catalog.get("repository")), "Missing repository")
    require(isinstance(catalog.get("source_snapshot_commit"), str) and
            bool(SHA.fullmatch(catalog["source_snapshot_commit"])),
            "source_snapshot_commit must be a lowercase full Git SHA")
    items = catalog.get("items")
    require(isinstance(items, list), "items must be a list")
    indexed: dict[str, tuple[dict, dict]] = {}
    seen_items: set[str] = set()
    seen_modules: set[str] = set()
    branches: set[str] = set()
    for item in items:
        require(isinstance(item, dict), "Each item must be an object")
        item_id = item.get("item_id")
        require(isinstance(item_id, str) and bool(re.fullmatch(r"[1-9]\d*\.[1-9]\d*", item_id)),
                f"Invalid item_id: {item_id!r}")
        require(item_id not in seen_items, f"Duplicate item: {item_id}")
        seen_items.add(item_id)
        chapter, number = map(int, item_id.split("."))
        module = f"P{chapter:02d}_{number:02d}"
        require(type(item.get("chapter")) is int and item["chapter"] == chapter,
                f"{item_id}: chapter mismatch")
        require(item.get("module_key") == module, f"{item_id}: module_key must be {module}")
        require(module not in seen_modules, f"Duplicate module_key: {module}")
        seen_modules.add(module)
        for field in ("title", "original_status", "original_source_url"):
            require(nonempty(item.get(field)), f"{item_id}: missing {field}")
        attempts = item.get("attempts")
        require(isinstance(attempts, list), f"{item_id}: attempts must be a list")
        for attempt in attempts:
            require(isinstance(attempt, dict), f"{item_id}: attempt must be an object")
            attempt_id = attempt.get("attempt_id")
            require(isinstance(attempt_id, str), f"{item_id}: missing attempt_id")
            require(attempt_id not in indexed, f"Duplicate attempt: {attempt_id}")
            role, part, iteration = (attempt.get(k) for k in ("role", "part", "iteration"))
            require(role in ROLES, f"{attempt_id}: invalid role")
            require(isinstance(part, str) and bool(PART.fullmatch(part)),
                    f"{attempt_id}: invalid part token")
            require(type(iteration) is int and iteration >= 1,
                    f"{attempt_id}: iteration must be a positive integer")
            require(attempt_id == identifier(module, part, role, iteration),
                    f"{attempt_id}: identity fields do not match")
            require(attempt.get("stage") in STAGES, f"{attempt_id}: invalid stage")
            for field in ("branch", "work_status", "relation_to_original", "target_url"):
                require(nonempty(attempt.get(field)), f"{attempt_id}: missing {field}")
            branch = attempt["branch"]
            require(branch not in branches, f"Duplicate branch registration: {branch}")
            branches.add(branch)
            require(isinstance(attempt.get("source_commit"), str) and
                    bool(SHA.fullmatch(attempt["source_commit"])),
                    f"{attempt_id}: source_commit must be a lowercase full Git SHA")
            prefix = (f"https://github.com/{catalog['repository']}/blob/"
                      f"{attempt['source_commit']}/")
            require(attempt["target_url"].startswith(prefix) and len(attempt["target_url"]) > len(prefix),
                    f"{attempt_id}: target_url must identify a file at its exact source_commit in this repository")
            for field in ("parents", "supersedes", "dependencies", "evidence"):
                require(isinstance(attempt.get(field), list), f"{attempt_id}: {field} must be a list")
            tier = attempt.get("new_proof_tier")
            require(tier in (None, "!", "!!", "!!!", "!!!!"), f"{attempt_id}: invalid new_proof_tier")
            claims_evidence = tier is not None or bool(re.search(
                r"(?:^|_)(?:PASS|PROVED|VERIFIED|CERTIFIED|COMPILED|AUDITED)(?:_|$)",
                attempt["work_status"]))
            require(not claims_evidence or bool(attempt["evidence"]),
                    f"{attempt_id}: proof/build status or tier requires evidence receipts")
            for field in ("parents", "supersedes"):
                references = attempt[field]
                require(all(nonempty(ref) for ref in references),
                        f"{attempt_id}: invalid {field} reference")
                require(len(references) == len(set(references)),
                        f"{attempt_id}: duplicate {field} reference")
            for dependency in attempt["dependencies"]:
                require(isinstance(dependency, dict), f"{attempt_id}: dependency must be an object")
                require(nonempty(dependency.get("attempt_id")), f"{attempt_id}: dependency needs attempt_id")
                require(nonempty(dependency.get("required_clause")),
                        f"{attempt_id}: dependency needs an exact required_clause")
                require(dependency.get("bridge_status") in ("OPEN", "VERIFIED"),
                        f"{attempt_id}: invalid bridge_status")
                require(isinstance(dependency.get("evidence"), list),
                        f"{attempt_id}: dependency evidence must be a list")
                if dependency["bridge_status"] == "VERIFIED":
                    require(bool(dependency["evidence"]),
                            f"{attempt_id}: VERIFIED bridge requires evidence receipts")
            indexed[attempt_id] = (item, attempt)

    for item in items:
        selected = item.get("selected_attempts", [])
        require(isinstance(selected, list) and all(nonempty(ref) for ref in selected),
                f"{item['item_id']}: selected_attempts must be a list of attempt IDs")
        require(len(selected) == len(set(selected)), f"{item['item_id']}: duplicate selected attempt")
        for reference in selected:
            require(reference in indexed, f"{item['item_id']}: unknown selected attempt {reference}")
            require(indexed[reference][0]["item_id"] == item["item_id"],
                    f"{item['item_id']}: selected attempt belongs to another item")

    edges: dict[str, set[str]] = {}
    for attempt_id, (_, attempt) in indexed.items():
        references = attempt["parents"] + attempt["supersedes"] + [
            d["attempt_id"] for d in attempt["dependencies"]
        ]
        for reference in references:
            require(reference in indexed, f"{attempt_id}: unknown reference {reference}")
            require(reference != attempt_id, f"{attempt_id}: cannot reference itself")
        edges[attempt_id] = set(references)
    # Combined lineage, replacement and dependency cycles are not evidence.
    done: set[str] = set()
    active: set[str] = set()

    def visit(node: str) -> None:
        require(node not in active, f"Cyclic lineage/dependency at {node}")
        if node in done:
            return
        active.add(node)
        for dependency in sorted(edges[node]):
            visit(dependency)
        active.remove(node)
        done.add(node)

    for node in indexed:
        visit(node)
    return indexed


def load_catalog(path: Path) -> dict:
    with path.open(encoding="utf-8") as handle:
        catalog = json.load(handle)
    validate(catalog)
    return catalog


def atomic_write(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.NamedTemporaryFile(mode="w", encoding="utf-8", newline="\n",
                                     dir=path.parent, delete=False) as handle:
        temporary = Path(handle.name)
        handle.write(text)
    try:
        temporary.replace(path)
    finally:
        temporary.unlink(missing_ok=True)


def append_attempt(catalog: dict, *, item_id: str, role: str, part: str,
                   branch: str, source_commit: str, target_url: str,
                   relation: str, parents: list[str], stage: str = "construction",
                   work_status: str = "DOCUMENTATION_ONLY_CANDIDATE") -> tuple[dict, dict]:
    """Allocate the next role/part-local ordinal; never edit an older record."""
    validate(catalog)
    updated = copy.deepcopy(catalog)
    item = next((i for i in updated["items"] if i["item_id"] == item_id), None)
    require(item is not None, f"Unknown item: {item_id}")
    iteration = 1 + max((a["iteration"] for a in item["attempts"]
                         if a["role"] == role and a["part"] == part), default=0)
    require(work_status in UNVERIFIED_STATUSES,
            "add only accepts unverified work statuses; it cannot register a proof or PASS")
    part_suffix = "" if part == "whole" else f"_{part}"
    item_branch = item["module_key"].lower().replace("_", "-")
    expected_branch = (f"experiment/zetahyperbolic-{item_branch}{part_suffix}_"
                       f"{role}_i{iteration:04d}_{stage}")
    require(branch == expected_branch, f"New attempt branch must be {expected_branch}")
    attempt = {
        "attempt_id": identifier(item["module_key"], part, role, iteration),
        "role": role, "part": part, "iteration": iteration,
        "branch": branch, "source_commit": source_commit, "stage": stage,
        "work_status": work_status, "relation_to_original": relation,
        "target_url": target_url, "parents": list(parents), "dependencies": [],
        "evidence": [], "supersedes": [], "new_proof_tier": None,
        "dependency_resolution_status": "CLAUSE_SELECTION_AND_COMPATIBILITY_PROOFS_REQUIRED",
    }
    item["attempts"].append(attempt)
    validate(updated)
    return updated, attempt


def markdown(value: object) -> str:
    return str(value).replace("|", "\\|").replace("\n", " ")


def render(catalog: dict) -> str:
    indexed = validate(catalog)
    lines = [
        "# Chain categorizer", "",
        "Generated from [CHAIN_CATALOG.json](CHAIN_CATALOG.json) by "
        "`python tools/chain_catalog.py render`. Edit the JSON and regenerate; "
        "do not use this table as an independent proof receipt.", "",
        "See the [categorizer guide](CHAIN_CATALOG_GUIDE.md) for iteration naming and registration rules.", "",
        f"{len(catalog['items'])} manuscript items; {len(indexed)} registered attempts. "
        "Each item/part/role admits multiple iterations. The registration ordinal "
        "does not establish historical chronology or mathematical progress.", "",
        "PROP and ALT statuses, original theorem status and downstream bridge "
        "evidence remain separate. A newer attempt does not automatically "
        "supersede an older one or certify the original statement.", "",
        "Use `list --item 3.4 --role alt` to filter, `validate` to check catalog "
        "structure, and `add --help` to register an existing branch snapshot. "
        "These commands do not create branches, execute Lean or verify proofs.", "",
    ]
    for item in sorted(catalog["items"], key=lambda i: tuple(map(int, i["item_id"].split(".")))):
        lines += [
            f"## {item['item_id']} — {markdown(item['title'])}", "",
            f"Original statement: {markdown(item['original_status'])}. "
            f"[Source register]({item['original_source_url']}).", "",
        ]
        if not item["attempts"]:
            lines += ["No research iteration registered; the original status above is preserved.", ""]
            continue
        lines += [
            "| Attempt | Role / part | Stage | Work status | Relation | Source | Parents / supersedes |",
            "| --- | --- | --- | --- | --- | --- | --- |",
        ]
        for attempt in sorted(item["attempts"], key=lambda a: (a["part"], a["role"], a["iteration"])):
            source = (f"[target]({attempt['target_url']}) · "
                      f"[{attempt['source_commit'][:12]}](https://github.com/{catalog['repository']}"
                      f"/tree/{attempt['source_commit']})")
            lineage = "parents: " + (", ".join(attempt["parents"]) or "—")
            lineage += "; supersedes: " + (", ".join(attempt["supersedes"]) or "—")
            cells = [attempt["attempt_id"], f"{attempt['role']} / {attempt['part']}",
                     attempt["stage"], attempt["work_status"], attempt["relation_to_original"],
                     source, lineage]
            lines.append("| " + " | ".join(markdown(c) for c in cells) + " |")
        lines.append("")
    lines += [
        "## Evidence and compatibility", "",
        "The JSON retains per-attempt dependencies and receipts. A dependency "
        "must name an exact required clause and an OPEN or VERIFIED bridge. "
        "VERIFIED requires evidence references, whose mathematical and compiler "
        "content must still be inspected independently. Structural validation "
        "does not grant `!`, `!!`, `!!!` or `!!!!`.", "",
    ]
    return "\n".join(lines)


def parser() -> argparse.ArgumentParser:
    root = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    root.add_argument("--catalog", type=Path, default=DEFAULT_CATALOG)
    commands = root.add_subparsers(dest="command", required=True)
    for name in ("list", "validate", "render", "add"):
        command = commands.add_parser(name)
        # Accept --catalog before or after the subcommand.
        command.add_argument("--catalog", type=Path, default=argparse.SUPPRESS)
        if name == "list":
            command.add_argument("--item")
            command.add_argument("--role", choices=ROLES)
            command.add_argument("--part")
            command.add_argument("--status")
        elif name == "render":
            command.add_argument("--output", type=Path, help="Defaults beside the catalog as CHAIN_CATALOG.md")
        elif name == "add":
            command.description = ("Register an existing branch and exact source commit. "
                                   "Appends metadata only; creates no branch or proof.")
            command.add_argument("--item", required=True)
            command.add_argument("--role", choices=ROLES, required=True)
            command.add_argument("--part", default="whole")
            command.add_argument("--branch", required=True)
            command.add_argument("--commit", required=True)
            command.add_argument("--target-url", required=True)
            command.add_argument("--relation", required=True)
            command.add_argument("--parent", action="append", default=[])
            command.add_argument("--stage", choices=STAGES, default="construction")
            command.add_argument("--work-status", choices=UNVERIFIED_STATUSES,
                                 default="DOCUMENTATION_ONLY_CANDIDATE")
            command.add_argument("--dry-run", action="store_true")
    return root


def main(argv: list[str] | None = None) -> int:
    args = parser().parse_args(argv)
    try:
        catalog = load_catalog(args.catalog)
        if args.command == "validate":
            count = len(validate(catalog))
            print(f"Catalog structure valid: {len(catalog['items'])} items, {count} attempts. No proof audit performed.")
        elif args.command == "list":
            print("ATTEMPT\tSTAGE\tWORK_STATUS\tBRANCH")
            for item in catalog["items"]:
                if args.item and item["item_id"] != args.item:
                    continue
                for attempt in item["attempts"]:
                    if any(value and attempt[field] != value for field, value in
                           (("role", args.role), ("part", args.part), ("work_status", args.status))):
                        continue
                    print("\t".join(attempt[k] for k in ("attempt_id", "stage", "work_status", "branch")))
        elif args.command == "render":
            output = args.output or args.catalog.with_name("CHAIN_CATALOG.md")
            atomic_write(output, render(catalog))
            print(f"Rendered {output}")
        elif args.command == "add":
            updated, attempt = append_attempt(
                catalog, item_id=args.item, role=args.role, part=args.part,
                branch=args.branch, source_commit=args.commit, target_url=args.target_url,
                relation=args.relation, parents=args.parent, stage=args.stage,
                work_status=args.work_status)
            if args.dry_run:
                print(json.dumps(attempt, ensure_ascii=False, indent=2))
            else:
                atomic_write(args.catalog, json.dumps(updated, ensure_ascii=False, indent=2) + "\n")
                print(f"Registered {attempt['attempt_id']}; run render to refresh the Markdown index.")
        return 0
    except (CatalogError, OSError, json.JSONDecodeError) as error:
        print(f"Catalog error: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
