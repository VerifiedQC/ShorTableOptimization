#!/usr/bin/env python3
"""Construct and verify the best-known Lean generator from published results."""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path, PurePosixPath
import re
import shutil
import tempfile
from typing import Any
import zipfile

from scripts.leaderboard import validate_config, weighted_cost
from scripts.verifier import (
    ALLOWED_AXIOMS,
    BANNED_PATTERNS,
    parse_axiom_names,
    parse_metric_output,
    run_cmd,
    strip_lean_comments,
)


SOURCE_PREFIX = "TableGeneration.Submission.Policy"
SOURCE_ROOT = PurePosixPath("TableGeneration/Submission")
ACCEPTED_ROOT = Path("TableGeneration/Policies/Accepted")
BEST_KNOWN_PATH = Path("TableGeneration/BestKnown.lean")
ARCHIVED_CATALOG_PATH = Path("TableGeneration/RecursiveCost/ArchivedCatalog.lean")
# The planner ranks by gate count, so it considers every accepted PhaseProduct
# table rather than only the per-target champions. A policy that never held a
# champion slot can still be the cheapest choice at some width.
CATALOG_MODE = "PhaseProduct"
BEST_KNOWN_REPORT_PATH = Path("leaderboard/best-known.md")
METRIC_FIELDS = (
    "arithmetic_operation_count",
    "parallel_phase_product_layer_count",
    "phase_product_count",
    "total_operation_count",
    "point_count",
    "weighted_cost",
)


def read_json(path: Path) -> dict[str, Any]:
    value = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(value, dict):
        raise ValueError(f"{path} must contain a JSON object")
    return value


def module_id(policy_id: str) -> str:
    if re.fullmatch(r"[0-9a-f]{40,64}", policy_id):
        return "P" + policy_id[:12]
    digest = hashlib.sha256(policy_id.encode("utf-8")).hexdigest()
    return "P" + digest[:12]


def policy_by_id(leaderboard: dict[str, Any]) -> dict[str, dict[str, Any]]:
    policies = leaderboard.get("policies")
    if not isinstance(policies, list):
        raise ValueError("leaderboard policies must be an array")
    result: dict[str, dict[str, Any]] = {}
    for policy in policies:
        if not isinstance(policy, dict) or not isinstance(policy.get("policy_id"), str):
            raise ValueError("leaderboard policy identity is invalid")
        result[policy["policy_id"]] = policy
    return result


def selected_champions(
    leaderboard: dict[str, Any],
    config_targets: list[dict[str, Any]],
) -> list[dict[str, Any]]:
    policies = policy_by_id(leaderboard)
    champions = leaderboard.get("champions")
    if not isinstance(champions, list):
        raise ValueError("leaderboard champions must be an array")
    champion_by_target: dict[tuple[str, int], dict[str, Any]] = {}
    for champion in champions:
        if not isinstance(champion, dict):
            raise ValueError("leaderboard champion must be an object")
        mode = champion.get("mode")
        k = champion.get("k")
        ids = champion.get("policy_ids")
        if not isinstance(mode, str) or not isinstance(k, int):
            raise ValueError("leaderboard champion target is invalid")
        if not isinstance(ids, list) or not ids or not all(
            isinstance(policy_id, str) for policy_id in ids
        ):
            raise ValueError("leaderboard champion policy_ids must be nonempty strings")
        policy_id = sorted(ids)[0]
        policy = policies.get(policy_id)
        if policy is None:
            raise ValueError(f"champion policy {policy_id} is missing")
        policy_results = policy.get("results")
        if not isinstance(policy_results, list):
            raise ValueError(f"champion policy {policy_id} has invalid results")
        metrics = next(
            (
                item
                for item in policy_results
                if isinstance(item, dict)
                and item.get("mode") == mode
                and item.get("k") == k
            ),
            None,
        )
        if metrics is None:
            raise ValueError(f"champion policy {policy_id} lacks {mode} k={k}")
        champion_by_target[(mode, k)] = {
            "mode": mode,
            "k": k,
            "policy_id": policy_id,
            "module_id": module_id(policy_id),
            "policy": policy,
            "metrics": metrics,
        }
    configured = {(target["mode"], target["k"]) for target in config_targets}
    unexpected = sorted(set(champion_by_target) - configured)
    if unexpected:
        raise ValueError(f"leaderboard has champions outside the benchmark: {unexpected}")
    return [
        champion_by_target[key]
        for key in ((target["mode"], target["k"]) for target in config_targets)
        if key in champion_by_target
    ]


def portable_members(archive: zipfile.ZipFile) -> list[zipfile.ZipInfo]:
    # This is the INSTALL set, deliberately narrower than the archive. The
    # archive also carries Submission/Defs.lean and Submission/Correctness.lean
    # so a submission can be reconstructed exactly; those two are adapters that
    # exist on the base branch and are not installed per policy, and
    # install_policy's path mapping below assumes every member sits under
    # Policy/. Widening this filter without reworking that mapping would break
    # promotion.
    members = []
    for info in archive.infolist():
        path = PurePosixPath(info.filename)
        if path.is_absolute() or ".." in path.parts:
            raise ValueError("source archive contains an unsafe path")
        if info.is_dir() or path.suffix != ".lean":
            continue
        if path == SOURCE_ROOT / "Policy.lean" or SOURCE_ROOT / "Policy" in path.parents:
            members.append(info)
    if not any(PurePosixPath(info.filename) == SOURCE_ROOT / "Policy.lean" for info in members):
        raise ValueError("source archive lacks TableGeneration/Submission/Policy.lean")
    return members


def install_policy(repo: Path, results_root: Path, selection: dict[str, Any]) -> None:
    policy = selection["policy"]
    source = policy.get("source")
    if not isinstance(source, dict) or not isinstance(source.get("archive_path"), str):
        raise ValueError(f"policy {selection['policy_id']} has no source archive")
    archive_path = results_root / source["archive_path"]
    if not archive_path.is_file():
        raise ValueError(f"source archive does not exist: {archive_path}")

    accepted_prefix = (
        f"TableGeneration.Policies.Accepted.{selection['module_id']}"
    )
    destination_root = repo / ACCEPTED_ROOT
    with zipfile.ZipFile(archive_path) as archive:
        for info in portable_members(archive):
            source_path = PurePosixPath(info.filename)
            relative = source_path.relative_to(SOURCE_ROOT)
            if relative == PurePosixPath("Policy.lean"):
                destination = destination_root / f"{selection['module_id']}.lean"
            else:
                destination = destination_root / selection["module_id"] / Path(
                    *relative.parts[1:]
                )
            text = archive.read(info).decode("utf-8")
            if SOURCE_PREFIX not in text:
                raise ValueError(f"portable policy file lacks namespace prefix: {source_path}")
            destination.parent.mkdir(parents=True, exist_ok=True)
            destination.write_text(
                text.replace(SOURCE_PREFIX, accepted_prefix),
                encoding="utf-8",
            )


def dispatch_lines(
    selections: list[dict[str, Any]],
    field: str,
    arguments: str,
    fallback: str,
) -> list[str]:
    if not selections:
        return [f"  {fallback}"]
    lines = []
    for index, selection in enumerate(selections):
        prefix = "if" if index == 0 else "else if"
        lines.append(
            f"  {prefix} mode = .{selection['mode']} ∧ k = {selection['k']} then"
        )
        namespace = f"Policies.Accepted.{selection['module_id']}.implementation"
        lines.append(f"    {namespace}.{field}")
        lines.append(f"      {arguments}")
    lines.append("  else")
    lines.append(f"    {fallback}")
    return lines


def champion_layer_bound(leaderboard: dict[str, Any]) -> dict[int, int]:
    """Parallel phase-product layers of the champion at each catalogue arity.

    The planner minimises gates and the gate model charges nothing for depth, so
    without a bound a table could buy gates by adding sequential layers. Until
    the benchmark states a depth rule of its own, the champion's layer count is
    the bound: a candidate may match it but not exceed it.
    """
    policies = policy_by_id(leaderboard)
    bound: dict[int, int] = {}
    for champion in leaderboard.get("champions", []):
        if champion.get("mode") != CATALOG_MODE:
            continue
        k = champion.get("k")
        ids = champion.get("policy_ids")
        if not isinstance(k, int) or not isinstance(ids, list) or not ids:
            raise ValueError("leaderboard champion target is invalid")
        policy = policies.get(sorted(ids)[0])
        if policy is None:
            raise ValueError(f"champion policy for {CATALOG_MODE} k={k} is missing")
        metrics = next(
            (
                item
                for item in policy.get("results", [])
                if isinstance(item, dict)
                and item.get("mode") == CATALOG_MODE
                and item.get("k") == k
            ),
            None,
        )
        if metrics is None:
            raise ValueError(f"champion lacks {CATALOG_MODE} k={k} metrics")
        layers = metrics.get("parallel_phase_product_layer_count")
        if not isinstance(layers, int):
            raise ValueError(f"champion {CATALOG_MODE} k={k} has no layer count")
        bound[k] = layers
    return bound


def catalog_entries(
    leaderboard: dict[str, Any],
    config_targets: list[dict[str, Any]],
    *,
    bound_layers: bool = True,
) -> list[dict[str, Any]]:
    """Every accepted PhaseProduct table, champion or not, as planner candidates.

    With `bound_layers` (the default), candidates deeper than the champion at
    the same arity are excluded; see `champion_layer_bound`. With it off, the
    whole accepted set comes back. The website plans over the unbounded set, so
    the oracle needs to be able to as well, or the two cannot be compared.
    """
    configured = {
        target["k"] for target in config_targets if target["mode"] == CATALOG_MODE
    }
    layer_bound = champion_layer_bound(leaderboard) if bound_layers else {}
    entries: list[dict[str, Any]] = []
    for policy in leaderboard.get("policies", []):
        policy_id = policy.get("policy_id")
        if not isinstance(policy_id, str):
            raise ValueError("leaderboard policy identity is invalid")
        results = policy.get("results")
        if not isinstance(results, list):
            raise ValueError(f"policy {policy_id} has invalid results")
        for item in results:
            if not isinstance(item, dict) or item.get("mode") != CATALOG_MODE:
                continue
            k = item.get("k")
            if not isinstance(k, int):
                raise ValueError(f"policy {policy_id} has an invalid k")
            if k not in configured:
                continue
            layers = item.get("parallel_phase_product_layer_count")
            if not isinstance(layers, int):
                raise ValueError(f"policy {policy_id} {CATALOG_MODE} k={k} has no layer count")
            bound = layer_bound.get(k)
            if bound is not None and layers > bound:
                continue
            entries.append(
                {
                    "policy_id": policy_id,
                    "module_id": module_id(policy_id),
                    "k": k,
                    "policy": policy,
                }
            )
    # Deterministic order: by arity, then by policy id.
    entries.sort(key=lambda entry: (entry["k"], entry["policy_id"]))
    return entries


def _candidate_lines(entries: list[dict[str, Any]], name: str) -> list[str]:
    lines = [f"def {name} : List Candidate :="]
    if not entries:
        lines.append("  []")
        return lines
    for index, entry in enumerate(entries):
        opener = "  [ " if index == 0 else "  , "
        accepted = f"Policies.Accepted.{entry['module_id']}"
        lines.append(f"{opener}{{ policyId := {json.dumps(entry['policy_id'])}")
        lines.append(f"    , k := {entry['k']}")
        lines.append("    , hk := by decide")
        lines.append(f"    , program := {accepted}.implementation.generate")
        lines.append(f"        .{CATALOG_MODE} {entry['k']} (by decide) }}")
    lines.append("  ]")
    return lines


def generate_archived_catalog(
    repo: Path,
    entries: list[dict[str, Any]],
    unbounded: list[dict[str, Any]] | None = None,
) -> None:
    unbounded = entries if unbounded is None else unbounded
    modules = sorted(
        {entry["module_id"] for entry in entries}
        | {entry["module_id"] for entry in unbounded}
    )
    lines = ["import TableGeneration.RecursiveCost.Catalog"]
    lines.extend(
        f"import TableGeneration.Policies.Accepted.{module}" for module in modules
    )
    lines.extend(
        [
            "",
            "namespace TableGeneration.RecursiveCost",
            "",
            "open Operations",
            "",
            "/- This file is generated by scripts/promote.py. -/",
            "",
            "/--",
            "Every accepted `PhaseProduct` table, as planner candidates.",
            "",
            "`bestKnownCandidates` holds one champion per arity, chosen by the",
            "leaderboard's structural weighted cost. The planner ranks by gate count,",
            "which is a different objective, so a table that lost its champion slot can",
            "still be the cheapest choice at some width. This list is every accepted",
            "table that is within the champion's layer bound at its arity, and is what",
            "the planner searches. For the set without that bound, which is what the",
            "leaderboard site plans over, see `archivedCandidatesUnbounded` below.",
            "-/",
        ]
    )
    lines.extend(_candidate_lines(entries, "archivedCandidates"))
    lines.extend(
        [
            "",
            "/--",
            "The same set with the champion layer bound lifted.",
            "",
            "`promote.py` drops candidates deeper than the champion at their arity, so",
            "`archivedCandidates` is a subset of the accepted tables. The leaderboard",
            "site applies no such bound: it plans over every accepted `PhaseProduct`",
            "table in `results.json`. Without this list the two cannot be compared, and",
            "the published gate count would rest on tables the Lean/JS differential",
            "never sees.",
            "-/",
        ]
    )
    lines.extend(_candidate_lines(unbounded, "archivedCandidatesUnbounded"))
    lines.extend(["", "end TableGeneration.RecursiveCost", ""])
    (repo / ARCHIVED_CATALOG_PATH).write_text("\n".join(lines), encoding="utf-8")


def generate_best_known(repo: Path, selections: list[dict[str, Any]]) -> None:
    modules = sorted({selection["module_id"] for selection in selections})
    lines = ["import TableGeneration.Policy"]
    lines.extend(
        f"import TableGeneration.Policies.Accepted.{module}" for module in modules
    )
    lines.extend(
        [
            "",
            "namespace TableGeneration",
            "",
            "open Operations",
            "",
            "/- This file is generated by scripts/promote.py. -/",
            "",
            "def bestKnownGeneratedPoints (mode : ProductMode) (k : Nat) : List Point :=",
        ]
    )
    lines.extend(
        dispatch_lines(
            selections,
            "generatedPoints",
            "mode k",
            "baselineGeneratedPoints mode k",
        )
    )
    lines.extend(
        [
            "",
            "def bestKnownGeneratePointsInOrder",
            "    (mode : ProductMode) (k : Nat) (hk : k >= 2) : List Point :=",
        ]
    )
    lines.extend(
        dispatch_lines(
            selections,
            "generatePointsInOrder",
            "mode k hk",
            "baselineGeneratePointsInOrder mode k hk",
        )
    )
    lines.extend(
        [
            "",
            "def bestKnownGenerate",
            "    (mode : ProductMode) (k : Nat) (hk : k >= 2) : Prog k :=",
        ]
    )
    lines.extend(
        dispatch_lines(
            selections,
            "generate",
            "mode k hk",
            "baselineGenerate mode k hk",
        )
    )
    lines.extend(
        [
            "",
            "def bestKnownPolicyId (mode : ProductMode) (k : Nat) : String :=",
        ]
    )
    if selections:
        for index, selection in enumerate(selections):
            prefix = "if" if index == 0 else "else if"
            lines.append(
                f"  {prefix} mode = .{selection['mode']} ∧ k = {selection['k']} then"
            )
            lines.append(f"    {json.dumps(selection['policy_id'])}")
        lines.extend(["  else", '    "general"'])
    else:
        lines.append('  "general"')
    lines.extend(["", "end TableGeneration", ""])
    (repo / BEST_KNOWN_PATH).write_text("\n".join(lines), encoding="utf-8")


def generate_best_known_report(
    repo: Path,
    selections: list[dict[str, Any]],
    configured_target_count: int,
) -> None:
    lines = [
        "# Best-Known Table-Generation Results",
        "",
        "Generated from verified per-target champion policies.",
        "",
        f"Coverage: **{len(selections)} of {configured_target_count}** targets.",
        "",
        "| Target | Weighted cost | Arithmetic ops | Parallel layers | Phase products | Total ops | Generated points |",
        "| --- | ---: | ---: | ---: | ---: | ---: | ---: |",
    ]
    for selection in selections:
        metrics = selection["metrics"]
        lines.append(
            f"| `{selection['mode']}` `k={selection['k']}` "
            f"| **{metrics['weighted_cost']}** "
            f"| {metrics['arithmetic_operation_count']} "
            f"| {metrics['parallel_phase_product_layer_count']} "
            f"| {metrics['phase_product_count']} "
            f"| {metrics['total_operation_count']} "
            f"| {metrics['point_count']} |"
        )
    lines.append("")
    (repo / BEST_KNOWN_REPORT_PATH).write_text("\n".join(lines), encoding="utf-8")


def construct(
    repo: Path,
    results_root: Path,
    leaderboard: dict[str, Any],
    config_targets: list[dict[str, Any]],
) -> list[dict[str, Any]]:
    selections = selected_champions(leaderboard, config_targets)
    entries = catalog_entries(leaderboard, config_targets)
    unbounded = catalog_entries(leaderboard, config_targets, bound_layers=False)
    module_ids: dict[str, str] = {}
    for record in [*selections, *unbounded]:
        previous = module_ids.setdefault(record["module_id"], record["policy_id"])
        if previous != record["policy_id"]:
            raise ValueError("promoted policy identifiers have a module-name collision")
    accepted = repo / ACCEPTED_ROOT
    if accepted.exists():
        shutil.rmtree(accepted)
    installed: set[str] = set()
    # Champions first, then any catalog-only policy: the planner searches tables
    # that never won a target, so their modules have to be installed too.
    for record in [*selections, *unbounded]:
        if record["policy_id"] not in installed:
            install_policy(repo, results_root, record)
            installed.add(record["policy_id"])
    generate_best_known(repo, selections)
    generate_archived_catalog(repo, entries, unbounded)
    generate_best_known_report(repo, selections, len(config_targets))
    return selections


def evaluate_targets(
    repo: Path, selections: list[dict[str, Any]]
) -> list[dict[str, Any]]:
    """Reproduce all metrics together; verify_source checks the Lean proofs."""
    source = [
        "import TableGeneration.BestKnown",
        "import TableGeneration.Metrics",
        "",
        "open TableGeneration",
        "open TableGeneration.Operations",
        "",
    ]
    for index, selection in enumerate(selections):
        mode = selection["mode"]
        k = selection["k"]
        source.extend(
            [
                f"def targetMode{index} : ProductMode := .{mode}",
                f"def targetK{index} : Nat := {k}",
                f"def targetProgram{index} : Prog targetK{index} := "
                f"bestKnownGenerate targetMode{index} targetK{index} (by decide)",
                f"def targetPoints{index} : List Point := "
                f"bestKnownGeneratedPoints targetMode{index} targetK{index}",
                f"def targetOrder{index} : List Point := "
                f"bestKnownGeneratePointsInOrder targetMode{index} targetK{index} "
                "(by decide)",
                "",
                f'#eval IO.println "PROMOTION_METRICS_BEGIN:{index}"',
                f'#eval IO.println ("mode={mode}")',
                f'#eval IO.println ("k={k}")',
                f'#eval IO.println ("policy_id=" ++ bestKnownPolicyId targetMode{index} targetK{index})',
                f'#eval IO.println ("total_operation_count=" ++ toString targetProgram{index}.length)',
                f'#eval IO.println ("arithmetic_operation_count=" ++ toString (arithmeticOperationCount targetProgram{index}))',
                f'#eval IO.println ("phase_product_count=" ++ toString (phaseProductCount targetProgram{index}))',
                f'#eval IO.println ("parallel_phase_product_layer_count=" ++ toString (parallelPhaseProductLayerCount targetProgram{index}))',
                f'#eval IO.println ("expected_point_count=" ++ toString (targetMode{index}.pointCount targetK{index}))',
                f'#eval IO.println ("point_count=" ++ toString targetPoints{index}.length)',
                f'#eval IO.println ("point_order_count=" ++ toString targetOrder{index}.length)',
                f'#eval IO.println "PROMOTION_METRICS_END:{index}"',
                "",
            ]
        )
    with tempfile.TemporaryDirectory() as tmp:
        source_path = Path(tmp) / "EvaluateBestKnown.lean"
        source_path.write_text("\n".join(source), encoding="utf-8")
        result = run_cmd(["lake", "env", "lean", str(source_path)], repo, 300)
    if result["returncode"] != 0:
        raise ValueError(f"could not evaluate promoted metrics: {result['output']}")

    integer_fields = (
        "k",
        "total_operation_count",
        "arithmetic_operation_count",
        "phase_product_count",
        "parallel_phase_product_layer_count",
        "expected_point_count",
        "point_count",
        "point_order_count",
    )
    evaluated = []
    for index, selection in enumerate(selections):
        mode = selection["mode"]
        k = selection["k"]
        metrics = parse_metric_output(
            str(result["output"]),
            begin=f"PROMOTION_METRICS_BEGIN:{index}",
            end=f"PROMOTION_METRICS_END:{index}",
        )
        required = {"mode", "policy_id", *integer_fields}
        missing = sorted(required - metrics.keys())
        if missing:
            raise ValueError(
                f"could not read {mode} k={k} metrics: {', '.join(missing)} missing"
            )
        for field in integer_fields:
            metrics[field] = int(metrics[field])
        if metrics["mode"] != mode or metrics["k"] != k:
            raise ValueError(f"promoted metric target {index} is mislabeled")
        if metrics["point_count"] != metrics["expected_point_count"]:
            raise ValueError(f"{mode} k={k} generated the wrong number of points")
        if metrics["point_order_count"] != metrics["point_count"]:
            raise ValueError(f"{mode} k={k} point order length is invalid")
        if metrics["phase_product_count"] != metrics["point_count"]:
            raise ValueError(f"{mode} k={k} phase-product count is invalid")
        evaluated.append(metrics)
    return evaluated


def verify_source(repo: Path, selections: list[dict[str, Any]]) -> None:
    failures = []
    for path in sorted((repo / ACCEPTED_ROOT).glob("**/*.lean")):
        text = strip_lean_comments(path.read_text(encoding="utf-8"))
        for label, pattern in BANNED_PATTERNS.items():
            if pattern.search(text):
                failures.append(f"{path.relative_to(repo)}: banned {label}")
    if failures:
        raise ValueError("; ".join(failures))

    modules = sorted({selection["module_id"] for selection in selections})
    source = [
        "import TableGeneration.BestKnown",
        "",
        "open TableGeneration",
        "open TableGeneration.Operations",
        "",
    ]
    for module in modules:
        name = f"TableGeneration.Policies.Accepted.{module}.implementation"
        source.append(f"#print axioms {name}")
    for selection in selections:
        name = (
            "TableGeneration.Policies.Accepted."
            f"{selection['module_id']}.implementation"
        )
        mode = selection["mode"]
        k = selection["k"]
        source.append(
            f"#check {name}.generatedPoints_valid .{mode} {k} "
            "(by decide) (by decide)"
        )
        source.append(
            f"#check {name}.generate_safe .{mode} {k} "
            "(by decide) (by decide)"
        )
    with tempfile.TemporaryDirectory() as tmp:
        source_path = Path(tmp) / "PromotionAxioms.lean"
        source_path.write_text("\n".join(source) + "\n", encoding="utf-8")
        result = run_cmd(["lake", "env", "lean", str(source_path)], repo, 600)
    if result["returncode"] != 0:
        raise ValueError(f"could not inspect promoted axioms: {result['output']}")
    unexpected = parse_axiom_names(str(result["output"])) - ALLOWED_AXIOMS
    if unexpected:
        raise ValueError("promoted policies use disallowed axioms: " + ", ".join(unexpected))


def verify(
    repo: Path,
    config: dict[str, Any],
    selections: list[dict[str, Any]],
) -> None:
    build = run_cmd(["lake", "build", "TableGeneration"], repo)
    if build["returncode"] != 0:
        raise ValueError(f"promoted generator does not build:\n{build['output']}")
    verify_source(repo, selections)
    evaluated = evaluate_targets(repo, selections)
    for selection, metrics in zip(selections, evaluated, strict=True):
        target = {"mode": selection["mode"], "k": selection["k"]}
        if metrics.get("policy_id") != selection["policy_id"]:
            raise ValueError(
                f"{target['mode']} k={target['k']} selected {metrics.get('policy_id')} "
                f"instead of {selection['policy_id']}"
            )
        expected = selection["metrics"]
        metrics["weighted_cost"] = weighted_cost(metrics, config["weights"])
        mismatches = [
            field for field in METRIC_FIELDS if metrics.get(field) != expected.get(field)
        ]
        if mismatches:
            raise ValueError(
                f"{target['mode']} k={target['k']} does not reproduce: "
                + ", ".join(mismatches)
            )


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--repo", default=".", help="Repository to update.")
    parser.add_argument("--results-root", required=True, help="submission-results tree.")
    parser.add_argument(
        "--leaderboard",
        default="",
        help="Leaderboard JSON; defaults below --results-root.",
    )
    parser.add_argument("--generate-only", action="store_true")
    args = parser.parse_args()

    repo = Path(args.repo).resolve()
    results_root = Path(args.results_root).resolve()
    leaderboard_path = (
        Path(args.leaderboard).resolve()
        if args.leaderboard
        else results_root / "leaderboard/results.json"
    )
    leaderboard = read_json(leaderboard_path)
    if leaderboard.get("schema_version") != 3:
        raise ValueError("leaderboard schema_version must be 3")
    config = read_json(repo / "leaderboard/config.json")
    config_targets = validate_config(config)
    selections = construct(repo, results_root, leaderboard, config_targets)
    if not args.generate_only:
        verify(repo, config, selections)
    print(f"Constructed {len(selections)} promoted target mappings.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
