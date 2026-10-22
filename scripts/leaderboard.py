#!/usr/bin/env python3
"""Build the benchmark index from a successful verifier artifact.

The index on `submission-results` is `scripts/promote.py`'s only input, and
`export_benchmark_config.py` imports `validate_config` from here.

The `generated_at` and `benchmark` fields fed the retired website and now have
no consumer. They stay: dropping them is a schema change, and `promote.py` pins
schema_version 3.
"""

from __future__ import annotations

import argparse
import datetime as dt
import json
from pathlib import Path
import re
from typing import Any


VALID_TARGET_MODES = {"PhaseProduct", "PhaseTripleProduct"}
REQUIRED_METRICS = {
    "arithmetic_operation_count",
    "parallel_phase_product_layer_count",
    "phase_product_count",
    "total_operation_count",
    "point_count",
}
OPERATION_PATTERNS = (
    (re.compile(r"\(shiftL, reg=(\d+), by=(\d+)\)"), "shiftL"),
    (re.compile(r"\(shiftR, reg=(\d+), by=(\d+)\)"), "shiftR"),
    (re.compile(r"\(negate, reg=(\d+)\)"), "negate"),
    (
        re.compile(
            r"\(addScaled, dst=(\d+), src=(\d+), sign=([+-])1, shift=(\d+)\)"
        ),
        "addScaled",
    ),
    (re.compile(r"\(phaseProduct, reg=(\d+)\)"), "phaseProduct"),
)
OPERATION_FORMAT = {
    "shiftL": ["register", "amount"],
    "shiftR": ["register", "amount"],
    "negate": ["register"],
    "addScaled": ["destination", "source", "source_sign", "shift"],
    "phaseProduct": ["register"],
}


def utc_now() -> str:
    return dt.datetime.now(dt.timezone.utc).isoformat().replace("+00:00", "Z")


def read_json(path: Path) -> dict[str, Any]:
    value = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(value, dict):
        raise ValueError(f"{path} must contain a JSON object")
    return value


def read_existing(path: Path) -> dict[str, Any] | None:
    if not path.is_file() or path.stat().st_size == 0:
        return None
    return read_json(path)


def validate_target(raw: Any, source: str) -> dict[str, Any]:
    if not isinstance(raw, dict):
        raise ValueError(f"{source} must be an object")
    mode = raw.get("mode")
    k = raw.get("k")
    if mode not in VALID_TARGET_MODES:
        raise ValueError(f"{source}.mode must be PhaseProduct or PhaseTripleProduct")
    if not isinstance(k, int) or isinstance(k, bool) or k < 2:
        raise ValueError(f"{source}.k must be an integer at least 2")
    return {"mode": mode, "k": k}


def validate_targets(raw: Any, source: str) -> list[dict[str, Any]]:
    if not isinstance(raw, list) or not raw:
        raise ValueError(f"{source} must be a nonempty array")
    targets: list[dict[str, Any]] = []
    seen: set[tuple[str, int]] = set()
    for index, item in enumerate(raw):
        target = validate_target(item, f"{source}[{index}]")
        key = (target["mode"], target["k"])
        if key in seen:
            raise ValueError(f"duplicate target {target['mode']} k={target['k']}")
        seen.add(key)
        targets.append(target)
    return targets


def validate_config(config: dict[str, Any]) -> list[dict[str, Any]]:
    if config.get("schema_version") != 2:
        raise ValueError("config schema_version must be 2")
    matrix = config.get("target_matrix")
    if not isinstance(matrix, dict):
        raise ValueError("config target_matrix must be an object")
    modes = matrix.get("modes")
    if not isinstance(modes, list) or not modes:
        raise ValueError("config target_matrix.modes must be a nonempty array")
    if len(set(modes)) != len(modes) or any(
        mode not in VALID_TARGET_MODES for mode in modes
    ):
        raise ValueError("config target_matrix.modes must contain unique valid modes")
    k_min = matrix.get("k_min")
    k_max = matrix.get("k_max")
    if (
        not isinstance(k_min, int)
        or isinstance(k_min, bool)
        or not isinstance(k_max, int)
        or isinstance(k_max, bool)
        or k_min < 2
        or k_max < k_min
    ):
        raise ValueError(
            "config target_matrix k_min and k_max must define a range from k >= 2"
        )
    targets = [
        {"mode": mode, "k": k}
        for k in range(k_min, k_max + 1)
        for mode in modes
    ]
    weights = config.get("weights")
    if not isinstance(weights, dict):
        raise ValueError("config weights must be an object")
    for key in ("arithmetic_operation_count", "parallel_phase_product_layer_count"):
        if (
            not isinstance(weights.get(key), int)
            or isinstance(weights[key], bool)
            or weights[key] < 0
        ):
            raise ValueError(f"config weights.{key} must be a nonnegative integer")
    return targets


def int_metric(metrics: dict[str, Any], key: str) -> int:
    value = metrics.get(key)
    if not isinstance(value, int):
        raise ValueError(f"metric {key} must be an integer")
    return value


def validate_metric_target(metrics: dict[str, Any], expected: dict[str, Any]) -> None:
    if metrics.get("mode") != expected["mode"] or metrics.get("k") != expected["k"]:
        raise ValueError(
            f"metric target {metrics.get('mode')} k={metrics.get('k')} "
            f"does not match expected {expected['mode']} k={expected['k']}"
        )
    missing = sorted(REQUIRED_METRICS - set(metrics))
    if missing:
        raise ValueError("submission result is missing metrics: " + ", ".join(missing))
    for key in REQUIRED_METRICS:
        int_metric(metrics, key)


def validate_result(
    result: dict[str, Any],
    config_targets: list[dict[str, Any]],
) -> list[dict[str, Any]]:
    if result.get("schema_version") != 1:
        raise ValueError("submission result schema_version must be 1")
    if result.get("challenge") != "table-generation":
        raise ValueError("submission result challenge must be table-generation")
    if result.get("status") != "success":
        raise ValueError("submission result status must be success")

    target = result.get("target")
    if not isinstance(target, dict) or not target.get("configured"):
        raise ValueError("submission result must include configured targets")
    result_targets = validate_targets(target.get("targets"), "result.target.targets")
    if result_targets != config_targets:
        raise ValueError("submission result targets do not match leaderboard config")

    metrics = result.get("metrics")
    if not isinstance(metrics, dict):
        raise ValueError("submission result metrics must be an object")
    metric_targets = metrics.get("targets")
    if not isinstance(metric_targets, list) or not metric_targets:
        raise ValueError("submission result must contain at least one handled target")
    expected_by_key = {(item["mode"], item["k"]): item for item in config_targets}
    seen: set[tuple[str, int]] = set()
    for metric in metric_targets:
        if not isinstance(metric, dict):
            raise ValueError("each target metric must be an object")
        key = (metric.get("mode"), metric.get("k"))
        expected = expected_by_key.get(key)
        if expected is None:
            raise ValueError(f"metric target {key} is not configured")
        if key in seen:
            raise ValueError(f"duplicate metric target {key}")
        seen.add(key)
        validate_metric_target(metric, expected)
    target_order = {
        (target["mode"], target["k"]): index
        for index, target in enumerate(config_targets)
    }
    return sorted(
        metric_targets,
        key=lambda item: target_order[(item["mode"], item["k"])],
    )


def weighted_cost(metrics: dict[str, Any], weights: dict[str, int]) -> int:
    return (
        weights["arithmetic_operation_count"] * metrics["arithmetic_operation_count"]
        + weights["parallel_phase_product_layer_count"]
        * metrics["parallel_phase_product_layer_count"]
    )


def parse_point_list(raw: Any, field: str) -> list[str]:
    if not isinstance(raw, str) or not raw.startswith("[") or not raw.endswith("]"):
        raise ValueError(f"metric {field} must be a rendered point list")
    inner = raw[1:-1]
    return [] if not inner else inner.split(", ")


def parse_operations(raw: Any) -> list[list[str | int]]:
    if not isinstance(raw, str) or not raw.startswith("[") or not raw.endswith("]"):
        raise ValueError("metric program must be a rendered operation list")
    if raw == "[]":
        return []
    if not raw.startswith("[(") or not raw.endswith(")]"):
        raise ValueError("metric program has an invalid operation list")

    rendered = [f"({item})" for item in raw[2:-2].split("), (")]
    operations: list[list[str | int]] = []
    for operation in rendered:
        for pattern, name in OPERATION_PATTERNS:
            match = pattern.fullmatch(operation)
            if match is None:
                continue
            values: list[str | int] = [name]
            for value in match.groups():
                if value == "+":
                    values.append(1)
                elif value == "-":
                    values.append(-1)
                else:
                    values.append(int(value))
            operations.append(values)
            break
        else:
            raise ValueError(f"metric program contains an unknown operation: {operation}")
    return operations


def target_entry(metrics: dict[str, Any], weights: dict[str, int]) -> dict[str, Any]:
    return {
        "mode": metrics["mode"],
        "k": metrics["k"],
        "weighted_cost": weighted_cost(metrics, weights),
        "arithmetic_operation_count": metrics["arithmetic_operation_count"],
        "parallel_phase_product_layer_count": metrics[
            "parallel_phase_product_layer_count"
        ],
        "phase_product_count": metrics["phase_product_count"],
        "total_operation_count": metrics["total_operation_count"],
        "point_count": metrics["point_count"],
    }


def policy_identity(metadata: dict[str, Any]) -> str:
    head_sha = str(metadata.get("head_sha") or "").strip().lower()
    if re.fullmatch(r"[0-9a-f]{40}", head_sha):
        return head_sha
    run_id = str(metadata.get("run_id") or "").strip()
    if run_id.isdigit():
        return f"run-{run_id}"
    raise ValueError("submission result metadata must identify a policy commit or run")


def build_operations_result(
    result: dict[str, Any], metric_targets: list[dict[str, Any]]
) -> dict[str, Any]:
    targets = []
    for metrics in metric_targets:
        operations = parse_operations(metrics.get("program"))
        generated_points = parse_point_list(metrics.get("points"), "points")
        point_order = parse_point_list(metrics.get("point_order"), "point_order")
        if len(operations) != int_metric(metrics, "total_operation_count"):
            raise ValueError("rendered operation count does not match total_operation_count")
        if sum(operation[0] == "phaseProduct" for operation in operations) != int_metric(
            metrics, "phase_product_count"
        ):
            raise ValueError("rendered phase-product count does not match metrics")
        if len(generated_points) != int_metric(metrics, "point_count"):
            raise ValueError("rendered generated-point count does not match metrics")
        if len(point_order) != int_metric(metrics, "point_count"):
            raise ValueError("rendered point-order count does not match metrics")
        targets.append(
            {
                "mode": metrics["mode"],
                "k": metrics["k"],
                "generated_points": generated_points,
                "point_order": point_order,
                "operations": operations,
            }
        )
    return {
        "schema_version": 1,
        "policy_id": policy_identity(result.get("metadata") or {}),
        "operation_format": OPERATION_FORMAT,
        "targets": targets,
    }


def build_policy(
    result: dict[str, Any],
    config: dict[str, Any],
    metric_targets: list[dict[str, Any]],
) -> dict[str, Any]:
    metadata = result.get("metadata") or {}
    weights = config["weights"]
    policy_id = policy_identity(metadata)

    source = {
        field: metadata[field]
        for field in (
            "repository",
            "pr_number",
            "head_ref",
            "run_id",
            "run_attempt",
            "created_at",
        )
        if metadata.get(field) not in (None, "")
    }
    source["archive_path"] = f"results/policies/{policy_id}/source.zip"

    return {
        "policy_id": policy_id,
        "operations_path": f"results/policies/{policy_id}/operations.json",
        "source": source,
        "results": [target_entry(metrics, weights) for metrics in metric_targets],
    }


def normalize_policy(
    policy: dict[str, Any],
    config_targets: list[dict[str, Any]],
    weights: dict[str, int],
) -> dict[str, Any] | None:
    policy_id = policy.get("policy_id")
    source = policy.get("source")
    old_results = policy.get("results")
    if not isinstance(policy_id, str) or not isinstance(source, dict):
        raise ValueError("existing policy identity is invalid")
    if not isinstance(old_results, list):
        raise ValueError("existing policy results must be an array")

    expected_by_key = {(item["mode"], item["k"]): item for item in config_targets}
    results = []
    seen: set[tuple[str, int]] = set()
    for metrics in old_results:
        if not isinstance(metrics, dict):
            raise ValueError("existing policy target result must be an object")
        key = (metrics.get("mode"), metrics.get("k"))
        expected = expected_by_key.get(key)
        if expected is None:
            continue
        if key in seen:
            raise ValueError(f"duplicate existing policy target {key}")
        seen.add(key)
        validate_metric_target(metrics, expected)
        results.append(target_entry(metrics, weights))
    if not results:
        return None
    normalized = {
        "policy_id": policy_id,
        "source": source,
        "results": results,
    }
    operations_path = policy.get("operations_path")
    if isinstance(operations_path, str):
        normalized["operations_path"] = operations_path
    return normalized


def sort_policies(policies: list[dict[str, Any]]) -> list[dict[str, Any]]:
    return sorted(
        policies,
        key=lambda policy: (
            policy["source"].get("created_at") or "",
            policy["policy_id"],
        ),
    )


def build_champions(
    policies: list[dict[str, Any]],
    config_targets: list[dict[str, Any]],
) -> list[dict[str, Any]]:
    champions = []
    for target in config_targets:
        candidates = []
        for policy in policies:
            for metrics in policy["results"]:
                if (
                    metrics["mode"] == target["mode"]
                    and metrics["k"] == target["k"]
                ):
                    candidates.append((policy, metrics))
                    break
        if not candidates:
            continue
        best_cost = min(metrics["weighted_cost"] for _, metrics in candidates)
        policy_ids = sorted(
            policy["policy_id"]
            for policy, metrics in candidates
            if metrics["weighted_cost"] == best_cost
        )
        champions.append(
            {
                "mode": target["mode"],
                "k": target["k"],
                "policy_ids": policy_ids,
            }
        )
    return champions


def update_leaderboard(
    existing: dict[str, Any] | None,
    result: dict[str, Any],
    config: dict[str, Any],
    config_targets: list[dict[str, Any]],
    metric_targets: list[dict[str, Any]],
) -> dict[str, Any]:
    policy = build_policy(result, config, metric_targets)
    policies_by_id: dict[str, dict[str, Any]] = {}
    if existing:
        if existing.get("schema_version") != 3:
            raise ValueError("existing leaderboard schema_version must be 3")
        if existing.get("challenge") != "table-generation":
            raise ValueError("existing leaderboard challenge must be table-generation")
        for old_policy in existing.get("policies", []):
            if not isinstance(old_policy, dict):
                raise ValueError("existing leaderboard policy must be an object")
            normalized = normalize_policy(old_policy, config_targets, config["weights"])
            if normalized:
                policies_by_id[normalized["policy_id"]] = normalized

    policies_by_id[policy["policy_id"]] = policy
    policies = sort_policies(list(policies_by_id.values()))
    return {
        "schema_version": 3,
        "challenge": "table-generation",
        "generated_at": utc_now(),
        "benchmark": {
            "target_matrix": config["target_matrix"],
            "weights": config["weights"],
        },
        "policies": policies,
        "champions": build_champions(policies, config_targets),
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--artifact", required=True, help="Verifier JSON artifact.")
    parser.add_argument("--config", default="leaderboard/config.json", help="Leaderboard config.")
    parser.add_argument("--existing", default="", help="Existing leaderboard JSON, if present.")
    parser.add_argument("--out", required=True, help="Output leaderboard JSON.")
    parser.add_argument("--operations-out", default="", help="Detailed operations JSON.")
    args = parser.parse_args()

    config = read_json(Path(args.config))
    config_targets = validate_config(config)
    result = read_json(Path(args.artifact))
    metric_targets = validate_result(result, config_targets)

    existing = read_existing(Path(args.existing)) if args.existing else None
    leaderboard = update_leaderboard(
        existing,
        result,
        config,
        config_targets,
        metric_targets,
    )
    out = Path(args.out)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(
        json.dumps(leaderboard, separators=(",", ":"), sort_keys=True) + "\n",
        encoding="utf-8",
    )
    if args.operations_out:
        operations_out = Path(args.operations_out)
        operations_out.parent.mkdir(parents=True, exist_ok=True)
        operations_out.write_text(
            json.dumps(
                build_operations_result(result, metric_targets),
                separators=(",", ":"),
                sort_keys=True,
            )
            + "\n",
            encoding="utf-8",
        )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
