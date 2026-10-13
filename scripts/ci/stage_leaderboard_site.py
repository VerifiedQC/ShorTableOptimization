#!/usr/bin/env python3
"""Stage the static leaderboard with its published data."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import shutil
from typing import Any


def read_json(path: Path) -> dict[str, Any]:
    value = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(value, dict):
        raise ValueError(f"{path} must contain a JSON object")
    return value


def stage(site: Path, results_root: Path, out: Path) -> None:
    index_path = results_root / "leaderboard/results.json"
    leaderboard = read_json(index_path)
    if leaderboard.get("schema_version") != 3:
        raise ValueError("leaderboard schema_version must be 3")

    out.mkdir(parents=True, exist_ok=True)
    # index.html is the RSA-2048 gate-count board; targets.html is the
    # per-target structural benchmark it links to. Both share site.css.
    for name in ("index.html", "targets.html", "site.css", "recursive-cost.js"):
        source = site / name
        if not source.is_file():
            raise ValueError(f"site file is missing: {name}")
        shutil.copyfile(source, out / name)
    shutil.copyfile(index_path, out / "results.json")

    policies = leaderboard.get("policies")
    if not isinstance(policies, list):
        raise ValueError("leaderboard policies must be an array")
    for policy in policies:
        if not isinstance(policy, dict) or not isinstance(policy.get("policy_id"), str):
            raise ValueError("leaderboard policy identity is invalid")
        operations_path = policy.get("operations_path")
        if operations_path is None:
            continue
        expected = f"results/policies/{policy['policy_id']}/operations.json"
        if operations_path != expected:
            raise ValueError(f"unexpected operations path for {policy['policy_id']}")
        source_path = results_root / operations_path
        if not source_path.is_file():
            raise ValueError(f"operations file does not exist: {operations_path}")
        destination = out / operations_path
        destination.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(source_path, destination)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--site", required=True)
    parser.add_argument("--results-root", required=True)
    parser.add_argument("--out", required=True)
    args = parser.parse_args()
    stage(Path(args.site), Path(args.results_root), Path(args.out))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
