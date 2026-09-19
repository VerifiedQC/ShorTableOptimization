#!/usr/bin/env python3
"""Verify a table-generation submission and emit CI artifacts."""

from __future__ import annotations

import argparse
import datetime as dt
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile
import zipfile
from typing import Any


CHALLENGE = "table-generation"
TARGET_MODULE = "TableGeneration"
SCORE_FIELDS = [
    "arithmetic_operation_count",
    "parallel_phase_product_layer_count",
]
BENCHMARK_METRIC_FIELDS = [
    "arithmetic_operation_count",
    "parallel_phase_product_layer_count",
    "phase_product_count",
    "total_operation_count",
    "point_count",
]
VALID_TARGET_MODES = {"PhaseProduct", "PhaseTripleProduct"}
SUBMISSION_DIR = Path("TableGeneration/Submission")
DEFS_FILE = SUBMISSION_DIR / "Defs.lean"
CORRECTNESS_FILE = SUBMISSION_DIR / "Correctness.lean"
POLICY_FILE = SUBMISSION_DIR / "Policy.lean"
SUBMISSION_FILES = {str(DEFS_FILE), str(CORRECTNESS_FILE), str(POLICY_FILE)}
ALLOWED_CHANGED_FILES = set(SUBMISSION_FILES)
SUBMISSION_PREFIX = "TableGeneration/Submission/"
PROTECTED_FILES = {
    "TableGeneration.lean",
    "TableGeneration/Basic.lean",
    "TableGeneration/Baseline.lean",
    "TableGeneration/Language.lean",
    "TableGeneration/Spec.lean",
    "TableGeneration/Metrics.lean",
    "TableGeneration/Policy.lean",
    "TableGeneration/BestKnown.lean",
    "TableGeneration/Submission.lean",
    "leaderboard/config.json",
    "lakefile.lean",
    "lean-toolchain",
}

EXPECTED_THEOREMS = {
    "generatedPoints_valid": (
        "theorem generatedPoints_valid (mode : ProductMode) (k : Nat) "
        "(_ : k >= 2) (_hhandles : submissionHandles mode k = true) "
        ": ValidPointList mode k "
        "(generatedPoints mode k) := by"
    ),
    "generate_ProgConsumesPtsSafe": (
        "theorem generate_ProgConsumesPtsSafe (mode : ProductMode) "
        "(k : Nat) (hk : k >= 2) "
        "(_hhandles : submissionHandles mode k = true) "
        ": ValidPointOrder (generatedPoints mode k) "
        "(generatePointsInOrder mode k hk) /\\ ProgConsumesPtsSafe "
        "(positive_of_ge_two hk) State.start_state (generate mode k hk) "
        "(generatePointsInOrder mode k hk) := by"
    ),
}

EXPECTED_WRAPPER_DEFS = {
    "generatedPoints": (
        "def generatedPoints (mode : ProductMode) (k : Nat) : List Point := "
        "Submission.Policy.implementation.generatedPoints mode k"
    ),
    "submissionHandles": (
        "def submissionHandles (mode : ProductMode) (k : Nat) : Bool := "
        "Submission.Policy.implementation.handles mode k"
    ),
    "submissionGeneratePointsInOrder": (
        "def submissionGeneratePointsInOrder "
        "(mode : ProductMode) (k : Nat) (hk : k >= 2) : List Point := "
        "Submission.Policy.implementation.generatePointsInOrder mode k hk"
    ),
    "submissionGenerate": (
        "def submissionGenerate "
        "(mode : ProductMode) (k : Nat) (hk : k >= 2) : Prog k := "
        "Submission.Policy.implementation.generate mode k hk"
    ),
    "generatePointsInOrder": (
        "def generatePointsInOrder "
        "(mode : ProductMode) (k : Nat) (hk : k >= 2) : List Point := "
        "if submissionHandles mode k then "
        "submissionGeneratePointsInOrder mode k hk "
        "else "
        "bestKnownGeneratePointsInOrder mode k hk"
    ),
    "generate": (
        "def generate (mode : ProductMode) (k : Nat) (hk : k >= 2) : Prog k := "
        "if submissionHandles mode k then "
        "submissionGenerate mode k hk "
        "else "
        "bestKnownGenerate mode k hk"
    ),
}

BANNED_PATTERNS = {
    "sorry/admit": re.compile(r"\bsorry\b|\bsorryAx\b|\badmit\b"),
    "axiom/constant": re.compile(r"\baxiom\b|\bconstant\b"),
    "unsafe": re.compile(r"\bunsafe\b"),
    "compile-time execution": re.compile(
        r"(^|\s)#eval\b|^\s*run_cmd\b|^\s*initialize\b|^\s*elab\b|"
        r"^\s*syntax\b|^\s*macro\b",
        re.MULTILINE,
    ),
    "external implementation hook": re.compile(r"\b(?:extern|implemented_by)\b"),
    "non-kernel computation": re.compile(r"\bnative_decide\b"),
}

ALLOWED_AXIOMS: set[str] = {"propext"}


def utc_now() -> str:
    return dt.datetime.now(dt.timezone.utc).isoformat().replace("+00:00", "Z")


# Keep every subprocess timeout strictly below the CI job's wall clock
# (45 minutes for the submission workflow). If a subprocess outlives the job,
# the run dies as an opaque cancellation instead of a verifier error naming the
# step that hung, which is much harder for a submitter to act on.
DEFAULT_CMD_TIMEOUT = 1800


def run_cmd(
    args: list[str],
    cwd: Path,
    timeout: int = DEFAULT_CMD_TIMEOUT,
    env: dict[str, str] | None = None,
) -> dict[str, Any]:
    try:
        completed = subprocess.run(
            args,
            cwd=cwd,
            env=env,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            timeout=timeout,
            check=False,
        )
        return {
            "args": args,
            "returncode": completed.returncode,
            "output": completed.stdout,
        }
    except subprocess.TimeoutExpired as exc:
        output = exc.stdout or ""
        if isinstance(output, bytes):
            output = output.decode("utf-8", errors="replace")
        return {
            "args": args,
            "returncode": 124,
            "output": output + f"\nTimed out after {timeout} seconds.\n",
        }


def check_result(name: str, ok: bool, details: str) -> dict[str, str]:
    return {
        "name": name,
        "status": "success" if ok else "failure",
        "details": details,
    }


def skipped_result(name: str, details: str) -> dict[str, str]:
    return {"name": name, "status": "skipped", "details": details}


def validate_target(raw: Any, source: str) -> tuple[dict[str, Any] | None, str | None]:
    if not isinstance(raw, dict):
        return None, f"{source} must be an object."
    mode = str(raw.get("mode", "")).strip()
    if mode not in VALID_TARGET_MODES:
        return None, f"{source}.mode must be PhaseProduct or PhaseTripleProduct."
    k_raw = raw.get("k")
    if not isinstance(k_raw, int):
        return None, f"{source}.k must be an integer."
    if k_raw < 2:
        return None, f"{source}.k must be at least 2."
    return {"mode": mode, "k": k_raw}, None


def read_target_config() -> tuple[list[dict[str, Any]] | None, str | None]:
    targets_raw = os.getenv("TABLE_GEN_TARGETS", "").strip()
    if targets_raw:
        try:
            parsed = json.loads(targets_raw)
        except json.JSONDecodeError as exc:
            return None, f"TABLE_GEN_TARGETS must be JSON: {exc}"
        if not isinstance(parsed, list):
            return None, "TABLE_GEN_TARGETS must be a JSON array."
        if not parsed:
            return None, None
        targets: list[dict[str, Any]] = []
        seen: set[tuple[str, int]] = set()
        for index, raw in enumerate(parsed):
            target, error = validate_target(raw, f"TABLE_GEN_TARGETS[{index}]")
            if error:
                return None, error
            assert target is not None
            key = (target["mode"], target["k"])
            if key in seen:
                return None, f"Duplicate target {target['mode']} k={target['k']}."
            seen.add(key)
            targets.append(target)
        return targets, None

    mode = os.getenv("TABLE_GEN_TARGET_MODE", "").strip()
    k_raw = os.getenv("TABLE_GEN_TARGET_K", "").strip()
    if not mode and not k_raw:
        config_path = Path(__file__).resolve().parents[1] / "leaderboard" / "config.json"
        try:
            config = json.loads(config_path.read_text(encoding="utf-8"))
            matrix = config["target_matrix"]
            modes = matrix["modes"]
            k_min = matrix["k_min"]
            k_max = matrix["k_max"]
        except (OSError, json.JSONDecodeError, KeyError, TypeError) as exc:
            return None, f"Could not read benchmark targets from {config_path}: {exc}"
        if (
            not isinstance(modes, list)
            or not modes
            or any(item not in VALID_TARGET_MODES for item in modes)
            or len(set(modes)) != len(modes)
            or not isinstance(k_min, int)
            or isinstance(k_min, bool)
            or not isinstance(k_max, int)
            or isinstance(k_max, bool)
            or k_min < 2
            or k_max < k_min
        ):
            return None, f"Benchmark target matrix in {config_path} is invalid."
        return [
            {"mode": item, "k": k}
            for k in range(k_min, k_max + 1)
            for item in modes
        ], None
    try:
        k = int(k_raw)
    except ValueError:
        return None, "TABLE_GEN_TARGET_K must be an integer."
    target, error = validate_target({"mode": mode, "k": k}, "TABLE_GEN_TARGET")
    if error:
        return None, error
    assert target is not None
    return [target], None


def validate_score_weights(
    raw: Any,
    source: str,
) -> tuple[dict[str, int] | None, str | None]:
    if not isinstance(raw, dict):
        return None, f"{source} must be a JSON object."
    weights: dict[str, int] = {}
    for field in SCORE_FIELDS:
        value = raw.get(field)
        if not isinstance(value, int) or isinstance(value, bool) or value < 0:
            return None, f"{source}.{field} must be a nonnegative integer."
        weights[field] = value
    return weights, None


def read_score_weights() -> tuple[dict[str, int] | None, str | None]:
    weights_raw = os.getenv("TABLE_GEN_SCORE_WEIGHTS", "").strip()
    if weights_raw:
        try:
            parsed = json.loads(weights_raw)
        except json.JSONDecodeError as exc:
            return None, f"TABLE_GEN_SCORE_WEIGHTS must be JSON: {exc}"
        return validate_score_weights(parsed, "TABLE_GEN_SCORE_WEIGHTS")

    config_path = Path(__file__).resolve().parents[1] / "leaderboard" / "config.json"
    try:
        config = json.loads(config_path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        return None, f"Could not read benchmark weights from {config_path}: {exc}"
    return validate_score_weights(config.get("weights"), "config.weights")


def score_formula(weights: dict[str, int]) -> str:
    return (
        "weighted_cost = "
        f"{weights['arithmetic_operation_count']} * arithmetic_operation_count + "
        f"{weights['parallel_phase_product_layer_count']} * "
        "parallel_phase_product_layer_count"
    )


def benchmark_metadata(
    weights: dict[str, int] | None,
    error: str | None = None,
) -> dict[str, Any]:
    if weights is None:
        metadata: dict[str, Any] = {"configured": False}
        if error:
            metadata["error"] = error
        return metadata
    return {
        "configured": True,
        "weights": weights,
        "formula": score_formula(weights),
    }


def target_metadata(
    targets: list[dict[str, Any]] | None,
    error: str | None = None,
) -> dict[str, Any]:
    if targets is None:
        metadata: dict[str, Any] = {"configured": False, "score": []}
        if error:
            metadata["error"] = error
        return metadata
    return {
        "configured": True,
        "targets": [{"mode": target["mode"], "k": target["k"]} for target in targets],
        "score": SCORE_FIELDS,
    }


def normalize_decl(text: str) -> str:
    return re.sub(r"\s+", " ", text).strip()


def strip_lean_comments(text: str) -> str:
    output: list[str] = []
    i = 0
    depth = 0
    n = len(text)
    while i < n:
        # At top level, a string literal is data, not code: copy it verbatim so
        # that `/-` / `-/` / `--` inside a string are not mistaken for comment
        # delimiters. Without this, a token bracketed by "/-" ... "-/" string
        # literals is silently deleted from the scan while Lean still compiles it.
        if depth == 0 and text[i] == '"':
            output.append('"')
            i += 1
            while i < n:
                c = text[i]
                if c == "\\" and i + 1 < n:
                    output.append(text[i:i + 2])
                    i += 2
                    continue
                output.append(c)
                i += 1
                if c == '"':
                    break
            continue
        if depth == 0 and text.startswith("--", i):
            while i < n and text[i] != "\n":
                i += 1
            if i < n:
                output.append("\n")
                i += 1
            continue
        if text.startswith("/-", i):
            depth += 1
            i += 2
            continue
        if depth > 0 and text.startswith("-/", i):
            depth -= 1
            i += 2
            continue
        if depth == 0:
            output.append(text[i])
        elif text[i] == "\n":
            output.append("\n")
        i += 1
    return "".join(output)


def extract_theorem_decl(text: str, theorem_name: str) -> tuple[int, str | None]:
    count = len(re.findall(rf"\btheorem\s+{re.escape(theorem_name)}\b", text))
    match = re.search(
        rf"\btheorem\s+{re.escape(theorem_name)}\b.*?:=\s*by",
        text,
        flags=re.DOTALL,
    )
    return count, match.group(0) if match else None


def extract_def_decl(text: str, def_name: str) -> tuple[int, str | None]:
    count = len(re.findall(rf"\bdef\s+{re.escape(def_name)}\b", text))
    match = re.search(
        rf"\bdef\s+{re.escape(def_name)}\b.*?"
        rf"(?=\n\s*(?:def|theorem|section|end|namespace|open)\b|\Z)",
        text,
        flags=re.DOTALL,
    )
    return count, match.group(0) if match else None


def get_changed_files(repo: Path) -> tuple[bool, list[str], str]:
    base = os.getenv("TABLE_GEN_BASE_SHA", "").strip()
    head = os.getenv("TABLE_GEN_HEAD_SHA", "").strip() or "HEAD"
    base_repo = os.getenv("TABLE_GEN_BASE_REPOSITORY", "").strip()
    event_name = os.getenv("GITHUB_EVENT_NAME", "").strip()

    if not base:
        if event_name == "pull_request":
            return False, [], "TABLE_GEN_BASE_SHA is missing for pull_request."
        return True, [], "No PR base SHA was provided; changed-file check skipped."

    has_base = run_cmd(["git", "cat-file", "-e", f"{base}^{{commit}}"], repo, 60)
    if has_base["returncode"] != 0:
        fetch_origin = run_cmd(["git", "fetch", "--no-tags", "--depth=1", "origin", base], repo, 300)
        if fetch_origin["returncode"] != 0 and base_repo:
            run_cmd(
                [
                    "git",
                    "fetch",
                    "--no-tags",
                    "--depth=1",
                    f"https://github.com/{base_repo}.git",
                    base,
                ],
                repo,
                300,
            )

    has_base = run_cmd(["git", "cat-file", "-e", f"{base}^{{commit}}"], repo, 60)
    if has_base["returncode"] != 0:
        return False, [], f"Could not fetch PR base commit {base}."

    diff = run_cmd(["git", "diff", "--name-only", f"{base}...{head}"], repo, 300)
    if diff["returncode"] != 0:
        return False, [], diff["output"].strip()

    files = [line.strip() for line in diff["output"].splitlines() if line.strip()]
    return True, files, f"Compared {base}...{head}."


def is_allowed_changed_file(path: str) -> bool:
    return path in ALLOWED_CHANGED_FILES or (
        path.startswith(SUBMISSION_PREFIX) and path.endswith(".lean")
    )


def verify_required_files(repo: Path) -> dict[str, str]:
    required = sorted(SUBMISSION_FILES | PROTECTED_FILES)
    missing = [path for path in required if not (repo / path).is_file()]
    return check_result(
        "required files exist",
        not missing,
        "All required files are present." if not missing else "Missing: " + ", ".join(missing),
    )


def verify_changed_files(repo: Path) -> dict[str, str]:
    ok, changed, details = get_changed_files(repo)
    if not ok:
        return check_result("changed files are allowed", False, details)
    if not changed:
        return skipped_result("changed files are allowed", details)
    disallowed = sorted(path for path in changed if not is_allowed_changed_file(path))
    if disallowed:
        return check_result(
            "changed files are allowed",
            False,
            "Only submission Lean files may change. Implement Policy.lean and place "
            "related helpers under TableGeneration/Submission/Policy/. Disallowed: "
            + ", ".join(disallowed),
        )
    return check_result(
        "changed files are allowed",
        True,
        "Changed files: " + ", ".join(sorted(changed)),
    )


def verify_theorem_statements(repo: Path) -> dict[str, str]:
    text = strip_lean_comments((repo / CORRECTNESS_FILE).read_text(encoding="utf-8"))
    failures: list[str] = []
    for theorem_name, expected in EXPECTED_THEOREMS.items():
        count, actual = extract_theorem_decl(text, theorem_name)
        if count != 1:
            failures.append(f"{theorem_name} appears {count} times")
            continue
        if actual is None:
            failures.append(f"{theorem_name} declaration could not be parsed")
            continue
        if normalize_decl(actual) != normalize_decl(expected):
            failures.append(f"{theorem_name} statement differs from the template")

    return check_result(
        "theorem statements are preserved",
        not failures,
        "The two theorem statements match the template."
        if not failures
        else "; ".join(failures),
    )


def verify_wrapper_definitions(repo: Path) -> dict[str, str]:
    text = strip_lean_comments((repo / DEFS_FILE).read_text(encoding="utf-8"))
    failures: list[str] = []
    for def_name, expected in EXPECTED_WRAPPER_DEFS.items():
        count, actual = extract_def_decl(text, def_name)
        if count != 1:
            failures.append(f"{def_name} appears {count} times")
            continue
        if actual is None:
            failures.append(f"{def_name} declaration could not be parsed")
            continue
        if normalize_decl(actual) != normalize_decl(expected):
            failures.append(f"{def_name} differs from the template")

    return check_result(
        "wrapper definitions are preserved",
        not failures,
        "The submission adapters and generate wrappers match the template."
        if not failures
        else "; ".join(failures),
    )


def verify_no_banned_tokens(repo: Path) -> dict[str, str]:
    lean_files = sorted((repo / SUBMISSION_DIR).glob("**/*.lean"))
    failures: list[str] = []
    for path in lean_files:
        stripped = strip_lean_comments(path.read_text(encoding="utf-8"))
        for label, pattern in BANNED_PATTERNS.items():
            for match in pattern.finditer(stripped):
                line = stripped.count("\n", 0, match.start()) + 1
                rel = path.relative_to(repo)
                failures.append(f"{rel}:{line}: banned {label}")

    return check_result(
        "no banned proof shortcuts",
        not failures,
        "No banned proof shortcuts, external hooks, or execution commands were found."
        if not failures
        else "; ".join(failures[:20]),
    )


def preflight_checks(repo: Path) -> list[dict[str, str]]:
    checks = [
        verify_required_files(repo),
        verify_changed_files(repo),
    ]
    if any(check["status"] == "failure" for check in checks):
        checks.append(
            skipped_result(
                "theorem statements are preserved",
                "Skipped because required files or changed-file checks failed.",
            )
        )
        checks.append(
            skipped_result(
                "wrapper definitions are preserved",
                "Skipped because required files or changed-file checks failed.",
            )
        )
        checks.append(
            skipped_result(
                "no banned proof shortcuts",
                "Skipped because required files or changed-file checks failed.",
            )
        )
        return checks

    checks.append(verify_theorem_statements(repo))
    checks.append(verify_wrapper_definitions(repo))
    checks.append(verify_no_banned_tokens(repo))
    return checks


def checks_passed(checks: list[dict[str, str]]) -> bool:
    return all(check["status"] == "success" for check in checks if check["status"] != "skipped")


def write_text(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")


def verify_build(repo: Path, out_dir: Path) -> dict[str, str]:
    build = run_cmd(["lake", "build", TARGET_MODULE], repo)
    write_text(out_dir / "table-generation-build.log", build["output"])
    return check_result(
        "lean build",
        build["returncode"] == 0,
        "Build completed successfully."
        if build["returncode"] == 0
        else f"Build failed with exit code {build['returncode']}. See build log.",
    )


def parse_axiom_names(output: str) -> set[str]:
    names: set[str] = set()
    for match in re.finditer(r"depends on axioms:\s*\[([^\]]*)\]", output):
        for raw in match.group(1).split(","):
            name = raw.strip().strip("'\"")
            if name:
                names.add(name)
    return names


def verify_axiom_dependencies(repo: Path, out_dir: Path) -> dict[str, str]:
    source = "\n".join(
        [
            "import TableGeneration.Submission.Correctness",
            "",
            "#print axioms TableGeneration.generatedPoints_valid",
            "#print axioms TableGeneration.generate_ProgConsumesPtsSafe",
            "",
        ]
    )
    with tempfile.TemporaryDirectory() as tmp:
        check_file = Path(tmp) / "CheckAxioms.lean"
        check_file.write_text(source, encoding="utf-8")
        result = run_cmd(["lake", "env", "lean", str(check_file)], repo, 600)

    write_text(out_dir / "table-generation-axioms.log", result["output"])
    if result["returncode"] != 0:
        return check_result(
            "axiom dependencies",
            False,
            f"Could not inspect theorem axioms; lean exited {result['returncode']}.",
        )

    output = result["output"]
    if "sorryAx" in output:
        return check_result("axiom dependencies", False, "A theorem depends on sorryAx.")

    found = parse_axiom_names(output)
    unexpected = sorted(found - ALLOWED_AXIOMS)
    if unexpected:
        return check_result(
            "axiom dependencies",
            False,
            "Unexpected theorem axioms: " + ", ".join(unexpected),
        )

    detail = (
        "No axioms were reported."
        if not found
        else "Only allowed axioms were reported: " + ", ".join(sorted(found))
    )
    return check_result("axiom dependencies", True, detail)


def parse_named_block(output: str, begin: str, end: str) -> dict[str, str]:
    values: dict[str, str] = {}
    in_block = False
    for line in output.splitlines():
        if line.strip() == begin:
            in_block = True
            continue
        if line.strip() == end:
            break
        if in_block and "=" in line:
            key, value = line.split("=", 1)
            values[key.strip()] = value.strip()
    return values


def parse_metric_output(
    output: str,
    begin: str = "TABLE_GENERATION_METRICS_BEGIN",
    end: str = "TABLE_GENERATION_METRICS_END",
) -> dict[str, str]:
    return parse_named_block(output, begin, end)


def collect_handled_targets(
    repo: Path,
    out_dir: Path,
    targets: list[dict[str, Any]],
) -> tuple[list[dict[str, Any]], dict[str, str]]:
    source_lines = [
        "import TableGeneration.Submission.Defs",
        "",
        "open TableGeneration",
        "",
        '#eval IO.println "TABLE_GENERATION_HANDLES_BEGIN"',
    ]
    for target in targets:
        mode = target["mode"]
        k = target["k"]
        source_lines.append(
            f'#eval IO.println ("{mode}:{k}=" ++ '
            f"toString (submissionHandles .{mode} {k}))"
        )
    source_lines.extend(['#eval IO.println "TABLE_GENERATION_HANDLES_END"', ""])

    with tempfile.TemporaryDirectory() as tmp:
        handles_file = Path(tmp) / "CollectHandles.lean"
        handles_file.write_text("\n".join(source_lines), encoding="utf-8")
        result = run_cmd(["lake", "env", "lean", str(handles_file)], repo, 600)

    write_text(out_dir / "table-generation-handles.log", result["output"])
    if result["returncode"] != 0:
        return [], check_result(
            "target coverage",
            False,
            f"Could not evaluate target coverage; lean exited {result['returncode']}.",
        )

    raw = parse_named_block(
        result["output"],
        "TABLE_GENERATION_HANDLES_BEGIN",
        "TABLE_GENERATION_HANDLES_END",
    )
    expected_keys = {f"{target['mode']}:{target['k']}" for target in targets}
    if set(raw) != expected_keys or any(
        value not in {"true", "false"} for value in raw.values()
    ):
        return [], check_result(
            "target coverage",
            False,
            "Target coverage output is incomplete or invalid.",
        )

    handled = [
        target
        for target in targets
        if raw[f"{target['mode']}:{target['k']}"] == "true"
    ]
    if not handled:
        return [], check_result(
            "target coverage",
            False,
            "The submission does not handle any configured benchmark target.",
        )
    return handled, check_result(
        "target coverage",
        True,
        f"The submission handles {len(handled)} of {len(targets)} configured targets.",
    )


def collect_metrics(
    repo: Path,
    out_dir: Path,
    target: dict[str, Any],
) -> tuple[dict[str, Any], dict[str, str]]:
    mode = str(target["mode"])
    k = int(target["k"])
    source = "\n".join(
        [
            "import TableGeneration.Submission.Defs",
            "import TableGeneration.Submission.Correctness",
            "import TableGeneration.Metrics",
            "",
            "open TableGeneration",
            "open TableGeneration.Operations",
            "",
            f"def targetMode : ProductMode := .{mode}",
            f"def targetK : Nat := {k}",
            "def targetProgram : Prog targetK := generate targetMode targetK (by decide)",
            "def targetPoints : List Point := generatedPoints targetMode targetK",
            "def targetPointOrder : List Point := generatePointsInOrder targetMode targetK (by decide)",
            "",
            '#eval IO.println "TABLE_GENERATION_METRICS_BEGIN"',
            f'#eval IO.println ("mode={mode}")',
            f'#eval IO.println ("k={k}")',
            '#eval IO.println ("submission_handles=" ++ toString (submissionHandles targetMode targetK))',
            '#eval IO.println ("total_operation_count=" ++ toString targetProgram.length)',
            '#eval IO.println ("arithmetic_operation_count=" ++ toString (arithmeticOperationCount targetProgram))',
            '#eval IO.println ("phase_product_count=" ++ toString (phaseProductCount targetProgram))',
            '#eval IO.println ("parallel_phase_product_layer_count=" ++ toString (parallelPhaseProductLayerCount targetProgram))',
            '#eval IO.println ("expected_point_count=" ++ toString (targetMode.pointCount targetK))',
            '#eval IO.println ("point_count=" ++ toString targetPoints.length)',
            '#eval IO.println ("point_order_count=" ++ toString targetPointOrder.length)',
            '#eval IO.println ("generated_points_all_valid=" ++ toString (targetPoints.all validPoint?))',
            '#eval IO.println ("generated_points_distinct=" ++ toString (decide (targetPoints.map normalizePoint).Nodup))',
            '#eval IO.println ("points=" ++ joinComma (targetPoints.map pointToString))',
            '#eval IO.println ("point_order=" ++ joinComma (targetPointOrder.map pointToString))',
            '#eval IO.println ("program=" ++ progToString targetProgram)',
            '#eval IO.println "TABLE_GENERATION_METRICS_END"',
            "",
        ]
    )

    with tempfile.TemporaryDirectory() as tmp:
        metrics_file = Path(tmp) / "CollectMetrics.lean"
        metrics_file.write_text(source, encoding="utf-8")
        result = run_cmd(["lake", "env", "lean", str(metrics_file)], repo, 600)

    write_text(out_dir / f"table-generation-metrics-{mode}-k{k}.log", result["output"])
    if result["returncode"] != 0:
        return {}, check_result(
            "target metrics",
            False,
            f"Could not evaluate {mode} k={k} metrics; lean exited {result['returncode']}.",
        )

    raw = parse_metric_output(result["output"])
    required = {
        "mode",
        "k",
        "submission_handles",
        "total_operation_count",
        "arithmetic_operation_count",
        "phase_product_count",
        "parallel_phase_product_layer_count",
        "expected_point_count",
        "point_count",
        "point_order_count",
        "generated_points_all_valid",
        "generated_points_distinct",
        "points",
        "point_order",
        "program",
    }
    missing = sorted(required - set(raw))
    if missing:
        return raw, check_result(
            "target metrics",
            False,
            "Missing metric fields: " + ", ".join(missing),
        )

    metrics: dict[str, Any] = dict(raw)
    int_keys = (
        "k",
        "total_operation_count",
        "arithmetic_operation_count",
        "phase_product_count",
        "parallel_phase_product_layer_count",
        "expected_point_count",
        "point_count",
        "point_order_count",
    )
    for key in int_keys:
        try:
            metrics[key] = int(str(metrics[key]))
        except ValueError:
            return raw, check_result("target metrics", False, f"{key} is not an integer.")

    if metrics["k"] != k or metrics["mode"] != mode:
        return metrics, check_result("target metrics", False, "Metrics target changed.")
    if str(metrics["submission_handles"]) != "true":
        return {}, skipped_result(
            "target metrics",
            f"The submission does not handle {mode} k={k}; target skipped.",
        )
    metrics["submission_handles"] = True
    if metrics["point_count"] != metrics["expected_point_count"]:
        return metrics, check_result(
            "target metrics",
            False,
            "Generated point count does not match the target mode and k.",
        )
    if str(metrics["generated_points_all_valid"]) != "true":
        return metrics, check_result(
            "target metrics",
            False,
            "Generated points must be 0, inf, or signed powers of two.",
        )
    metrics["generated_points_all_valid"] = True
    if str(metrics["generated_points_distinct"]) != "true":
        return metrics, check_result(
            "target metrics",
            False,
            "Generated points must be mathematically distinct.",
        )
    metrics["generated_points_distinct"] = True
    if metrics["point_order_count"] != metrics["point_count"]:
        return metrics, check_result(
            "target metrics",
            False,
            "The generated point order must have the same length as the generated point list.",
        )
    if metrics["phase_product_count"] != metrics["point_order_count"]:
        return metrics, check_result(
            "target metrics",
            False,
            "Phase-product operation count must equal generated point-order count.",
        )
    expected_total = metrics["arithmetic_operation_count"] + metrics["phase_product_count"]
    if metrics["total_operation_count"] != expected_total:
        return metrics, check_result(
            "target metrics",
            False,
            "Total operation count must equal arithmetic operations plus phase-product operations.",
        )
    has_valid_layers = (
        metrics["parallel_phase_product_layer_count"] == 0
        if metrics["phase_product_count"] == 0
        else 1 <= metrics["parallel_phase_product_layer_count"] <= metrics["phase_product_count"]
    )
    if not has_valid_layers:
        return metrics, check_result(
            "target metrics",
            False,
            "Parallel phase-product layer count is inconsistent with phase-product count.",
        )

    metrics["score"] = {
        "arithmetic_operation_count": metrics["arithmetic_operation_count"],
        "parallel_phase_product_layer_count": metrics["parallel_phase_product_layer_count"],
    }

    return metrics, check_result(
        "target metrics",
        True,
        f"{mode} k={k} score is "
        f"{metrics['arithmetic_operation_count']} arithmetic ops and "
        f"{metrics['parallel_phase_product_layer_count']} parallel phase-product layers.",
    )


def collect_target_metrics(
    repo: Path,
    out_dir: Path,
    targets: list[dict[str, Any]],
) -> tuple[dict[str, Any], dict[str, str]]:
    handled_targets, coverage_check = collect_handled_targets(repo, out_dir, targets)
    if coverage_check["status"] == "failure":
        return {"targets": []}, coverage_check

    target_metrics: list[dict[str, Any]] = []
    failures: list[str] = []
    details: list[str] = []
    for target in handled_targets:
        metrics, check = collect_metrics(repo, out_dir, target)
        if metrics:
            target_metrics.append(metrics)
        if check["status"] == "failure":
            failures.append(check["details"])
        elif check["status"] == "success":
            details.append(check["details"])
        else:
            failures.append(
                f"Coverage changed while evaluating {target['mode']} k={target['k']}."
            )

    if failures:
        return {"targets": target_metrics}, check_result(
            "target metrics",
            False,
            "; ".join(failures),
        )
    return {"targets": target_metrics}, check_result(
        "target metrics",
        True,
        f"Scored {len(target_metrics)} of {len(targets)} configured targets; "
        f"skipped {len(targets) - len(handled_targets)} unhandled targets. "
        + " ".join(details),
    )


def summary_detail(text: object, limit: int = 260) -> str:
    detail = str(text).replace("\n", " ").strip()
    if len(detail) <= limit:
        return detail
    return detail[: limit - 3].rstrip() + "..."


def weighted_cost(metrics: dict[str, Any], weights: dict[str, int]) -> int:
    return sum(weights[field] * metrics[field] for field in SCORE_FIELDS)


def build_benchmark_result(result: dict[str, Any]) -> dict[str, Any] | None:
    if result.get("phase") != "full" or result.get("status") != "success":
        return None

    benchmark = result.get("benchmark")
    if not isinstance(benchmark, dict) or not benchmark.get("configured"):
        return None
    weights = benchmark.get("weights")
    if not isinstance(weights, dict):
        return None

    metrics = result.get("metrics")
    target_metrics = metrics.get("targets") if isinstance(metrics, dict) else None
    if not isinstance(target_metrics, list) or not target_metrics:
        return None

    results = []
    for item in target_metrics:
        if not isinstance(item, dict):
            return None
        target_result = {
            "mode": item["mode"],
            "k": item["k"],
            "weighted_cost": weighted_cost(item, weights),
        }
        for field in BENCHMARK_METRIC_FIELDS:
            target_result[field] = item[field]
        results.append(target_result)

    metadata = result.get("metadata") or {}
    submission = {
        field: metadata[field]
        for field in (
            "repository",
            "pr_number",
            "head_ref",
            "head_sha",
            "base_sha",
            "run_id",
            "run_attempt",
            "created_at",
        )
        if metadata.get(field) not in (None, "")
    }
    target = result.get("target") or {}
    configured_targets = target.get("targets") or []
    return {
        "schema_version": 2,
        "benchmark": {
            "name": CHALLENGE,
            "target_count": len(configured_targets),
            "weights": weights,
        },
        "submission": submission,
        "results": results,
    }


def build_benchmark_markdown(benchmark: dict[str, Any]) -> str:
    submission = benchmark.get("submission") or {}
    submission_parts = []
    if submission.get("pr_number"):
        submission_parts.append(f"PR #{submission['pr_number']}")
    if submission.get("head_sha"):
        submission_parts.append(f"commit `{str(submission['head_sha'])[:12]}`")

    benchmark_config = benchmark["benchmark"]
    weights = benchmark_config["weights"]
    configured_target_count = benchmark_config["target_count"]
    lines = [
        "<!-- table-generation-submission-result -->",
        "### Table generation benchmark",
        "",
        "Status: **SUCCESS**",
    ]
    if submission_parts:
        lines.extend(["", "Submission: " + " · ".join(submission_parts)])
    lines.extend(
        [
            "",
            f"Scoring: `{score_formula(weights)}`.",
            "",
            f"Coverage: **{len(benchmark['results'])} of {configured_target_count}** targets.",
            "",
            "| Target | Weighted cost | Arithmetic ops | Parallel layers | Phase products | Total ops | Generated points |",
            "| --- | ---: | ---: | ---: | ---: | ---: | ---: |",
        ]
    )
    for item in benchmark["results"]:
        lines.append(
            f"| `{item['mode']}` `k={item['k']}` "
            f"| **{item['weighted_cost']}** "
            f"| {item['arithmetic_operation_count']} "
            f"| {item['parallel_phase_product_layer_count']} "
            f"| {item['phase_product_count']} "
            f"| {item['total_operation_count']} "
            f"| {item['point_count']} |"
        )
    lines.extend(["", "All correctness and safety checks passed."])
    return "\n".join(lines) + "\n"


def build_summary(result: dict[str, Any]) -> str:
    status = result["status"].upper()
    phase = result.get("phase", "full")
    lines = [
        "<!-- table-generation-submission-result -->",
        "### Table generation submission",
        "",
        f"Status: **{status}**",
    ]

    if phase == "preflight":
        lines.extend(["", "Phase: preflight checks only."])

    metrics = result.get("metrics") or {}
    target_metrics = metrics.get("targets") if isinstance(metrics, dict) else None
    if phase != "preflight" and result["status"] == "success" and target_metrics:
        lines.extend(["", "Scores:"])
        for item in target_metrics:
            lines.append(
                "- "
                f"`{item.get('mode')}` `k={item.get('k')}`: "
                f"`{item.get('arithmetic_operation_count')}` arithmetic ops, "
                f"`{item.get('parallel_phase_product_layer_count')}` parallel phase-product layers."
            )
    elif phase != "preflight" and result["status"] == "success":
        lines.extend(
            [
                "",
                "No scoring target is configured, so no metric score was produced.",
            ]
        )

    failed = [check for check in result["checks"] if check["status"] == "failure"]
    if failed:
        lines.extend(["", "Failed checks:"])
        for check in failed:
            lines.append(f"- `{check['name']}`: {summary_detail(check['details'])}")
    elif result["status"] == "success":
        if phase == "preflight":
            lines.extend(["", "Preflight checks passed. Full Lean verification has not run."])
        else:
            lines.extend(["", "All required checks passed."])

    lines.extend(["", "Artifacts uploaded: JSON result and logs."])
    return "\n".join(lines) + "\n"


def collect_metadata() -> dict[str, Any]:
    return {
        "repository": os.getenv("GITHUB_REPOSITORY", ""),
        "workflow": os.getenv("GITHUB_WORKFLOW", ""),
        "run_id": os.getenv("GITHUB_RUN_ID", ""),
        "run_attempt": os.getenv("GITHUB_RUN_ATTEMPT", ""),
        "event_name": os.getenv("GITHUB_EVENT_NAME", ""),
        "pr_number": os.getenv("TABLE_GEN_PR_NUMBER", ""),
        "base_ref": os.getenv("GITHUB_BASE_REF", ""),
        "head_ref": os.getenv("GITHUB_HEAD_REF", ""),
        "base_sha": os.getenv("TABLE_GEN_BASE_SHA", ""),
        "head_sha": os.getenv("TABLE_GEN_HEAD_SHA", ""),
        "created_at": utc_now(),
    }


def verify(repo: Path, out_dir: Path, preflight_only: bool = False) -> dict[str, Any]:
    metrics: dict[str, Any] = {}
    targets, target_error = read_target_config()
    weights, weights_error = read_score_weights()
    benchmark = benchmark_metadata(weights, weights_error)

    checks = preflight_checks(repo)

    if preflight_only:
        success = checks_passed(checks)
        return {
            "schema_version": 1,
            "challenge": CHALLENGE,
            "phase": "preflight",
            "status": "success" if success else "failure",
            "target": target_metadata(targets, target_error),
            "benchmark": benchmark,
            "metadata": collect_metadata(),
            "checks": checks,
            "metrics": metrics,
        }

    if not checks_passed(checks):
        checks.append(skipped_result("lean build", "Skipped because preflight checks failed."))
        checks.append(
            skipped_result("axiom dependencies", "Skipped because preflight checks failed.")
        )
        checks.append(skipped_result("target metrics", "Skipped because preflight checks failed."))
        return {
            "schema_version": 1,
            "challenge": CHALLENGE,
            "phase": "full",
            "status": "failure",
            "target": target_metadata(targets, target_error),
            "benchmark": benchmark,
            "metadata": collect_metadata(),
            "checks": checks,
            "metrics": metrics,
        }

    build_check = verify_build(repo, out_dir)
    checks.append(build_check)

    if build_check["status"] == "success":
        axiom_check = verify_axiom_dependencies(repo, out_dir)
        checks.append(axiom_check)
        proof_checks_ok = all(
            check["status"] == "success"
            for check in checks
            if check["status"] != "skipped"
        )
        if not proof_checks_ok:
            checks.append(
                skipped_result("target metrics", "Skipped because proof checks failed.")
            )
        elif target_error:
            checks.append(check_result("target metrics", False, target_error))
        elif weights_error:
            checks.append(check_result("target metrics", False, weights_error))
        elif targets is None:
            checks.append(skipped_result("target metrics", "No scoring target is configured."))
        else:
            metrics, metric_check = collect_target_metrics(repo, out_dir, targets)
            checks.append(metric_check)
    else:
        checks.append(skipped_result("axiom dependencies", "Skipped because Lean build failed."))
        checks.append(skipped_result("target metrics", "Skipped because Lean build failed."))

    required_checks = [check for check in checks if check["status"] != "skipped"]
    success = all(check["status"] == "success" for check in required_checks)
    return {
        "schema_version": 1,
        "challenge": CHALLENGE,
        "phase": "full",
        "status": "success" if success else "failure",
        "target": target_metadata(targets, target_error),
        "benchmark": benchmark,
        "metadata": collect_metadata(),
        "checks": checks,
        "metrics": metrics,
    }


def write_source_archive(repo: Path, out_dir: Path) -> None:
    archive_path = out_dir / "table-generation-submission-source.zip"
    helper_root = repo / SUBMISSION_DIR / "Policy"
    lean_files = [repo / POLICY_FILE, *sorted(helper_root.glob("**/*.lean"))]
    with zipfile.ZipFile(archive_path, "w", compression=zipfile.ZIP_DEFLATED) as archive:
        for path in lean_files:
            archive.write(path, arcname=path.relative_to(repo))


def write_artifacts(result: dict[str, Any], repo: Path, out_dir: Path) -> None:
    out_dir.mkdir(parents=True, exist_ok=True)
    write_text(
        out_dir / "table-generation-submission-result.json",
        json.dumps(result, indent=2, sort_keys=True) + "\n",
    )
    write_text(out_dir / "table-generation-summary.md", build_summary(result))
    benchmark = build_benchmark_result(result)
    if benchmark is not None:
        write_text(
            out_dir / "table-generation-results.json",
            json.dumps(benchmark, separators=(",", ":"), sort_keys=True) + "\n",
        )
        write_text(
            out_dir / "table-generation-results.md",
            build_benchmark_markdown(benchmark),
        )
        write_source_archive(repo, out_dir)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--repo", default=".", help="Repository root to verify.")
    parser.add_argument("--out-dir", default="artifacts", help="Artifact output directory.")
    parser.add_argument(
        "--preflight-only",
        action="store_true",
        help="Run structural submission checks without installing or invoking Lean.",
    )
    args = parser.parse_args()

    repo = Path(args.repo).resolve()
    out_dir = (repo / args.out_dir).resolve()
    try:
        result = verify(repo, out_dir, preflight_only=args.preflight_only)
    except Exception as exc:  # noqa: BLE001
        result = {
            "schema_version": 1,
            "challenge": CHALLENGE,
            "phase": "exception",
            "status": "failure",
            "target": target_metadata(None),
            "benchmark": benchmark_metadata(None),
            "metadata": collect_metadata(),
            "checks": [
                check_result("verifier exception", False, f"{type(exc).__name__}: {exc}")
            ],
            "metrics": {},
        }

    write_artifacts(result, repo, out_dir)
    return 0 if result["status"] == "success" else 1


if __name__ == "__main__":
    sys.exit(main())
