#!/usr/bin/env python3
"""The verifier's overall deadline.

Per-command limits did not bound the run: 1800 for the build plus 600 each for
the axiom, coverage and metrics checks is 3600 seconds against a 2700-second
job, so a slow submission was cancelled by GitHub mid-step instead of being
told which step ran out.

Run: python3 scripts/test_verifier_deadline.py
"""
import sys
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from scripts import verifier  # noqa: E402


def _reset() -> None:
    verifier._deadline = None


def test_unset_deadline_leaves_timeout_alone():
    # Tests and library callers that never start a budget keep the old behaviour.
    _reset()
    assert verifier.remaining_seconds() is None
    r = verifier.run_cmd(["true"], Path("."))
    assert r["returncode"] == 0, r


def test_command_is_clamped_to_what_is_left():
    verifier.start_deadline(2)
    # `sleep 10` would pass its own 1800s default, but only ~2s of budget remain.
    started = time.monotonic()
    r = verifier.run_cmd(["sleep", "10"], Path("."))
    elapsed = time.monotonic() - started
    _reset()
    assert r["returncode"] == 124, r
    assert elapsed < 6, f"clamped command ran {elapsed:.1f}s; budget was 2s"


def test_expired_budget_refuses_without_running():
    verifier.start_deadline(0)
    time.sleep(0.01)
    started = time.monotonic()
    r = verifier.run_cmd(["sleep", "10"], Path("."))
    elapsed = time.monotonic() - started
    _reset()
    assert r["returncode"] == 124, r
    assert elapsed < 1, f"expired budget still ran the command for {elapsed:.1f}s"
    assert "ran out before" in r["output"], r["output"]
    assert "sleep 10" in r["output"], r["output"]


def test_deadline_decreases():
    verifier.start_deadline(60)
    first = verifier.remaining_seconds()
    time.sleep(0.05)
    second = verifier.remaining_seconds()
    _reset()
    assert first is not None and second is not None
    assert second < first, (first, second)


def test_build_target_is_narrowed_and_mathlib_free():
    # The whole point of the narrowed target: a submission must not drag in
    # Mathlib or the accepted policies, neither of which it can affect.
    assert verifier.TARGET_MODULES == [
        "TableGeneration.Submission.Correctness",
        "TableGeneration.Metrics",
    ], verifier.TARGET_MODULES
    assert not hasattr(verifier, "TARGET_MODULE"), "stale single-target constant"


if __name__ == "__main__":
    tests = [v for k, v in sorted(globals().items()) if k.startswith("test_")]
    for t in tests:
        t()
        print(f"ok  {t.__name__}")
    print(f"\n{len(tests)} passed")
