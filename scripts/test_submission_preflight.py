#!/usr/bin/env python3
"""Regression tests for the submission import and namespace preflight checks.

Run: python3 scripts/test_submission_preflight.py

These checks guard promotion, not the kernel: an installed policy file
(`Policy.lean` and everything under `Policy/`) is copied into the accepted tree
with its `TableGeneration.Submission.Policy` prefix rewritten. A file that
imports `BestKnown` or `RecursiveCost`, or opens a foreign top-level namespace,
builds at submission time and then breaks -- or silently mis-installs -- at
promotion. The checks move that failure to the pull request.
"""
import importlib.util
import tempfile
from pathlib import Path

_spec = importlib.util.spec_from_file_location(
    "verifier", Path(__file__).with_name("verifier.py")
)
verifier = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(verifier)


def _repo(policy: str, helpers: dict[str, str] | None = None) -> Path:
    root = Path(tempfile.mkdtemp())
    sub = root / "TableGeneration" / "Submission"
    (sub / "Policy").mkdir(parents=True)
    (sub / "Policy.lean").write_text(policy, encoding="utf-8")
    (sub / "Defs.lean").write_text("-- adapters\n", encoding="utf-8")
    (sub / "Correctness.lean").write_text("-- theorems\n", encoding="utf-8")
    for rel, text in (helpers or {}).items():
        path = sub / "Policy" / rel
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text, encoding="utf-8")
    return root


# --- imports -----------------------------------------------------------------

def test_contract_and_accepted_imports_are_allowed():
    policy = (
        "import TableGeneration.Policy\n"
        "import TableGeneration.Metrics\n"
        "import TableGeneration.Policies.Accepted.Pf4aff955f16b.OptimizedParity\n"
        "import TableGeneration.Submission.Policy.Helper\n"
        "namespace TableGeneration.Submission.Policy\n"
        "def implementation : Nat := 0\n"
        "end TableGeneration.Submission.Policy\n"
    )
    repo = _repo(policy, {"Helper.lean": "import TableGeneration.Policy\n"})
    assert verifier.verify_submission_imports(repo)["status"] == "success"


def test_bestknown_import_is_rejected():
    policy = (
        "import TableGeneration.BestKnown\n"
        "namespace TableGeneration.Submission.Policy\n"
        "end TableGeneration.Submission.Policy\n"
    )
    result = verifier.verify_submission_imports(_repo(policy))
    assert result["status"] == "failure"
    assert "BestKnown" in result["details"]


def test_recursivecost_import_is_rejected():
    policy = (
        "import TableGeneration.RecursiveCost.Planner\n"
        "namespace TableGeneration.Submission.Policy\n"
        "end TableGeneration.Submission.Policy\n"
    )
    assert verifier.verify_submission_imports(_repo(policy))["status"] == "failure"


def test_submission_adapter_import_is_rejected():
    # Installed files keep this import literally (it is not under the rewritten
    # prefix), so it points back at the template and cycles through BestKnown.
    policy = (
        "import TableGeneration.Submission.Defs\n"
        "namespace TableGeneration.Submission.Policy\n"
        "end TableGeneration.Submission.Policy\n"
    )
    assert verifier.verify_submission_imports(_repo(policy))["status"] == "failure"


def test_mathlib_import_is_rejected():
    policy = (
        "import Mathlib.Tactic\n"
        "namespace TableGeneration.Submission.Policy\n"
        "end TableGeneration.Submission.Policy\n"
    )
    assert verifier.verify_submission_imports(_repo(policy))["status"] == "failure"


def test_helper_import_is_checked_too():
    policy = (
        "import TableGeneration.Policy\n"
        "namespace TableGeneration.Submission.Policy\n"
        "end TableGeneration.Submission.Policy\n"
    )
    repo = _repo(policy, {"Bad.lean": "import TableGeneration.RecursiveCost.Model\n"})
    assert verifier.verify_submission_imports(repo)["status"] == "failure"


# --- namespaces --------------------------------------------------------------

def test_prefixed_and_nested_namespaces_are_allowed():
    # Mirrors the real GeneralParity helper: a prefixed outer namespace with
    # unprefixed namespaces nested inside it.
    helper = (
        "import TableGeneration.Policy\n"
        "namespace TableGeneration.Submission.Policy.GeneralParity\n"
        "namespace Precomputed\n"
        "def x : Nat := 0\n"
        "end Precomputed\n"
        "end TableGeneration.Submission.Policy.GeneralParity\n"
    )
    policy = (
        "import TableGeneration.Policy\n"
        "namespace TableGeneration.Submission.Policy\n"
        "def implementation : Nat := 0\n"
        "end TableGeneration.Submission.Policy\n"
    )
    repo = _repo(policy, {"GeneralParity.lean": helper})
    assert verifier.verify_namespace_prefix(repo)["status"] == "success"


def test_foreign_top_level_namespace_is_rejected():
    policy = (
        "import TableGeneration.Policy\n"
        "namespace Tables\n"
        "def x : Nat := 0\n"
        "end Tables\n"
    )
    result = verifier.verify_namespace_prefix(_repo(policy))
    assert result["status"] == "failure"
    assert "Tables" in result["details"]


def test_foreign_namespace_after_a_closed_prefixed_block_is_rejected():
    policy = (
        "import TableGeneration.Policy\n"
        "namespace TableGeneration.Submission.Policy\n"
        "end TableGeneration.Submission.Policy\n"
        "namespace Sneaky\n"
        "def x : Nat := 0\n"
        "end Sneaky\n"
    )
    assert verifier.verify_namespace_prefix(_repo(policy))["status"] == "failure"


def test_sections_do_not_unbalance_the_namespace_stack():
    policy = (
        "import TableGeneration.Policy\n"
        "namespace TableGeneration.Submission.Policy\n"
        "section\n"
        "def x : Nat := 0\n"
        "end\n"
        "namespace Inner\n"
        "def y : Nat := 0\n"
        "end Inner\n"
        "end TableGeneration.Submission.Policy\n"
    )
    assert verifier.verify_namespace_prefix(_repo(policy))["status"] == "success"


if __name__ == "__main__":
    tests = [v for k, v in sorted(globals().items()) if k.startswith("test_")]
    for t in tests:
        t()
        print(f"ok  {t.__name__}")
    print(f"\n{len(tests)} passed")
