#!/usr/bin/env python3
"""Regression tests for archive completeness.

Run: python3 scripts/test_archive_completeness.py

The property under test is a containment:

    { files preflight admits }  ==  { files write_source_archive collects }

If the admitted set is ever the larger of the two, a submission can pass CI
while depending on a file its own `source.zip` never captured — the policy is
then accepted but not recheckable from its archive, which is the one thing the
archive exists to guarantee.

Two holes were closed here, neither of which had ever fired:

  1. Preflight admitted `TableGeneration/Submission/**/*.lean` at any depth,
     while the archiver collected only `Policy.lean` and `Policy/**`. A helper
     at `Submission/Helpers.lean` was admitted and dropped.
  2. `Defs.lean` and `Correctness.lean` are writable by a submission and were
     never archived. `verify_wrapper_definitions` and
     `verify_theorem_statements` pin the *named* declarations but neither
     forbids an extra definition alongside them, so `Policy.lean` could depend
     on one that no archive captured.

Note the archive is deliberately WIDER than `promote.portable_members`, which
is the install set: the two adapters are archived for reconstruction but are
not installed per policy.
"""
import importlib.util
import tempfile
import zipfile
from pathlib import Path

_spec = importlib.util.spec_from_file_location(
    "verifier", Path(__file__).with_name("verifier.py")
)
verifier = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(verifier)


def _fake_repo(root: Path, extra: dict[str, str] | None = None) -> Path:
    """A minimal tree with the three submission files, plus anything extra."""
    sub = root / "TableGeneration" / "Submission"
    (sub / "Policy").mkdir(parents=True)
    (sub / "Policy.lean").write_text("import TableGeneration.Policy\n", encoding="utf-8")
    (sub / "Defs.lean").write_text("-- adapters\n", encoding="utf-8")
    (sub / "Correctness.lean").write_text("-- theorems\n", encoding="utf-8")
    for rel, text in (extra or {}).items():
        path = root / rel
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text, encoding="utf-8")
    return root


def _archive_names(repo: Path) -> set[str]:
    with tempfile.TemporaryDirectory() as out:
        verifier.write_source_archive(repo, Path(out))
        zip_path = Path(out) / "table-generation-submission-source.zip"
        with zipfile.ZipFile(zip_path) as archive:
            return {
                n.replace("\\", "/") for n in archive.namelist() if n.endswith(".lean")
            }


# --- the containment property ------------------------------------------------

def test_admitted_set_is_archived():
    """Every path preflight admits must appear in the archive. The core property."""
    with tempfile.TemporaryDirectory() as tmp:
        repo = _fake_repo(
            Path(tmp),
            {"TableGeneration/Submission/Policy/Helper.lean": "-- helper\n"},
        )
        archived = _archive_names(repo)
        for name in sorted(archived):
            assert verifier.is_allowed_changed_file(name), (
                f"{name} is archived but preflight would reject it"
            )
        candidates = [
            "TableGeneration/Submission/Policy.lean",
            "TableGeneration/Submission/Defs.lean",
            "TableGeneration/Submission/Correctness.lean",
            "TableGeneration/Submission/Policy/Helper.lean",
        ]
        for name in candidates:
            assert verifier.is_allowed_changed_file(name)
            assert name in archived, f"{name} is admitted by preflight but not archived"


# --- hole 1: a helper outside Policy/ ----------------------------------------

def test_helper_outside_policy_dir_is_rejected():
    """The case that was admitted and then silently dropped from the archive."""
    for path in (
        "TableGeneration/Submission/Helpers.lean",
        "TableGeneration/Submission/Lib/Parity.lean",
        "TableGeneration/Submission/PolicyExtra.lean",
    ):
        assert not verifier.is_allowed_changed_file(path), (
            f"{path} must be rejected: the archiver does not collect it"
        )


def test_helper_inside_policy_dir_is_admitted_at_any_depth():
    assert verifier.is_allowed_changed_file(
        "TableGeneration/Submission/Policy/Parity.lean"
    )
    assert verifier.is_allowed_changed_file(
        "TableGeneration/Submission/Policy/Deep/Nested/Aux.lean"
    )


def test_nested_helpers_are_archived():
    with tempfile.TemporaryDirectory() as tmp:
        repo = _fake_repo(
            Path(tmp),
            {"TableGeneration/Submission/Policy/Deep/Nested/Aux.lean": "-- aux\n"},
        )
        assert "TableGeneration/Submission/Policy/Deep/Nested/Aux.lean" in _archive_names(repo)


# --- hole 2: the writable adapter files --------------------------------------

def test_adapter_files_are_archived():
    """Defs.lean and Correctness.lean are writable, so they must be captured."""
    with tempfile.TemporaryDirectory() as tmp:
        archived = _archive_names(_fake_repo(Path(tmp)))
        assert "TableGeneration/Submission/Defs.lean" in archived
        assert "TableGeneration/Submission/Correctness.lean" in archived


# --- guards against over-collecting ------------------------------------------

def test_base_branch_files_are_not_archived():
    """Only submission files. Pulling in base-branch modules would be a new bug."""
    with tempfile.TemporaryDirectory() as tmp:
        repo = _fake_repo(Path(tmp), {"TableGeneration/Policy.lean": "-- base\n"})
        assert "TableGeneration/Policy.lean" not in _archive_names(repo)
    assert not verifier.is_allowed_changed_file("TableGeneration/Policy.lean")
    assert not verifier.is_allowed_changed_file("scripts/verifier.py")
    assert not verifier.is_allowed_changed_file("lakefile.lean")


def test_non_lean_files_under_policy_are_rejected():
    assert not verifier.is_allowed_changed_file(
        "TableGeneration/Submission/Policy/notes.md"
    )


def test_historical_submissions_still_pass():
    """Every changed-file set from the eight real submission branches.

    Narrowing preflight must not retroactively invalidate an accepted policy.
    """
    historical = [
        ["TableGeneration/Submission/Policy.lean"],
        [
            "TableGeneration/Submission/Policy.lean",
            "TableGeneration/Submission/Policy/GeneralParity.lean",
        ],
        [
            "TableGeneration/Submission/Policy.lean",
            "TableGeneration/Submission/Policy/Fixed.lean",
            "TableGeneration/Submission/Policy/OptimizedParity.lean",
        ],
    ]
    for changed in historical:
        for path in changed:
            assert verifier.is_allowed_changed_file(path), (
                f"{path} was accepted historically and must remain admissible"
            )


if __name__ == "__main__":
    tests = [v for k, v in sorted(globals().items()) if k.startswith("test_")]
    for t in tests:
        t()
        print(f"ok  {t.__name__}")
    print(f"\n{len(tests)} passed")
