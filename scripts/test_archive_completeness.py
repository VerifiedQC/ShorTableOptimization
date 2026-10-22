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
import sys
import tempfile
import zipfile
from pathlib import Path

_spec = importlib.util.spec_from_file_location(
    "verifier", Path(__file__).with_name("verifier.py")
)
verifier = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(verifier)

# promote.py imports from the `scripts` package, so the repository root has to
# be importable when this file is run directly rather than as a module.
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from scripts import promote  # noqa: E402


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


# --- hole 2 (closed differently): the adapter files are now protected --------

def test_adapter_files_are_not_editable_and_not_archived():
    """Defs.lean and Correctness.lean are fixed adapters: a submission may not
    change them, so they are not part of the editable, archived surface. This
    is the containment kept the other way round -- nothing editable is missing
    from the archive, and nothing archived is uneditable."""
    assert not verifier.is_allowed_changed_file(
        "TableGeneration/Submission/Defs.lean"
    )
    assert not verifier.is_allowed_changed_file(
        "TableGeneration/Submission/Correctness.lean"
    )
    with tempfile.TemporaryDirectory() as tmp:
        archived = _archive_names(_fake_repo(Path(tmp)))
        assert "TableGeneration/Submission/Defs.lean" not in archived
        assert "TableGeneration/Submission/Correctness.lean" not in archived


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


def _leaderboard(layer_counts):
    """Synthetic leaderboard: one champion at k=4 plus challengers."""
    policies = [
        {
            "policy_id": f"{index:040x}",
            "results": [
                {
                    "mode": "PhaseProduct",
                    "k": 4,
                    "parallel_phase_product_layer_count": layers,
                    "arithmetic_operation_count": 26,
                }
            ],
        }
        for index, layers in enumerate(layer_counts)
    ]
    return {
        "policies": policies,
        "champions": [
            {"mode": "PhaseProduct", "k": 4, "policy_ids": [policies[0]["policy_id"]]}
        ],
    }


def test_catalog_excludes_tables_deeper_than_the_champion():
    """The gate model charges nothing for depth, so the catalogue bounds it."""
    targets = [{"mode": "PhaseProduct", "k": 4}]
    # champion has 3 layers; challengers have 2, 3 and 4.
    board = _leaderboard([3, 2, 3, 4])
    champions = promote.selected_champions(board, targets)
    kept = {
        entry["policy_id"] for entry in promote.catalog_entries(board, targets, champions)
    }
    shallower, equal, deeper = (
        board["policies"][1]["policy_id"],
        board["policies"][2]["policy_id"],
        board["policies"][3]["policy_id"],
    )
    assert shallower in kept, "a shallower table must stay in the catalogue"
    assert equal in kept, "a table matching the champion's depth must stay"
    assert deeper not in kept, "a table deeper than the champion must be excluded"


def test_catalog_keeps_every_table_at_the_champion_depth():
    """The bound is a no-op when nothing exceeds it."""
    targets = [{"mode": "PhaseProduct", "k": 4}]
    board = _leaderboard([3, 3, 3])
    kept = promote.catalog_entries(board, targets, promote.selected_champions(board, targets))
    assert len(kept) == 3, "no table at the bound may be dropped"


def test_layer_bound_follows_the_selected_champion():
    # The bound used to resolve champion -> policy -> metrics on its own. Tying
    # it to selected_champions' output is what stops the two disagreeing about
    # which policy is the champion at an arity.
    targets = [{"mode": "PhaseProduct", "k": 4}]
    board = _leaderboard([3, 2, 4])
    champions = promote.selected_champions(board, targets)
    assert promote.champion_layer_bound(champions) == {4: 3}
    # Move the champion slot to the 2-layer table: the bound must follow the
    # policy selected_champions resolved, not any other entry in the board.
    ids = sorted(policy["policy_id"] for policy in board["policies"])
    board["champions"][0]["policy_ids"] = [ids[2], ids[1]]
    champions = promote.selected_champions(board, targets)
    assert champions[0]["policy_id"] == ids[1], "policy_ids ties break on the lowest id"
    assert promote.champion_layer_bound(champions) == {4: 2}


if __name__ == "__main__":
    tests = [v for k, v in sorted(globals().items()) if k.startswith("test_")]
    for t in tests:
        t()
        print(f"ok  {t.__name__}")
    print(f"\n{len(tests)} passed")
