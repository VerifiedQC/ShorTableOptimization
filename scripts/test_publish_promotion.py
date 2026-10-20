#!/usr/bin/env python3
"""Check that promotion commits what it may and refuses what it may not.

`publish_promotion.py` is the last gate before generated Lean lands on `main`,
and it pushes without anyone reviewing the diff. The two things that must hold
are that the allowlist actually blocks a stray path, and that the rebase keeps
a concurrent commit to `main` when the hour-long job is overtaken.

Run: python3 scripts/test_publish_promotion.py
"""

from __future__ import annotations

import subprocess
import sys
import tempfile
from pathlib import Path

SCRIPT = Path(__file__).resolve().parent / "ci" / "publish_promotion.py"
GENERATED = "TableGeneration/BestKnown.lean"
REPORT = "leaderboard/best-known.md"


def git(repo: Path, *args: str) -> str:
    done = subprocess.run(
        ["git", *args], cwd=repo, text=True, capture_output=True, check=True
    )
    return done.stdout.strip()


def write(repo: Path, path: str, text: str) -> None:
    target = repo / path
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_text(text, encoding="utf-8")


def promote(repo: Path) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        [sys.executable, str(SCRIPT)], cwd=repo, text=True, capture_output=True
    )


def fixture(root: Path) -> tuple[Path, Path]:
    """A bare `origin` with one commit on `main`, and a clone of it."""
    origin, work = root / "origin.git", root / "work"
    subprocess.run(
        ["git", "init", "--bare", "--initial-branch=main", str(origin)],
        check=True, capture_output=True,
    )
    subprocess.run(
        ["git", "clone", str(origin), str(work)], check=True, capture_output=True
    )
    git(work, "config", "user.email", "test@example.invalid")
    git(work, "config", "user.name", "Test")
    write(work, GENERATED, "-- baseline\n")
    write(work, REPORT, "# baseline\n")
    git(work, "add", "-A")
    git(work, "commit", "-m", "baseline")
    git(work, "push", "origin", "main")
    return origin, work


def remote_head(origin: Path) -> str:
    return subprocess.run(
        ["git", "--git-dir", str(origin), "rev-parse", "main"],
        text=True, capture_output=True, check=True,
    ).stdout.strip()


def test_nothing_to_do() -> None:
    with tempfile.TemporaryDirectory() as tmp:
        origin, work = fixture(Path(tmp))
        before = remote_head(origin)
        done = promote(work)
        assert done.returncode == 0, done.stderr
        assert "already current" in done.stdout, done.stdout
        assert remote_head(origin) == before, "pushed with nothing to promote"


def test_generated_paths_land_on_main() -> None:
    with tempfile.TemporaryDirectory() as tmp:
        origin, work = fixture(Path(tmp))
        before = remote_head(origin)
        write(work, GENERATED, "-- promoted\n")
        write(work, "TableGeneration/Policies/Accepted/K6.lean", "-- accepted\n")
        done = promote(work)
        assert done.returncode == 0, done.stderr + done.stdout
        after = remote_head(origin)
        assert after != before, "promotion did not reach main"
        assert "Promoted to main" in done.stdout, done.stdout
        subject = git(work, "log", "-1", "--format=%s", after)
        assert subject == "feat: promote best-known table policies", subject


def test_stray_path_is_refused() -> None:
    with tempfile.TemporaryDirectory() as tmp:
        origin, work = fixture(Path(tmp))
        before = remote_head(origin)
        write(work, GENERATED, "-- promoted\n")
        write(work, "scripts/verifier.py", "# not promotion's to touch\n")
        done = promote(work)
        assert done.returncode != 0, "a stray path was allowed through"
        assert "scripts/verifier.py" in done.stderr, done.stderr
        assert remote_head(origin) == before, "pushed despite a stray path"


def test_rebases_onto_a_main_that_moved() -> None:
    """The job takes ~an hour; `main` can gain a commit while it runs."""
    with tempfile.TemporaryDirectory() as tmp:
        origin, work = fixture(Path(tmp))

        other = Path(tmp) / "other"
        subprocess.run(
            ["git", "clone", str(origin), str(other)], check=True, capture_output=True
        )
        git(other, "config", "user.email", "other@example.invalid")
        git(other, "config", "user.name", "Other")
        write(other, "README.md", "# moved on\n")
        git(other, "add", "-A")
        git(other, "commit", "-m", "unrelated work")
        git(other, "push", "origin", "main")

        write(work, GENERATED, "-- promoted\n")
        done = promote(work)
        assert done.returncode == 0, done.stderr + done.stdout

        log = git(work, "log", "--format=%s", "origin/main")
        assert log.splitlines()[:2] == [
            "feat: promote best-known table policies",
            "unrelated work",
        ], log
        head = remote_head(origin)
        kept = subprocess.run(
            ["git", "--git-dir", str(origin), "show", f"{head}:README.md"],
            text=True, capture_output=True, check=True,
        ).stdout
        assert kept == "# moved on\n", "the concurrent commit was clobbered"


if __name__ == "__main__":
    for name, case in sorted(globals().items()):
        if name.startswith("test_"):
            case()
            print(f"ok  {name}")
    print("publish_promotion: all checks passed")
