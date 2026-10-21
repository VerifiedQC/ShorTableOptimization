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


def test_submission_template_is_fast_forwarded() -> None:
    # A `GITHUB_TOKEN` push starts no workflow runs, so `sync-submission-template`
    # never fires after a promotion. Promotion has to move the branch itself.
    with tempfile.TemporaryDirectory() as tmp:
        origin, work = fixture(Path(tmp))
        git(work, "push", "origin", "main:submission/template")
        write(work, GENERATED, "-- promoted\n")
        done = promote(work)
        assert done.returncode == 0, done.stderr + done.stdout
        main_sha = git(work, "rev-parse", "refs/remotes/origin/main")
        template = git(work, "ls-remote", str(origin), "refs/heads/submission/template")
        assert template.split()[0] == main_sha, (
            f"template at {template.split()[0]!r}, main at {main_sha!r}"
        )


def test_a_failing_follow_up_does_not_fail_the_promotion() -> None:
    # `main` is already pushed by then. Reporting failure would read as though
    # nothing had landed.
    with tempfile.TemporaryDirectory() as tmp:
        origin, work = fixture(Path(tmp))
        # Make the template push fail: a non-fast-forward the promotion cannot
        # resolve, since it never force-pushes.
        write(work, REPORT, "# divergent\n")
        git(work, "add", "-A")
        git(work, "commit", "-m", "divergent template")
        git(work, "push", "origin", "HEAD:submission/template")
        git(work, "reset", "--hard", "HEAD~1")

        before = remote_head(origin)
        write(work, GENERATED, "-- promoted\n")
        done = promote(work)
        assert done.returncode == 0, (
            "a failed follow-up must not fail the promotion\n" + done.stdout + done.stderr
        )
        assert remote_head(origin) != before, "main did not move"
        assert "warning: could not" in done.stdout, done.stdout


def test_best_effort_swallows_failure_and_reports_it() -> None:
    sys.path.insert(0, str(SCRIPT.parent.parent.parent))
    from scripts.ci import publish_promotion

    assert publish_promotion.best_effort(["false"], "fail on purpose") is False
    assert publish_promotion.best_effort(["true"], "succeed") is True
    assert publish_promotion.best_effort(["no-such-binary-xyzzy"], "missing") is False


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
