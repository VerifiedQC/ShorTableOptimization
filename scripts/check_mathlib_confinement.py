#!/usr/bin/env python3
"""Fail if Mathlib or the companion library is imported outside the recursive-cost model.

The submission contract's guarantee is that `#print axioms` on
`TableGeneration.generatedPoints_valid` and
`TableGeneration.generate_ProgConsumesPtsSafe` reports `propext` and nothing
else. That holds today for a structural reason: those theorems' proof terms
never reach `TableGeneration/RecursiveCost/**`, which is the only part of the
library that imports Mathlib.

Nothing in Lean enforces that boundary. The moment a Mathlib import lands in
`Basic.lean`, `Language.lean`, `Spec.lean`, `Policy.lean`, `BestKnown.lean`,
`Policies/Accepted/**` or `Submission/**`, the proofs in those files can pick up
`Classical.choice` and the audit starts failing -- and it would fail on a
submitter's pull request, for a change a maintainer made. This script is the
enforcement, so the breakage surfaces here instead.

This runs on changes to `main`, not on submission pull requests, and that is
deliberate. A submission is gated by the audit itself: `verify_axiom_dependencies`
runs `#print axioms` on both contract theorems against `ALLOWED_AXIOMS`, so a
submitter who imports Mathlib and reaches `Classical.choice` is rejected by the
thing the guarantee is actually made of. One who imports it and stays
`propext`-clean has broken nothing, and a grep for the import would reject them
anyway. The structural check is for maintainer edits, which no per-submission
audit would catch until it started failing on someone else's pull request.

Exit codes: 0 confined, 1 a Mathlib import escaped, 2 the check could not run.
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

# The only subtree allowed to import Mathlib.
ALLOWED_PREFIX = Path("TableGeneration/RecursiveCost")

# Batteries arrives with Mathlib and carries the same risk. FastMultiplication
# is the companion Lake dependency; it imports Mathlib itself, so an import of
# it outside the allowed prefix would pull Mathlib into the submission path just
# as directly, and would break the `propext`-only axiom audit.
IMPORT_RE = re.compile(r"^\s*import\s+(Mathlib|Batteries|FastMultiplication)\b", re.M)

# A direct Mathlib import is not the only way to pull Mathlib onto the submission
# path: importing `TableGeneration.RecursiveCost.*` (the only subtree that is
# allowed to import Mathlib) drags it in transitively. Flag that import anywhere
# outside the allowed prefix, except in the library root `TableGeneration.lean`,
# which is meant to import `RecursiveCost.Correctness` to place it in the build.
TRANSITIVE_RE = re.compile(r"^\s*import\s+(TableGeneration\.RecursiveCost\b[\w.]*)", re.M)
ROOT_FILE = Path("TableGeneration.lean")

SEARCH_ROOTS = [Path("TableGeneration"), Path("scripts")]


def main() -> int:
    repo = Path(__file__).resolve().parent.parent
    offenders: list[tuple[Path, str]] = []
    scanned = 0

    for root in SEARCH_ROOTS:
        base = repo / root
        if not base.is_dir():
            continue
        for path in sorted(base.rglob("*.lean")):
            relative = path.relative_to(repo)
            scanned += 1
            try:
                text = path.read_text(encoding="utf-8")
            except OSError as error:  # unreadable file is a real failure
                print(f"check_mathlib_confinement: cannot read {relative}: {error}",
                      file=sys.stderr)
                return 2
            if ALLOWED_PREFIX in relative.parents:
                continue
            for match in IMPORT_RE.finditer(text):
                line = text[: match.start()].count("\n") + 1
                offenders.append((relative, f"{line}: {match.group(0).strip()}"))
            # The transitive rule applies to the contract library only. The Lean
            # test drivers under scripts/tests/ legitimately import RecursiveCost
            # (they exercise it) and never ship on the submission path.
            if root == Path("TableGeneration") and relative != ROOT_FILE:
                for match in TRANSITIVE_RE.finditer(text):
                    line = text[: match.start()].count("\n") + 1
                    offenders.append((relative, f"{line}: {match.group(0).strip()}"))

    if not scanned:
        print("check_mathlib_confinement: no Lean files found", file=sys.stderr)
        return 2

    if offenders:
        print(f"Mathlib escaped {ALLOWED_PREFIX}/ -- the propext-only axiom audit "
              f"for the submission theorems is no longer structurally guaranteed:\n")
        for relative, where in offenders:
            print(f"  {relative}:{where}")
        print("\nEither move the import under "
              f"{ALLOWED_PREFIX}/, or, if the dependency is genuinely needed on "
              "the submission path, update ALLOWED_AXIOMS in scripts/verifier.py "
              "deliberately and say so in the benchmark documentation.")
        return 1

    print(f"check_mathlib_confinement: {scanned} Lean files scanned, "
          f"Mathlib confined to {ALLOWED_PREFIX}/")
    return 0


if __name__ == "__main__":
    sys.exit(main())
