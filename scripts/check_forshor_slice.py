#!/usr/bin/env python3
"""Check the integrated companion cost-model slice against its source.

`TableGeneration/RecursiveCost/ForShor/` holds a small set of definitions taken
verbatim from the companion development. Because they are integrated rather
than depended on, nothing stops them drifting from upstream. This script is the
check.

It needs a companion checkout, supplied by `--forshor` or `$FORSHOR_ROOT`, and
**skips cleanly when neither is set**, so it is safe to wire into a workflow
that has no access to one. It never reaches the network and never records a
URL: the path comes from the environment.

For each declaration in MANIFEST it extracts the body from both trees,
normalizes away comments, whitespace and the `Nat`/`Rat` spellings, and
compares. Deviations that are known and deliberate are listed in DEVIATIONS
with the reason, and are reported rather than treated as drift.

Exit codes: 0 agreement (or skipped), 1 drift found, 2 the check could not run.
"""

from __future__ import annotations

import argparse
import os
import re
import subprocess
import sys
from pathlib import Path

# Companion commit the slice was taken from. Update together with the files.
PINNED_COMMIT = "d5a165b"

FRAMEWORK = "FastMultiplication/ShorVerification/Framework"

# our_module -> (companion file, [declaration names])
MANIFEST: dict[str, tuple[str, list[str]]] = {
    "Registers.lean": (
        f"{FRAMEWORK}/Quantum/Registers.lean",
        ["Reg", "empty", "width", "regSize", "ExtReg", "capacity"],
    ),
    "LowGate.lean": (
        f"{FRAMEWORK}/AbstractMachine/LowGate.lean",
        ["LowGate"],
    ),
    "LowGate.lean:costmodel": (
        f"{FRAMEWORK}/Gatecount/CostModel.lean",
        ["LowGateCostModel", "gateCount"],
    ),
    "ResourceModel.lean": (
        f"{FRAMEWORK}/Gatecount/ResourceModel.lean",
        [
            "directSignedPhaseProductGateCount",
            "GateResources",
            "zero",
            "seq",
            "totalGates",
            "LowGateResourceModel",
            "resources",
            "toCostModel",
            "cuccaroModAddResources",
            "negateResources",
            "addScaledResources",
            "radixReverseResources",
            "shorGateResourceModel",
            "shorGateCostModel",
        ],
    ),
}

# Declarations that intentionally differ, and why.
DEVIATIONS: dict[str, str] = {
    "Disjoint": (
        "List.Disjoint is in Batteries, not Lean core; its statement is "
        "inlined as ListDisjoint so the slice needs no dependency"
    ),
    "Angle": "companion writes the Mathlib notation Q; Rat is the same type",
}

# Ours only: not from the companion, so nothing to compare against.
OURS_ONLY = {
    "ListDisjoint",
    "canonicalReg",
    "canonicalExtReg",
    "canonicalReg_width",
    "canonicalExtReg_width",
    "negateResourcesAtWidth",
    "negateResources_eq_atWidth",
    "shorGateCostModel_negate_atWidth",
    "cuccaroModAddResources_totalGates",
    "negateResourcesAtWidth_totalGates",
    "negateResources_totalGates",
    "shorGateResourceModel_signExtend_totalGates",
    "shorGateResourceModel_zeroExtend_totalGates",
}

SLICE_DIR = Path("TableGeneration/RecursiveCost/ForShor")

DECL_RE = r"^(?:@\[[^\]]*\]\s*)?(?:noncomputable )?(?:def|structure|inductive|abbrev) "


def extract(text: str, name: str) -> str | None:
    """Pull one declaration's source out of a Lean file."""
    match = re.search(DECL_RE + re.escape(name) + r"\b", text, re.M)
    if not match:
        return None
    lines = text[match.start():].split("\n")
    out = [lines[0]]
    for line in lines[1:]:
        stripped = line.strip()
        if stripped.startswith("/-") or stripped.startswith("end "):
            break
        # a new top-level declaration ends this one
        if line and not line[0].isspace() and not stripped.startswith(("|", "deriving")):
            break
        out.append(line)
    return "\n".join(out).rstrip()


def normalize(text: str) -> str:
    text = text.replace("ℕ", "Nat").replace("ℚ", "Rat").replace("ℤ", "Int")
    text = re.sub(r"--.*", "", text)
    text = re.sub(r"/-.*?-/", "", text, flags=re.S)
    return re.sub(r"\s+", " ", text).strip()


def companion_file(root: Path, relpath: str, commit: str | None) -> str | None:
    """Read a companion file, at a pinned commit when the checkout has git."""
    if commit:
        try:
            return subprocess.run(
                ["git", "-C", str(root), "cat-file", "-p", f"{commit}:{relpath}"],
                capture_output=True, text=True, check=True,
            ).stdout
        except (subprocess.CalledProcessError, FileNotFoundError):
            pass  # fall back to the working tree
    path = root / relpath
    return path.read_text() if path.exists() else None


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--forshor", default=os.environ.get("FORSHOR_ROOT"),
                        help="companion checkout (default: $FORSHOR_ROOT)")
    parser.add_argument("--commit", default=PINNED_COMMIT,
                        help=f"companion commit to compare against (default: {PINNED_COMMIT})")
    parser.add_argument("--working-tree", action="store_true",
                        help="compare against the checkout's current state, not the pinned commit")
    args = parser.parse_args()

    if not args.forshor:
        print("check_forshor_slice: no companion checkout given "
              "(--forshor or $FORSHOR_ROOT); skipping.")
        return 0

    root = Path(args.forshor).expanduser()
    if not root.is_dir():
        print(f"check_forshor_slice: {root} is not a directory", file=sys.stderr)
        return 2

    commit = None if args.working_tree else args.commit
    repo = Path(__file__).resolve().parent.parent
    ok, drift, missing = 0, [], []

    for our_name, (relpath, decls) in MANIFEST.items():
        our_path = repo / SLICE_DIR / our_name.split(":")[0]
        if not our_path.exists():
            missing.append(f"{our_path} does not exist")
            continue
        ours_text = our_path.read_text()
        theirs_text = companion_file(root, relpath, commit)
        if theirs_text is None:
            missing.append(f"{relpath} not found in the companion at {commit or 'working tree'}")
            continue
        for decl in decls:
            ours, theirs = extract(ours_text, decl), extract(theirs_text, decl)
            if theirs is None:
                missing.append(f"{decl}: not found in {relpath}")
            elif ours is None:
                missing.append(f"{decl}: not found in {our_path.name}")
            elif normalize(ours) == normalize(theirs):
                ok += 1
            else:
                drift.append((decl, relpath, normalize(theirs), normalize(ours)))

    print(f"companion: {root} @ {commit or 'working tree'}")
    print(f"agreement: {ok} declarations match")
    for decl, why in sorted(DEVIATIONS.items()):
        print(f"deviation: {decl} -- {why}")
    if missing:
        print()
        for m in missing:
            print(f"UNRESOLVED: {m}")
    if drift:
        print()
        for decl, relpath, theirs, ours in drift:
            print(f"DRIFT: {decl} ({relpath})")
            print(f"  companion: {theirs[:200]}")
            print(f"  ours     : {ours[:200]}")
        return 1
    return 2 if missing else 0


if __name__ == "__main__":
    sys.exit(main())
