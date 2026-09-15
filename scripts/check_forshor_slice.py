#!/usr/bin/env python3
"""Check the integrated companion cost-model slice against its source.

**A maintainer tool, run by hand. Not a CI gate.**

`TableGeneration/RecursiveCost/ForShor/` holds a small set of definitions taken
verbatim from the companion development and pinned to the commit in
`PINNED_COMMIT`. This project is not a dependent of the companion -- it is built
on the same framework, and small divergences in the framework layer are fine.
The cost model is the part that must not drift, and it is finished, so checking
it is something you do deliberately when syncing the slice to a new companion
commit, not something worth running on every promotion.

What guards the cost model continuously is in-repo and needs no companion
checkout: the oracle's `--width-scan` and `--allocation` modes
(`scripts/tests/RecursiveCostOracle.lean`, run by
`scripts/test_recursive_cost.js` in CI) check the planner's array width scan and
its closed-form allocation charge against the integrated copies. This script
answers a different question -- whether those integrated copies still match
upstream.

Usage:

    FORSHOR_ROOT=/path/to/ForShor python3 scripts/check_forshor_slice.py

    # before re-pinning, compare against the companion's current HEAD instead
    python3 scripts/check_forshor_slice.py --forshor /path/to/ForShor --working-tree

For each declaration in MANIFEST it extracts the body from both trees,
normalizes away comments, whitespace and the `Nat`/`Rat` spellings, and
compares. Deviations that are known and deliberate are listed in DEVIATIONS with
the reason, and are reported rather than counted as drift.

The companion path comes from the environment or the command line, so no URL is
recorded here. Nothing reaches the network.

Exit codes: 0 agreement, 1 drift found, 2 the check could not run.
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
IMPL = "FastMultiplication/ShorVerification/Implementation"

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
    "Layout.lean": (
        f"{IMPL}/PhaseProduct/Compiler/Layout.lean",
        [
            "WidthState",
            "updateWidthState",
            "NeededWidths",
            "mergeNeededWidths",
            "widthsOfState",
            "phaseLimbWidthOfWidth",
            "phaseLimbWidth",
            "isTopChunk",
            "phaseSplitLogicalWidth",
            "commonNeededWidth",
            "extraDelta",
        ],
    ),
    "Widths.lean": (
        f"{IMPL}/PhaseProduct/Compiler/Widths.lean",
        [
            "initWidthState",
            "scanNeededWidthsAux",
            "scanNeededWidths",
            "phaseInputSize",
            "nextSignedWidth",
        ],
    ),
    "Definitions.lean": (
        f"{IMPL}/GateCount/Definitions.lean",
        [
            "phaseArithmeticOpCost",
            "phaseProgramOverhead",
            "phaseOpWidthGrowth",
            "phaseProgramWidthGrowth",
        ],
    ),
    "Allocation.lean": (
        f"{IMPL}/PhaseProduct/Compiler/Compile.lean",
        [
            "allocChunkGate",
            "deallocChunkGate",
            "compileSignedAllocationsAux",
            "compileSignedAllocations",
            "compileSignedDeallocationsAux",
            "compileSignedDeallocations",
        ],
    ),
    "Allocation.lean:gates": (
        f"{FRAMEWORK}/AbstractMachine/Gates.lean",
        ["Gate"],
    ),
    "Allocation.lean:layout": (
        f"{IMPL}/PhaseProduct/Compiler/Layout.lean",
        ["LayoutState", "growExtRegTo", "targetSignedLayoutState"],
    ),
    "Allocation.lean:cost": (
        f"{IMPL}/GateCount/PhaseProduct/Lemmas.lean",
        ["BookkeepingGate", "bookkeepingGateCost"],
    ),
    "Registers.lean:algebra": (
        f"{FRAMEWORK}/Quantum/Registers.lean",
        ["take", "drop", "append", "CanGrow", "newBits", "remainingReserve",
         "grow", "ownedQubits", "OwnedDisjoint"],
    ),
    "ResourceModel.lean": (
        f"{FRAMEWORK}/Gatecount/ResourceModel.lean",
        [
            "rippleAdderGateBound",
            "negateGateBound",
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
    "Angle": "companion writes the Mathlib notation Q; Rat is the same type",
    "compileSignedAllocationsAux": (
        "the companion's generic order lemmas lt_of_lt_of_le / le_rfl are "
        "replaced by their Nat counterparts; the terms are defeq"
    ),
    "compileSignedDeallocationsAux": (
        "the companion's generic order lemmas lt_of_lt_of_le / le_rfl are "
        "replaced by their Nat counterparts; the terms are defeq"
    ),
    "compileSignedAllocations": "le_rfl replaced by Nat.le_refl; defeq",
    "compileSignedDeallocations": "le_rfl replaced by Nat.le_refl; defeq",
    "grow": "le_refl replaced by Nat.le_refl; defeq",
}

# Ours only: not from the companion, so nothing to compare against.
OURS_ONLY = {
    "slotExtReg",
    "slotExtReg_width",
    "slotExtReg_capacity",
    "canonicalLayoutState",
    "canonicalAllocationCost",
    "cuccaroModAddResources_totalGates_le_rippleAdderGateBound",
    "negateResourcesAtWidth_totalGates_le_negateGateBound",
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
    text = text.replace("<=", "≤").replace(">=", "≥")
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
        print("check_forshor_slice: no companion checkout given.\n"
              "  Pass --forshor <path> or set FORSHOR_ROOT.\n"
              "  This is a maintainer tool for re-checking the integrated slice "
              "against upstream;\n"
              "  the continuous guards on the cost model are the oracle's "
              "--width-scan and --allocation modes.",
              file=sys.stderr)
        return 2

    root = Path(args.forshor).expanduser()
    if not root.is_dir():
        print(f"check_forshor_slice: {root} is not a directory", file=sys.stderr)
        return 2

    commit = None if args.working_tree else args.commit
    repo = Path(__file__).resolve().parent.parent
    ok, deviated, drift, missing = 0, 0, [], []

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
            elif decl in DEVIATIONS:
                # a declared, deliberate difference -- reported, not drift
                deviated += 1
            else:
                drift.append((decl, relpath, normalize(theirs), normalize(ours)))

    print(f"companion: {root} @ {commit or 'working tree'}")
    print(f"agreement: {ok} declarations match, {deviated} differ as declared")
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
