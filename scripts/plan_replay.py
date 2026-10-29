#!/usr/bin/env python3
"""Kernel-replay the planner modules (one module per process, memcap) and write a statement pin.

    plan_replay.py --out runs/plan_from_site/replay_plan.json
"""
import argparse, hashlib, json, re, sys
from pathlib import Path
HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import plan_from_site as pf  # noqa: E402

MODS = [(pf.ROOT, "TableGeneration.RecursiveCost.PlanCore"),
        (pf.ROOT, "TableGeneration.RecursiveCost.BandedPolicy.Plan"),
        (pf.DEFAULT_PTP_ROOT, "TableGeneration.RecursiveCost.PlanCore"),
        (pf.DEFAULT_PTP_ROOT, "TableGeneration.RecursiveCost.PTP.Plan")]
HEADLINE = {"plan_check", "plan_check_of_all", "plan_correct", "plan_correct_reg", "plan_correct_w", "plan_correct_tight",
            "plan_ladder", "plan_choose_visit", "plan_sorted", "plan_bands_mem", "plan_ne_of_unsorted",
            "plan_ne_of_foreign", "planWith_check", "chooseL_merge", "merge_sorted", "walk_sorted", "ladder_walk",
            "chooseL_planList_visit", "ladder_planList"}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--out", required=True)
    ap.add_argument("--cap-gb", type=float, default=8)
    a = ap.parse_args()
    res = []
    for root, mod in MODS:
        nonce = pf.secrets.token_hex(8)
        rc, out, mem = pf.capped(["lake", "env", "lean", "--run", "scripts/trusted/ReplayPrefix.lean", "--", nonce,
                                  mod, mod], root, a.cap_gb, 1800)
        lines = out.splitlines()
        if f"AF_TRUSTED_{nonce}" not in lines:
            res.append({"root": root.name, "module": mod, "verdict": "no trusted output", "mem": mem,
                        "tail": out[-1500:]})
            continue
        rj = json.loads(lines[lines.index(f"AF_TRUSTED_{nonce}") + 1])
        thms = rj.get("theorems", [])
        pin = {t["name"]: {"type": t["type"], "axioms": sorted(t["axioms"]), "sorry": t["sorry"],
                           "sha256": hashlib.sha256(re.sub(r"\s+", " ", t["type"]).encode()).hexdigest()}
               for t in thms if t["name"].rsplit(".", 1)[-1] in HEADLINE}
        res.append({"root": root.name, "module": mod, "verdict": rj.get("verdict"), "decls": rj.get("decls"),
                    "theorems": len(thms), "axioms": sorted({x for t in thms for x in t["axioms"]}),
                    "sorry": any(t["sorry"] for t in thms), "peak_gb": mem.get("peak_gb"),
                    "seconds": mem.get("seconds"), "pin": pin})
        print(json.dumps({k: v for k, v in res[-1].items() if k != "pin"}), flush=True)
    Path(a.out).write_text(json.dumps(res, indent=1, ensure_ascii=False))


if __name__ == "__main__":
    main()
