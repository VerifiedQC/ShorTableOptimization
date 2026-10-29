#!/usr/bin/env python3
"""Cross-check the mirror's exact ("tight") width ladder against sto_site's
`engine/paper_model/forshor_qualtran/tight_width.py` (loaded read-only by file path;
nothing in sto_site is written).

    python3 scripts/crosscheck_tight_width.py POLICY.json [POLICY.json ...] \
        [--target-width 2048] [--index I] [--lean-record RECORD.json ...] \
        [--sto-site PATH] [--out OUT.json]

For each policy it walks the banded recursion from the target width (ForShor `choose`:
first band with threshold <= w; recurse while the next width is < w) under four width rules:

  mirror_exact   scripts/exact_width.py, the transcription of `PolicyTable.tightWidth` (Tight.lean):
                 floor limbs (lower k-1 limbs unsigned n//k bits, top limb signed, the
                 remainder), every register of every prefix-reachable state, exact intervals
  site_floor     tight_width.tight_width_closed_form(ops, k, w)            (same limbs)
  site_padded    tight_width.tight_width_closed_form(ops, k, k*ceil(w/k))  (rule R2's
                 zero-extension to a multiple of k, = TightRule.at_n on the uniform ladder)
  scan           width_scan.next_width(ops, k, w) (= STO nextSignedWidth n n, Lean's scan)

and, when a harness record with report.tight_ladder / report.ladder is given, compares the
Lean-evaluated ladders with mirror_exact / scan. Exit 1 on any mismatch between
mirror_exact, site_floor and the Lean tight ladder (or between scan and the Lean ladder).
"""
from __future__ import annotations

import argparse
import importlib.util
import json
import sys
from pathlib import Path

DEFAULT_STO_SITE = Path(__file__).resolve().parent.parent.parent / "sto_site"  # sibling checkout; pass --sto-site


def load(path: Path, name: str):
    sys.dont_write_bytecode = True  # read-only on sto_site: no __pycache__ written there
    spec = importlib.util.spec_from_file_location(name, path)
    mod = importlib.util.module_from_spec(spec)
    sys.modules[name] = mod
    spec.loader.exec_module(mod)
    return mod


def ops_to_dicts(ops):
    out = []
    for o in ops:
        n = o[0]
        if n == "addScaled":
            out.append({"op": "addScaled", "dst": o[1], "src": o[2], "negSrc": o[3] == -1, "shift": o[4]})
        elif n in ("shiftL", "shiftR"):
            out.append({"op": n, "i": o[1], "n": o[2]})
        else:
            out.append({"op": n, "i": o[1]})
    return out


# ---------------------------------------------------------------- the mirror's definition
sys.path.insert(0, str(Path(__file__).resolve().parent))
from exact_width import exact_width as mirror_tight_raw  # noqa: E402  (transcription of Tight.lean)


def mirror_tight(k, ops, n):
    return mirror_tight_raw(k, ops, n)


# ---------------------------------------------------------------- ladders
def choose(bands, w):
    for b in bands:
        if b["threshold"] <= w:
            return b
    return None


def walk(bands, n, nxt):
    out = []
    w = n
    for _ in range(n + 2):
        b = choose(bands, w)
        if b is None:
            out.append({"width": w, "k": None})
            return out
        w2 = nxt(b, w)
        if not w2 < w:
            out.append({"width": w, "k": None})
            return out
        out.append({"width": w, "k": b["k"]})
        w = w2
    raise RuntimeError("ladder did not terminate")


def ladders(policy, n, tw, ws):
    bands = policy["bands"]
    for b in bands:
        b["_d"] = ops_to_dicts(b["operations"])
    rules = {
        "mirror_exact": lambda b, w: mirror_tight(b["k"], b["operations"], w),
        "site_floor": lambda b, w: tw.tight_width_closed_form(b["_d"], b["k"], w),
        "site_padded": lambda b, w: tw.tight_width_closed_form(b["_d"], b["k"], b["k"] * -(-w // b["k"])),
        "scan": lambda b, w: ws.next_width(b["_d"], b["k"], w),
    }
    out = {name: walk(bands, n, f) for name, f in rules.items()}
    # pointwise: at every width of the exact chain, all four next-width rules
    out["pointwise_on_exact_chain"] = [
        {"width": r["width"], "k": r["k"],
         **({name: f(choose(bands, r["width"]), r["width"]) for name, f in rules.items()} if r["k"] else {})}
        for r in out["mirror_exact"]]
    for b in bands:
        del b["_d"]
    return out


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("policies", nargs="+")
    ap.add_argument("--target-width", type=int, default=2048)
    ap.add_argument("--index", type=int)
    ap.add_argument("--lean-record", nargs="*", default=[])
    ap.add_argument("--sto-site", default=str(DEFAULT_STO_SITE))
    ap.add_argument("--out")
    ap.add_argument("--pin", help="also write a compact per-policy pin (verdict, Lean exact ladder, scan, "
                    "site floor/padded ladders, replay peaks, axioms) for the site to consume")
    a = ap.parse_args(argv)
    fq = Path(a.sto_site) / "engine/paper_model/forshor_qualtran"
    tw = load(fq / "tight_width.py", "_sto_tight_width")
    ws = load(fq / "width_scan.py", "_sto_width_scan")
    recs = {}
    for r in a.lean_record:
        d = json.loads(Path(r).read_text())
        recs[d.get("policy_sha256")] = d
    import hashlib
    results, bad = [], 0
    for p in a.policies:
        raw = Path(p).read_bytes()
        doc = json.loads(raw)
        if a.index is not None:
            doc = doc["policies"][a.index]["policy"]
        elif "policy" in doc and "bands" not in doc:
            doc = doc["policy"]
        lad = ladders(doc, a.target_width, tw, ws)
        widths = {k: [r["width"] for r in v] for k, v in lad.items() if k != "pointwise_on_exact_chain"}
        ok = widths["mirror_exact"] == widths["site_floor"]
        entry = {"policy": p, "sha256": hashlib.sha256(raw).hexdigest(), "mode": doc.get("mode"),
                 "ladders": widths, "exact_ladder": lad["mirror_exact"],
                 "pointwise_on_exact_chain": lad["pointwise_on_exact_chain"],
                 "mirror_eq_site_floor": ok}
        rec = recs.get(entry["sha256"])
        if rec and "report" in rec:
            lt = rec["report"].get("tight_ladder")
            if lt is not None:
                entry["lean_tight_eq_mirror"] = [r["width"] for r in lt] == widths["mirror_exact"] and \
                    [r["k"] for r in lt] == [r["k"] for r in lad["mirror_exact"]]
                ok = ok and entry["lean_tight_eq_mirror"]
            entry["lean_scan_eq_site_scan"] = [r["width"] for r in rec["report"]["ladder"]] == widths["scan"]
            ok = ok and entry["lean_scan_eq_site_scan"]
        entry["ok"] = ok
        entry["_rec"] = rec
        bad += not ok
        results.append(entry)
    if a.pin:
        pins = []
        for e in results:
            rec = e["_rec"] or {}
            pins.append({
                "policy": e["policy"], "policy_sha256": e["sha256"], "mode": e["mode"],
                "verdict": rec.get("verdict"), "rejection": rec.get("rejection"),
                "widths_rule": rec.get("widths_rule"),
                "exact_ladder": rec.get("exact_ladder"),
                "exact_ladder_kernel_proved": "exact_ladder" in rec.get("audit", {}),
                "scan_ladder": rec.get("scan_ladder") or (rec.get("report") or {}).get("ladder"),
                "declared_ladder": rec.get("declared_ladder"),
                "site_tight_width_py_floor": e["ladders"]["site_floor"],
                "site_tight_width_py_padded": e["ladders"]["site_padded"],
                "lean_exact_eq_site_floor": e.get("lean_tight_eq_mirror", None) and e["mirror_eq_site_floor"],
                "theorems": {k: v["axioms"] for k, v in rec.get("audit", {}).items()},
                "replay_peak_gb": [m.get("peak_gb") for m in (rec.get("replay") or {}).get("modules", [])],
                "lean_sha256": rec.get("lean_sha256"),
                "seconds": rec.get("seconds"),
            })
        Path(a.pin).write_text(json.dumps({"tool": "crosscheck_tight_width --pin", "target_width": a.target_width,
                                           "rule": "exact = PolicyTable.tightWidth (Tight.lean), floor limbs",
                                           "runs": pins}, indent=1))
    for e in results:
        del e["_rec"]
    out = json.dumps({"tool": "crosscheck_tight_width", "target_width": a.target_width,
                      "sto_site_files": [str(fq / "tight_width.py"), str(fq / "width_scan.py")],
                      "results": results, "all_ok": bad == 0}, indent=1)
    if a.out:
        Path(a.out).write_text(out)
    print(out)
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
