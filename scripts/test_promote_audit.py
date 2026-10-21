#!/usr/bin/env python3
"""The promotion axiom audit must cover catalogue-only policies, not only
champions.

The planner searches every accepted PhaseProduct table, champion or not, so a
`sorry` or an unprovable `handles` in a catalogue-only table reaches the gate
count. Before this, promotion ran `#print axioms` and the `generate_safe`
re-check over champions alone, so such a table was installed and planned over
without ever being audited.

Run: python3 scripts/test_promote_audit.py
"""
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from scripts import promote  # noqa: E402


def _champion(module: str, k: int, mode: str = "PhaseProduct") -> dict:
    return {"module_id": module, "mode": mode, "k": k}


def _catalog(module: str, k: int) -> dict:
    # catalog_entries carries no mode; it is always CATALOG_MODE.
    return {"module_id": module, "k": k}


def test_catalog_only_module_is_audited():
    selections = [_champion("Pchamp", 4)]
    unbounded = [_catalog("Pchamp", 4), _catalog("Pcatalog", 4)]
    records = promote.audit_records(selections, unbounded)
    audited = {(r["module_id"], r["mode"], r["k"]) for r in records}
    assert ("Pcatalog", promote.CATALOG_MODE, 4) in audited, (
        "a catalogue-only table must be audited"
    )
    assert ("Pchamp", "PhaseProduct", 4) in audited


def test_duplicate_module_mode_k_is_collapsed():
    selections = [_champion("Pchamp", 4)]
    unbounded = [_catalog("Pchamp", 4)]
    records = promote.audit_records(selections, unbounded)
    keys = [(r["module_id"], r["mode"], r["k"]) for r in records]
    assert keys == [("Pchamp", "PhaseProduct", 4)], keys


def test_triple_product_champion_is_kept():
    # PhaseTripleProduct has no catalogue, so its champion must still be audited.
    selections = [_champion("Ptp", 3, mode="PhaseTripleProduct")]
    records = promote.audit_records(selections, [])
    audited = {(r["module_id"], r["mode"], r["k"]) for r in records}
    assert ("Ptp", "PhaseTripleProduct", 3) in audited


def test_every_audited_module_is_imported():
    # BestKnown imports champions only, so a catalogue-only module needs its own
    # import or the audit dies on an unknown identifier instead of auditing it.
    records = promote.audit_records([_champion("Pchamp", 4)], [_catalog("Pcat", 4)])
    source = promote.audit_source(records)
    imports = {line.split()[1] for line in source if line.startswith("import ")}
    for record in records:
        module = f"TableGeneration.Policies.Accepted.{record['module_id']}"
        assert module in imports, f"{module} is audited but never imported"


def test_imports_precede_commands():
    # Lean rejects an import after the first command.
    source = promote.audit_source(promote.audit_records([_champion("Pa", 4)], []))
    last_import = max(i for i, line in enumerate(source) if line.startswith("import "))
    first_cmd = min(i for i, line in enumerate(source) if line.startswith("#"))
    assert last_import < first_cmd, source


def test_records_are_ordered_deterministically():
    selections = [_champion("Pb", 5), _champion("Pa", 4)]
    unbounded = [_catalog("Pc", 6)]
    records = promote.audit_records(selections, unbounded)
    keys = [(r["module_id"], r["mode"], r["k"]) for r in records]
    assert keys == sorted(keys)


if __name__ == "__main__":
    tests = [v for k, v in sorted(globals().items()) if k.startswith("test_")]
    for t in tests:
        t()
        print(f"ok  {t.__name__}")
    print(f"\n{len(tests)} passed")
