#!/usr/bin/env python3
"""The policy `name` field is the one untrusted string that reaches Lean text.

Every other value a policy JSON carries is validated before it is emitted:
`nat` rejects anything that is not a non-negative int, `op_lean` whitelists the
operation names and routes each argument through `fin`/`nat`, and `point_lean`
re-emits an int it parsed itself from an anchored `fullmatch`. `module` and
`data_module` must match `IDENT`.

`name` is different -- it is copied into the `/-! ... -/` banner comment the
generators put at the top of each file. `json.dumps` escapes quotes,
backslashes and newlines, but it does not escape the Lean comment delimiters,
so a name containing `-/` closed the banner and turned everything after it into
live code. A policy could carry its own `axiom` that way and discharge any
obligation the harness asked it to prove.

`lean_comment` closes that by breaking both delimiters. These tests pin the
invariant for the three generators that emit a banner.
"""
from __future__ import annotations

import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from policy_json_to_lean import lean_comment  # noqa: E402

ATTACKS = [
    'golden reference -/ axiom injected_cheat : False /- rest',
    '-/',
    '/-',
    '-/-',
    '/-/',
    '--//',
    'a -/ b /- c -/ d',
    '-' * 50 + '/' * 50,
    '\\-/',
    '"-/"',
]


def test_no_delimiter_survives():
    for raw in ATTACKS:
        out = lean_comment(raw, 200)
        assert "-/" not in out, f"comment closer survived {raw!r}: {out}"
        assert "/-" not in out, f"comment opener survived {raw!r}: {out}"


def test_truncation_cannot_reintroduce_a_delimiter():
    # Truncating to `limit` must not slice a replacement apart and leave a
    # delimiter at the boundary.
    for raw in ATTACKS:
        for limit in range(1, 60):
            out = lean_comment(raw, limit)
            assert "-/" not in out, f"closer at limit={limit} for {raw!r}: {out}"
            assert "/-" not in out, f"opener at limit={limit} for {raw!r}: {out}"


def test_ordinary_names_are_left_readable():
    for raw in ["ref_pp_2048", "k=5 six band", "width 2048 (exact)"]:
        assert raw in lean_comment(raw, 200)


def test_json_escaping_is_still_applied():
    out = lean_comment('a"b\nc\\d', 200)
    for ch in ('"', "\n", "\\"):
        assert ch not in out[1:-1] or out.count("\\") > 0
    assert "\n" not in out


def test_every_generator_banner_uses_the_helper():
    # A fourth generator added later must not reintroduce the raw json.dumps
    # banner. Pin that no script interpolates into `/-!` without the helper.
    scripts = Path(__file__).resolve().parent
    offenders = []
    for py in scripts.glob("*.py"):
        if py.name == Path(__file__).name:
            continue
        for n, line in enumerate(py.read_text().splitlines(), 1):
            if "/-!" in line and "json.dumps" in line:
                offenders.append(f"{py.name}:{n}")
    assert not offenders, f"raw json.dumps in a Lean banner: {offenders}"


if __name__ == "__main__":
    tests = [v for k, v in sorted(globals().items()) if k.startswith("test_")]
    for t in tests:
        t()
        print(f"ok  {t.__name__}")
    print(f"\n{len(tests)} passed")
