#!/usr/bin/env python3
"""The parse-tree gate on submitted Lean sources.

`verify_no_banned_tokens` is a regex blocklist over text whose comments the
verifier strips itself. That has to re-implement Lean's lexer, and every
construct where a quote or a comment opener is data rather than a delimiter is
a chance to desynchronise from it. Five were found and patched by hand.

The gate in `scripts/ci/submission_syntax_gate.lean` parses with Lean's own
grammar instead and allowlists what comes back. These tests pin what that makes
possible and the regex does not, and the three bypasses an adversarial review
found in the first draft of the gate itself:

  * `debug.skipKernelTC`, which makes `addDecl` skip kernel typechecking. The
    propext-only axiom audit does NOT catch it -- the audit reports the axioms
    of a term the kernel never checked -- so before this gate nothing did. It
    has to be refused at command, term AND tactic level: those are three
    distinct syntax kinds.
  * a ceiling written in hex, or on the line after the option name. Lean's
    parser decodes the numeral; a regex over text does not.
  * any command outside the allowlist, at any position in the file. The first
    draft stopped after 10000 commands, so a submission could choose its own
    padding and hide `initialize` behind it.
  * `import A import B` on one physical line, which Lean takes as two imports
    and `verify_submission_imports`'s line-anchored regex takes as one.

The gate is NOT a superset of the blocklist: `sorry`, `axiom`, `unsafe`,
`extern`, `implemented_by` and `csimp` are a declaration or an attribute on
one, so the gate admits them by design and the blocklist still refuses them.
`test_the_gate_does_not_replace_the_blocklist` pins that division so neither
side is quietly dropped on the belief that the other covers it.

Needs a Lean checkout with a build tree, and runs `lake` in the CURRENT
directory, not in the directory this script lives in: in CI the trusted
verifier checkout holds this script and the gate, and the submission checkout
holds `.lake`. Run: python3 scripts/test_submission_syntax_gate.py
"""

from __future__ import annotations

import subprocess
import sys
import tempfile
from pathlib import Path

REPO = Path(__file__).resolve().parents[1]
GATE = REPO / "scripts" / "ci" / "submission_syntax_gate.lean"
# The built checkout `lake` runs in. Separate from REPO: see the module docstring.
WORK = Path.cwd()
HEADER = "import TableGeneration.Policy\n"


def run_paths(*paths: str | Path) -> tuple[int, str]:
    done = subprocess.run(
        ["lake", "env", "lean", "--run", str(GATE), *(str(p) for p in paths)],
        cwd=WORK, text=True, capture_output=True, timeout=900,
    )
    return done.returncode, done.stdout + done.stderr


def run_gate(*sources: str) -> tuple[int, str]:
    with tempfile.TemporaryDirectory() as tmp:
        paths = []
        for i, src in enumerate(sources):
            p = Path(tmp) / f"case{i}.lean"
            p.write_text(src, encoding="utf-8")
            paths.append(p)
        return run_paths(*paths)


def test_the_production_file_set_is_clean() -> None:
    # Through verifier.py, so the file set under test is the one CI actually
    # passes to the gate rather than a hand-picked list.
    sys.path.insert(0, str(REPO / "scripts"))
    import verifier

    result = verifier.verify_submission_syntax(WORK)
    assert result["status"] == "success", result["details"]


def test_every_accepted_policy_is_clean() -> None:
    # Real paths, not copies: a helper under Policy/ has to still be judged
    # clean where it sits, with the imports it really has.
    policies = sorted((REPO / "TableGeneration/Policies/Accepted").glob("**/*.lean"))
    assert policies, "no accepted policies found"
    rc, out = run_paths(*policies)
    assert rc == 0, out


def test_kernel_typecheck_cannot_be_skipped() -> None:
    # The one the regex scanner and the axiom audit both miss. All three
    # syntactic positions `set_option` has.
    for src in [
        "set_option debug.skipKernelTC true in\ntheorem t : 1 = 1 := rfl\n",
        "def b : Nat := set_option debug.skipKernelTC true in 1\n",
        "example : True := by set_option debug.skipKernelTC true in trivial\n",
    ]:
        rc, out = run_gate(HEADER + src)
        assert rc == 1, f"admitted: {src}"
        assert "debug.skipKernelTC" in out and "not permitted" in out, out


def test_ceilings_bind_at_term_and_tactic_level() -> None:
    # A ceiling enforced on commands alone is not enforced: the same option
    # reaches elaboration through a term and through a tactic.
    for src in [
        "def a : Nat := set_option maxHeartbeats 0 in 1\n",
        "example : True := by set_option maxRecDepth 100000000 in trivial\n",
    ]:
        rc, out = run_gate(HEADER + src)
        assert rc == 1, f"admitted: {src}"
        assert "ceiling" in out, out


def test_a_payload_behind_padding_is_still_seen() -> None:
    # The first draft broke out of the parse loop after 10000 commands, which
    # let a submission pick a padding length and hide anything after it.
    padding = "\n".join(f"def f{i} : Nat := {i}" for i in range(10002))
    for payload, needle in [
        ("set_option debug.skipKernelTC true in\ntheorem evil : 1 = 1 := rfl\n", "debug.skipKernelTC"),
        ('open Nat in initialize zz : Nat <- (IO.println "x" *> pure 1)\n', "initialize"),
    ]:
        rc, out = run_gate(f"{HEADER}{padding}\n{payload}")
        assert rc == 1, f"padding hid the payload: {needle}"
        assert needle in out, out


def test_two_imports_on_one_line_are_both_read() -> None:
    # Lean takes both; the verifier's line-anchored regex takes only the first.
    rc, out = run_gate("import TableGeneration.Policy import Mathlib\ndef w : Nat := 1\n")
    assert rc == 1, out
    assert "Mathlib" in out and "not permitted" in out, out


def test_hex_heartbeat_ceiling_is_decoded() -> None:
    rc, out = run_gate(HEADER + "set_option maxHeartbeats 0x7FFFFFFF in\ndef a : Nat := 1\n")
    assert rc == 1, out
    assert "2147483647" in out, f"the parsed value should be reported, got: {out}"


def test_heartbeat_ceiling_on_the_next_line_is_caught() -> None:
    rc, out = run_gate(HEADER + "set_option maxHeartbeats\n  100000000000 in\ndef a : Nat := 1\n")
    assert rc == 1, out
    assert "100000000000" in out, out


def test_zero_heartbeats_is_refused() -> None:
    # 0 means "no ceiling", so it must not pass the `<= ceiling` test.
    rc, out = run_gate(HEADER + "set_option maxHeartbeats 0 in\ndef a : Nat := 1\n")
    assert rc == 1, out


def test_values_the_archive_uses_are_allowed() -> None:
    rc, out = run_gate(
        HEADER + "set_option maxHeartbeats 1000000000 in\nset_option maxRecDepth 100000 in\ndef a : Nat := 1\n"
    )
    assert rc == 0, out


def test_ordinary_lean_structure_is_allowed() -> None:
    # The allowlist is a trust boundary, not a style guide. `section`,
    # `variable` and `mutual` are everyday Lean and a policy may need them.
    rc, out = run_gate(
        HEADER
        + "namespace N\nsection\nvariable (n : Nat)\nuniverse u\n"
        + "mutual\n  def ev : Nat -> Bool | 0 => true | n+1 => od n\n"
        + "  def od : Nat -> Bool | 0 => false | n+1 => ev n\nend\n"
        + "end\nend N\n"
    )
    assert rc == 0, out


def test_compile_time_commands_are_refused() -> None:
    for src, needle in [
        ("#eval (1 : Nat)\n", "eval"),
        ('macro "boom" : term => `(1)\n', "macro"),
        ("initialize x : Nat ← pure 1\n", "initialize"),
        ("attribute [simp] Nat.add_zero\n", "attribute"),
    ]:
        rc, out = run_gate(HEADER + src)
        assert rc == 1, f"{needle} was allowed: {out}"
        assert "not permitted" in out, out


def test_a_file_that_does_not_parse_is_refused() -> None:
    # The gate cannot judge what it cannot read, so it refuses rather than passes.
    rc, out = run_gate(HEADER + "def a : Nat := ((((\n")
    assert rc == 1, out


def test_the_gate_does_not_replace_the_blocklist() -> None:
    # These are a declaration or an attribute on one, so the gate admits them.
    # The regex blocklist is the only thing refusing them, and this records
    # that division so neither layer is dropped believing the other covers it.
    sys.path.insert(0, str(REPO / "scripts"))
    import verifier

    for src in [
        "theorem t : 1 = 1 := by sorry\n",
        "axiom cheat : 1 = 2\n",
        "unsafe def u : Nat := 1\n",
        '@[extern "lean_evil"] opaque ev : Nat\n',
        "@[csimp] theorem pq : True = True := rfl\n",
        "theorem n : 1 = 1 := by native_decide\n",
    ]:
        rc, _ = run_gate(HEADER + src)
        assert rc == 0, f"the gate now refuses {src!r}; move it out of this test"
        assert any(
            p.search(src) for p in verifier.BANNED_PATTERNS.values()
        ), f"nothing refuses {src!r}"


if __name__ == "__main__":
    tests = [v for k, v in sorted(globals().items()) if k.startswith("test_")]
    failures = 0
    for t in tests:
        try:
            t()
            print(f"ok    {t.__name__}")
        except Exception as exc:  # noqa: BLE001
            failures += 1
            print(f"FAIL  {t.__name__}\n{exc}")
    print(f"\n{len(tests) - failures} passed, {failures} failed")
    sys.exit(1 if failures else 0)
