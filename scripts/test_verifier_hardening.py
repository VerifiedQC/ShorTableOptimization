#!/usr/bin/env python3
"""Regression tests for verifier banned-token scanner hardening.

Run: python3 scripts/test_verifier_hardening.py

Covers the hardening fixes:
  1. `strip_lean_comments` is literal-aware across string, raw-string and
     character literals, so a banned token cannot be hidden from the scanner by
     bracketing it between `"/-"` ... `"-/"` literals, nor by using a `'"'`
     character literal to flip the scanner's idea of where strings begin (Lean
     parses those as data and the token as live code, so an unaware stripper
     silently deletes the token from the scan -- a false negative that is a
     compile-time code-execution hole, since the preflight scan is the only gate
     before untrusted Lean is built).
  2. `native_decide` and the `decide +native` option are banned (non-kernel
     computation path).
  3. The compile-time-execution scan catches metaprogramming commands behind a
     modifier or attribute (`local macro`, `@[x] elab`) and the notation family
     (`macro_rules`, `notation`, ...).
  4. `set_option maxHeartbeats 0` (and absurd finite ceilings) are rejected.
"""
import importlib.util
from pathlib import Path

_spec = importlib.util.spec_from_file_location(
    "verifier", Path(__file__).with_name("verifier.py")
)
verifier = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(verifier)


def scan(text: str) -> list[str]:
    stripped = verifier.strip_lean_comments(text)
    return [label for label, pat in verifier.BANNED_PATTERNS.items() if pat.search(stripped)]


def test_plain_banned_token_is_flagged():
    assert scan("def a := 1\n@[implemented_by foo] def b := 2\n")


def test_string_bracketed_token_is_flagged():
    # The core regression: token hidden between "/-" ... "-/" string literals.
    src = 'def s1 : String := "/-"\n@[implemented_by foo] def b := 2\ndef s2 : String := "-/"\n'
    assert scan(src), "banned token bracketed by string literals must still be caught"


def test_legit_string_with_comment_markers_is_not_flagged():
    # A legitimate string containing comment-like text is data, not a banned token,
    # and code after it must not be swallowed.
    assert scan('def s : String := "/- just data -/"\ndef g := 3\n') == []


def test_native_decide_is_flagged():
    assert "non-kernel computation" in scan("theorem t : True := by native_decide\n")


def test_decide_plus_native_is_flagged():
    assert "non-kernel computation" in scan("theorem t : True := by decide +native\n")


def test_char_literal_bypass_is_flagged():
    # The character literal `'"'` is a single double-quote CHARACTER. An unaware
    # stripper reads that `"` as opening a string, so every later `"` is
    # inverted: the `"x /-"` string's closing quote is seen as an opener, the
    # attacker's `/-` becomes a real comment, and the #eval between the literals
    # is dropped from the scan while Lean still runs it.
    src = (
        "def dq : Char := '\"'\n"
        'def a : String := "x /-"\n'
        '#eval IO.println "pwned"\n'
        'def z : String := "-/ y"\n'
    )
    assert "compile-time execution" in scan(src), (
        "a #eval hidden behind a '\"' character literal must still be caught"
    )


def test_raw_string_bypass_is_flagged():
    # A raw string `r"..."` takes no escapes and ends at the first `"`, so an
    # unaware stripper that looks for an escaped-quote close desynchronises.
    src = 'def a := r"/-"\n#eval IO.println "x"\ndef z := r"-/"\n'
    assert "compile-time execution" in scan(src)


def test_escaped_quote_char_literal_bypass_is_flagged():
    # `'\''` is an escaped-single-quote CHARACTER. A stripper that finds the
    # close starting at the escaped char mistakes it for the terminator and
    # leaves a stray `'`, which then eats a following string's opening quote and
    # desynchronises -- hiding the #eval between the literals.
    src = "'\\''\"'/-\"\n#eval IO.println \"pwned\"\n"
    assert "compile-time execution" in scan(src), (
        "a #eval hidden behind an escaped-quote char literal must be caught"
    )


def test_identifier_r_prefix_is_not_a_raw_string():
    # `xr"..."` is one identifier `xr` then an ORDINARY string, where `\"` does
    # not close the string. Reading `r"..."` as raw here closes early and
    # desynchronises.
    src = 'def a := xr"b\\"/-"\n#eval IO.println "x"\ndef z := "-/"\n'
    assert "compile-time execution" in scan(src)


def test_various_escaped_char_literals_do_not_desync():
    # Each is a legitimate escaped character literal followed by live code with a
    # banned token; the token must still be seen.
    for lit in ("'\\n'", "'\\\\'", "'\\t'", "'\\u00ab'", "'\\x27'", "'\\\"'"):
        src = f"def c : Char := {lit}\ntheorem t : False := sorry\n"
        assert "sorry/admit" in scan(src), f"desync after {lit!r}"


def test_guillemet_identifier_bypass_is_flagged():
    # `«x/-»` is one Lean identifier; the scanner must not read the
    # `/-` inside it as a comment opener and swallow the code after it. Lean runs
    # the #eval here, so the scan has to catch it, at every placement.
    for src in (
        "def «x/-» := 0\n#eval danger\n",
        "theorem «t/-» : False := sorry\n",
        "def a := «f/-»\n#eval danger\n",
        "namespace «N/-»\n#eval danger\nend «N/-»\n",
    ):
        hits = scan(src)
        assert ("compile-time execution" in hits) or ("sorry/admit" in hits), (
            f"guillemet bypass not caught: {src!r}"
        )


def test_legit_guillemet_identifier_is_not_flagged():
    assert scan("def «my name» := 1\ndef g := 2\n") == []
    assert "sorry/admit" in scan(
        "def «ok» := 1\ntheorem t : False := sorry\n"
    )


def test_legit_char_literals_do_not_hide_tokens():
    # Ordinary character literals are data and must neither be flagged nor
    # swallow a following banned token.
    assert scan("def c : Char := 'a'\ndef g := 3\n") == []
    assert "sorry/admit" in scan("def c : Char := 'a'\ntheorem t : False := sorry\n")


def test_identifier_prime_is_not_a_char_literal():
    # A trailing prime on an identifier (`h'`) must not be read as an unterminated
    # character literal and swallow the rest of the file.
    assert "sorry/admit" in scan("theorem t (h' : True) : False := sorry\n")


def test_modified_metaprogram_commands_are_flagged():
    for src in (
        "local macro \"x\" : term => `(1)\n",
        "scoped syntax \"s\" : term => `(1)\n",
        "@[inline] elab \"e\" : term => pure default\n",
        "macro_rules | `(x) => `(1)\n",
        "elab_rules : term | `(y) => pure default\n",
        'notation "Q" => True\n',
    ):
        assert "compile-time execution" in scan(src), f"not flagged: {src!r}"


def test_disable_heartbeats_is_flagged():
    assert "unbounded elaboration" in scan("set_option maxHeartbeats 0 in\n")
    assert "unbounded elaboration" in scan("set_option maxHeartbeats 100000000000 in\n")


def test_real_heartbeat_limits_are_allowed():
    # The values the real archive uses must stay admissible.
    assert scan("set_option maxHeartbeats 10000000\n") == []
    assert scan("set_option maxHeartbeats 1000000000\n") == []


def test_ordinary_declarations_are_not_flagged():
    # Identifiers that merely contain a banned keyword as a substring, and a
    # `prefixSum` def, must not trip the command scan.
    assert scan("def prefixSum := 0\ndef macroExpansionNote := 1\n") == []


def test_real_comments_are_still_stripped():
    # sorry/axiom genuinely inside comments must not be flagged (no false positives).
    src = "def a := 1 -- sorry this is a comment\n/- axiom hidden -/\ndef b := 2\n"
    assert scan(src) == []


if __name__ == "__main__":
    tests = [v for k, v in sorted(globals().items()) if k.startswith("test_")]
    for t in tests:
        t()
        print(f"ok  {t.__name__}")
    print(f"\n{len(tests)} passed")
