#!/usr/bin/env python3
"""The banded harness and its memory cap were written against macOS only.

Both failed on Linux in a way that produced a plausible-looking answer instead
of an error, which is the reason these are pinned:

  * `check_banded_policy.py` staged its working copy with `cp -cR`. The `-c`
    flag is an APFS clone; GNU coreutils has no such flag and exits 1. The
    harness raised `CalledProcessError`, and a wrapper reading exit status
    scored that as a *rejected policy* rather than a broken run. Every banded
    policy looked refused, including the two that must be accepted.

  * `memcap.py` polled `top -l 1 -pid N -stats mem`, whose flags are macOS
    spellings. On Linux `top` rejected them, `mem()` returned 0 for every
    process, and the cap never fired however much the child allocated. A run
    logged `peak_gb: 0.0` while Lean held several GB.

A cap that cannot measure must refuse to run, not run uncapped.
"""
from __future__ import annotations

import json
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "scripts"))

import memcap  # noqa: E402
from check_banded_policy import CLONE  # noqa: E402


def test_clone_flags_match_the_platform():
    if sys.platform == "darwin":
        assert CLONE == ["cp", "-cR"]
    else:
        assert "-c" not in CLONE, f"APFS-only flag on {sys.platform}: {CLONE}"
        assert "--reflink=auto" in CLONE


def test_clone_command_actually_copies_a_tree():
    # The flags have to be accepted by *this* machine's cp, not just look right.
    with tempfile.TemporaryDirectory() as d:
        src, dst = Path(d) / "src", Path(d) / "dst"
        (src / "sub").mkdir(parents=True)
        (src / "sub" / "f.txt").write_text("content")
        subprocess.run(CLONE + [str(src), str(dst)], check=True)
        assert (dst / "sub" / "f.txt").read_text() == "content"


def test_memory_backend_reads_a_live_process():
    import os
    rss = memcap.mem(os.getpid())
    assert rss > 0, f"{memcap.mem.__name__} read {rss} for a live process; cap would never fire"


def test_memory_backend_returns_zero_for_a_dead_pid():
    assert memcap.mem(2 ** 22) == 0


def test_linux_backend_uses_pss_not_rss():
    """RSS summed over a tree double-counts shared pages.

    `lake`, `lean` and the poller all map the same Mathlib oleans. Charging
    those pages to each process in turn over-counted by 20% on a mid-size
    replay (4310 MB against a true 3596 MB), which tripped an 8 GB cap on a run
    holding about 7.4 GB and rejected a policy that should have been accepted.
    """
    if sys.platform == "darwin":
        return
    import os
    pid = os.getpid()
    rss = swap = 0
    with open(f"/proc/{pid}/status") as f:
        for l in f:
            if l.startswith("VmRSS:"):
                rss = int(l.split()[1]) * 1024
            elif l.startswith("VmSwap:"):
                swap = int(l.split()[1]) * 1024
    got = memcap.mem(pid)
    assert got <= rss + swap, f"reading {got} exceeds RSS+swap {rss + swap}"
    # This process maps libc and libpython, so some pages are shared and PSS
    # must come out strictly under RSS. Equality means RSS crept back in.
    assert got < rss + swap, "reading equals RSS+swap; PSS is not being used"


def test_the_cap_kills_a_process_that_exceeds_it():
    with tempfile.TemporaryDirectory() as d:
        hog, log = Path(d) / "hog.py", Path(d) / "log.json"
        hog.write_text(
            "import time\n"
            "x = []\n"
            "for _ in range(100):\n"
            "    x.append(bytearray(20 * 1024 * 1024))\n"
            "    time.sleep(0.1)\n"
            "print('NOT KILLED')\n"
        )
        p = subprocess.run(
            [sys.executable, str(ROOT / "scripts" / "memcap.py"),
             "--cap-gb", "0.25", "--timeout", "60", "--log", str(log),
             "--", sys.executable, str(hog)],
            capture_output=True, text=True, timeout=120,
        )
        assert "NOT KILLED" not in p.stdout, "hog outlived its cap"
        assert p.returncode == 137, f"expected 137, got {p.returncode}"
        rec = json.loads(log.read_text())
        assert rec["outcome"].startswith("killed: memory"), rec["outcome"]
        assert rec["peak_gb"] > 0, f"peak never measured: {rec}"


if __name__ == "__main__":
    tests = [v for k, v in sorted(globals().items()) if k.startswith("test_")]
    for t in tests:
        t()
        print(f"ok  {t.__name__}")
    print(f"\n{len(tests)} passed")
