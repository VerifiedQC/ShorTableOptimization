#!/usr/bin/env python3
"""Run a command under a hard memory cap and a timeout.

    memcap.py --cap-gb 10 --timeout 1800 --log run.mem.json -- CMD ARGS...

Polls every second the memory of the whole process tree and kills the tree when
the sum exceeds the cap or the timeout passes. Writes peak memory, wall time
and outcome to --log. Exit code: the command's, or 137 if killed.

Counts resident plus the pages the process still owns that RSS alone hides:
compressed memory on macOS (`top -stats mem`), swap on Linux (`VmSwap` in
/proc). A reading of 0 for a live process means the cap is not being enforced,
so the probe at startup fails loudly rather than running uncapped.
"""
import argparse, json, os, re, signal, subprocess, sys, time

UNITS = {"B": 1, "K": 1 << 10, "M": 1 << 20, "G": 1 << 30}


def tree(pid):
    out = subprocess.run(["ps", "-A", "-o", "pid=,ppid="], capture_output=True, text=True).stdout
    kids = {}
    for line in out.splitlines():
        p, pp = map(int, line.split())
        kids.setdefault(pp, []).append(p)
    seen, stack = [], [pid]
    while stack:
        p = stack.pop()
        seen.append(p)
        stack.extend(kids.get(p, []))
    return seen


def mem_darwin(pid):
    out = subprocess.run(["top", "-l", "1", "-pid", str(pid), "-stats", "mem"], capture_output=True, text=True).stdout
    vals = re.findall(r"^\s*([\d.]+)([BKMG])\+?-?\s*$", out, re.M)
    return int(float(vals[-1][0]) * UNITS[vals[-1][1]]) if vals else 0


def mem_linux(pid):
    """Proportional set size plus swap, in bytes.

    PSS, not RSS: these totals are summed over a process tree, and `lake`,
    `lean` and this poller all map the same Mathlib oleans. RSS charges every
    shared page to each process that maps it, so summing RSS over the tree
    counts those pages two or three times -- measured at 4310 MB against a true
    3596 MB on a mid-size replay, a 20% over-count, which is enough to trip an
    8 GB cap on a run holding about 7.4 GB. PSS divides each shared page by the
    number of sharers, so the sum is right.
    """
    try:
        total = 0
        try:
            with open(f"/proc/{pid}/smaps_rollup") as f:
                for l in f:
                    if l.startswith("Pss:"):
                        total += int(l.split()[1]) * 1024
                        break
        except OSError:
            # smaps_rollup needs kernel >= 4.14 and the right privileges.
            # RSS over-counts shared pages; better that than no reading at all.
            with open(f"/proc/{pid}/status") as f:
                for l in f:
                    if l.startswith("VmRSS:"):
                        total += int(l.split()[1]) * 1024
                        break
        with open(f"/proc/{pid}/status") as f:
            for l in f:
                if l.startswith("VmSwap:"):
                    total += int(l.split()[1]) * 1024
                    break
        return total
    except (OSError, ValueError, IndexError):
        return 0  # exited between listing the tree and reading it


mem = mem_darwin if sys.platform == "darwin" else mem_linux


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--cap-gb", type=float, default=10)
    ap.add_argument("--timeout", type=float, default=1800)
    ap.add_argument("--log")
    ap.add_argument("cmd", nargs=argparse.REMAINDER)
    a = ap.parse_args()
    cmd = a.cmd[1:] if a.cmd and a.cmd[0] == "--" else a.cmd
    cap = int(a.cap_gb * (1 << 30))
    if mem(os.getpid()) <= 0:
        sys.exit(f"memcap: cannot read memory on {sys.platform} via {mem.__name__}; "
                 f"refusing to run uncapped")
    t0 = time.monotonic()
    p = subprocess.Popen(cmd, start_new_session=True)
    peak, outcome = 0, None
    while p.poll() is None:
        total = sum(mem(q) for q in tree(p.pid))
        peak = max(peak, total)
        if total > cap:
            outcome = f"killed: memory {total / (1 << 30):.2f} GB > cap {a.cap_gb} GB"
        elif time.monotonic() - t0 > a.timeout:
            outcome = f"killed: timeout {a.timeout} s"
        if outcome:
            os.killpg(p.pid, signal.SIGKILL)
            p.wait()
            break
        time.sleep(1)
    rc = 137 if outcome else p.returncode
    rec = {"cmd": cmd, "exit": rc, "outcome": outcome or "finished", "peak_gb": round(peak / (1 << 30), 2),
           "seconds": round(time.monotonic() - t0, 1), "cap_gb": a.cap_gb}
    if a.log:
        with open(a.log, "w") as f:
            json.dump(rec, f)
    print(json.dumps(rec), file=sys.stderr)
    sys.exit(rc)


if __name__ == "__main__":
    main()
