#!/usr/bin/env python3
"""Rebuild the reader whenever new Lean work is pushed.

    python3 site/watch.py --lean-repo PATH_TO_A_CLONE [--interval 120]

Every interval, fetches `origin` in the given clone of the project (any clone
works; a clone outside iCloud-synced folders avoids stalls on offloaded git
objects) and, when `origin/main` has moved, rebuilds `site/_build/` from that
commit. The rebuild swaps in atomically, so a server pointed at `site/_build/`
always serves a complete site. The fidelity check runs once at start-up; it
compares the site with the pinned book, which new Lean work does not change.
Stop with Ctrl-C.
"""

from __future__ import annotations

import argparse
import subprocess
import sys
import time
from datetime import datetime
from pathlib import Path

HERE = Path(__file__).resolve().parent


def git(repo: Path, *args: str) -> str:
    return subprocess.run(["git", "-C", str(repo), *args], capture_output=True, text=True,
                          check=True, timeout=120).stdout.strip()


def log(msg: str) -> None:
    print(f"[{datetime.now().strftime('%Y-%m-%d %H:%M:%S')}] {msg}", flush=True)


def build(repo: Path, rev: str) -> bool:
    r = subprocess.run([sys.executable, "-I", str(HERE / "build.py"), "--lean-repo", str(repo), "--rev", rev],
                       capture_output=True, text=True)
    tail = "\n".join((r.stdout + r.stderr).strip().splitlines()[-4:])
    log(("rebuilt" if r.returncode == 0 else "BUILD FAILED, previous site kept") + f" for {rev[:10]}\n{tail}")
    return r.returncode == 0


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--lean-repo", required=True, help="a git clone of the project with an `origin` remote")
    ap.add_argument("--interval", type=int, default=120, help="seconds between checks (default 120)")
    ap.add_argument("--branch", default="main")
    args = ap.parse_args()
    repo = Path(args.lean_repo).resolve()
    ref = f"origin/{args.branch}"

    last = None
    first = True
    while True:
        try:
            git(repo, "fetch", "--quiet", "origin", args.branch)
            rev = git(repo, "rev-parse", ref)
            if rev != last:
                if last:
                    subjects = git(repo, "log", "--format=%h %s", f"{last}..{rev}")
                    log(f"new commits on {ref}:\n{subjects}")
                if build(repo, rev):
                    last = rev
                    if first:
                        r = subprocess.run([sys.executable, "-I", str(HERE / "check_fidelity.py")],
                                           capture_output=True, text=True)
                        log("fidelity check: " + (r.stdout.strip().splitlines() or ["(no output)"])[-1])
                        first = False
        except (subprocess.SubprocessError, OSError) as exc:
            log(f"check failed ({exc}); will retry")
        time.sleep(args.interval)


if __name__ == "__main__":
    try:
        sys.exit(main())
    except KeyboardInterrupt:
        sys.exit(0)
