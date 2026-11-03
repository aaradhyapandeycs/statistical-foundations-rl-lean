#!/usr/bin/env python3
"""Compile every project module and audit axioms, without rebuilding dependencies."""
from __future__ import annotations

import datetime
import hashlib
import json
from pathlib import Path
import re
import subprocess
import time

ROOT = Path(__file__).resolve().parents[1]


def lean_code(text: str) -> str:
    """Mask nested block comments, line comments, and strings, retaining newlines."""
    output = list(text)
    depth = 0
    string = False
    i = 0
    while i < len(text):
        if depth:
            if text.startswith("/-", i):
                depth += 1
                output[i:i + 2] = "  "
                i += 2
            elif text.startswith("-/", i):
                depth -= 1
                output[i:i + 2] = "  "
                i += 2
            else:
                if text[i] != "\n":
                    output[i] = " "
                i += 1
        elif string:
            if text[i] == "\\" and i + 1 < len(text):
                output[i:i + 2] = "  "
                i += 2
            else:
                if text[i] == '"':
                    string = False
                if text[i] != "\n":
                    output[i] = " "
                i += 1
        elif text.startswith("/-", i):
            depth = 1
            output[i:i + 2] = "  "
            i += 2
        elif text.startswith("--", i):
            end = text.find("\n", i)
            end = len(text) if end == -1 else end
            output[i:end] = " " * (end - i)
            i = end
        elif text[i] == '"':
            string = True
            output[i] = " "
            i += 1
        else:
            i += 1
    return "".join(output)


def main() -> None:
    sources = [ROOT / "Formalization.lean", *sorted((ROOT / "Formalization").rglob("*.lean")), ROOT / "Audit.lean"]
    modules = {str(path.relative_to(ROOT).with_suffix("")).replace("/", "."): path for path in sources}
    for path in sources:
        if not path.is_file():
            raise RuntimeError(f"Required source missing: {path.name}")
    hashes = {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in sources}
    imports: dict[str, list[str]] = {}
    for name, path in modules.items():
        code = lean_code(path.read_text())
        if re.search(r"\b(sorry|admit|axiom)\b", code):
            raise RuntimeError(f"Unauthorized placeholder or axiom command in {name}")
        imported = [token for line in re.findall(r"^\s*(?:public\s+)?import\s+([^\n]+)", code, re.M) for token in line.split()]
        imports[name] = [item for item in imported if item in modules]
    order: list[str] = []
    active: set[str] = set()
    done: set[str] = set()

    def visit(name: str) -> None:
        if name in active:
            raise RuntimeError(f"Local import cycle at {name}")
        if name in done:
            return
        active.add(name)
        for dependency in imports[name]:
            visit(dependency)
        active.remove(name)
        done.add(name)
        order.append(name)

    for name in modules:
        visit(name)
    # The axiom audit must see the complete library, not just a narrow facade.
    closure: set[str] = set()

    def cover(name: str) -> None:
        if name in closure:
            return
        closure.add(name)
        for dependency in imports[name]:
            cover(dependency)

    cover("Audit")
    if closure != set(modules):
        raise RuntimeError(f"Audit import closure omits: {sorted(set(modules) - closure)}")
    stamp = datetime.datetime.now(datetime.timezone.utc).strftime("%Y%m%dT%H%M%S%fZ")
    report_dir = ROOT / "verification" / stamp
    report_dir.mkdir(parents=True)
    report = {"utc": stamp, "source_sha256": hashes, "modules": [], "success": False}
    version = subprocess.run(["bash", "scripts/lean-local.sh", "--version"], cwd=ROOT, text=True, capture_output=True, check=True)
    report["compiler"] = version.stdout.strip()
    try:
        for name in order:
            relative = modules[name].relative_to(ROOT)
            artifact = Path(".lake/build/lib/lean") / relative.with_suffix(".olean")
            (ROOT / artifact).parent.mkdir(parents=True, exist_ok=True)
            command = ["bash", "scripts/lean-local.sh", "-o", str(artifact), str(relative)]
            started = time.monotonic()
            process = subprocess.run(command, cwd=ROOT, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
            elapsed = time.monotonic() - started
            log = name + ".log"
            (report_dir / log).write_text(process.stdout)
            report["modules"].append({"module": name, "command": command, "exit": process.returncode, "wall_seconds": elapsed, "log": log})
            print(f"{name}: exit {process.returncode}, {elapsed:.2f}s", flush=True)
            if process.stdout:
                print(process.stdout, end="", flush=True)
            if process.returncode:
                raise RuntimeError(f"Compilation failed: {name}")
        for relative, expected in hashes.items():
            if hashlib.sha256((ROOT / relative).read_bytes()).hexdigest() != expected:
                raise RuntimeError(f"Concurrent source edit invalidated verification: {relative}")
        report["success"] = True
    finally:
        (report_dir / "manifest.json").write_text(json.dumps(report, indent=2) + "\n")
    print(f"Checked {len(order)} project modules; evidence in verification/{stamp}/")


if __name__ == "__main__":
    main()
