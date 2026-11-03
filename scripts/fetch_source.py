#!/usr/bin/env python3
"""Restore the exact pinned public arXiv inputs without executing TeX or archive code."""
from __future__ import annotations

import hashlib
import io
import json
from pathlib import Path
import shutil
import tarfile
import urllib.request

ROOT = Path(__file__).resolve().parents[1]


def main() -> None:
    metadata = json.loads((ROOT / "source/provenance.json").read_text())
    destination = ROOT / "source/upstream"
    destination.mkdir(parents=True, exist_ok=True)
    for name, url in (("2610.41903v1.tar", metadata["source_url"]),
                      ("2610.41903v1.pdf", metadata["pdf_url"])):
        artifact = destination / name
        if artifact.is_file() and hashlib.sha256(artifact.read_bytes()).hexdigest() == metadata["artifacts"][name]:
            continue
        with urllib.request.urlopen(url, timeout=90) as response:
            data = response.read()
        if hashlib.sha256(data).hexdigest() != metadata["artifacts"][name]:
            raise RuntimeError(f"Pinned checksum mismatch: {name}")
        artifact.write_bytes(data)
    extraction = destination / "tex"
    extraction.mkdir(exist_ok=True)
    for name, expected in metadata["source_files"].items():
        existing = extraction / name
        if existing.is_symlink():
            raise RuntimeError(f"Refusing to overwrite symlink: {name}")
        if existing.exists() and hashlib.sha256(existing.read_bytes()).hexdigest() != expected:
            raise RuntimeError(f"Refusing to overwrite modified source: {name}")
    with tarfile.open(fileobj=io.BytesIO((destination / "2610.41903v1.tar").read_bytes())) as archive:
        members = archive.getmembers()
        for member in members:
            resolved = (extraction / member.name).resolve()
            if not resolved.is_relative_to(extraction.resolve()) or not (member.isfile() or member.isdir()):
                raise RuntimeError(f"Unsafe archive entry: {member.name}")
        for member in members:
            target = extraction / member.name
            if member.isdir():
                target.mkdir(parents=True, exist_ok=True)
            elif not target.exists():
                target.parent.mkdir(parents=True, exist_ok=True)
                stream = archive.extractfile(member)
                if stream is None:
                    raise RuntimeError(f"Cannot read archive entry: {member.name}")
                with stream, target.open("xb") as output:
                    shutil.copyfileobj(stream, output)
    for name, expected in metadata["source_files"].items():
        if hashlib.sha256((extraction / name).read_bytes()).hexdigest() != expected:
            raise RuntimeError(f"Extracted checksum mismatch: {name}")
    print(f"Verified {len(metadata['source_files'])} source files and both pinned downloads.")


if __name__ == "__main__":
    main()
