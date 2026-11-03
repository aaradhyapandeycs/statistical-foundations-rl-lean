#!/usr/bin/env python3
"""Reproduce a lexical, source-only checklist; this is deliberately not a TeX engine.

Run from anywhere: python3 scripts/inventory.py [--check]. The source tree is
read-only. See the generated Markdown for scope and limitations.
"""
from __future__ import annotations

import argparse
from bisect import bisect_right
from collections import Counter, defaultdict
import hashlib
import json
from pathlib import Path
import re
import sys


PROJECT = Path(__file__).resolve().parents[1]
SOURCE = Path("source/upstream/tex")
MAIN = "StatisticalRL-nowplain.tex"
COMMAND = re.compile(r"\\([A-Za-z@]+|[^A-Za-z@])")
DISPLAY = {"equation", "align", "gather", "multline", "flalign", "alignat", "eqnarray", "displaymath"}
HEADING_LEVEL = {"chapter": 0, "section": 1, "subsection": 2, "subsubsection": 3, "paragraph": 4, "subparagraph": 5}
DEFINERS = {"newcommand", "renewcommand", "providecommand", "DeclareMathOperator"}
PROOF_CUE = re.compile(r"proof|analysis|derivation|step\s*\d|bounding|controlling|establishing", re.I)
DEFINITION_CUE = re.compile(r"\\(?:defn|coloneqq|eqqcolon)\b|\b(?:we define|is defined|are defined|we denote|is called|are called|assume that|suppose that)\b", re.I)
OMISSION_CUE = re.compile(r"\bomit(?:ted|s)?\b|\bwithout proof\b|\b(?:proof|algorithmic details)\b[^\n]{0,160}\b(?:refer|defer|found)\w*\b|\b(?:refer|defer)\w*\b[^\n]{0,160}\b(?:proof|details)\b", re.I)


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def blank(text: str) -> str:
    return "".join("\n" if c == "\n" else " " for c in text)


def uncomment(text: str) -> str:
    """Mask unescaped percent comments, keeping every character and newline."""
    out = list(text)
    i = 0
    while i < len(text):
        if text[i] == "\\":
            m = COMMAND.match(text, i)
            i = m.end() if m else i + 1
        elif text[i] == "%":
            j = text.find("\n", i)
            j = len(text) if j < 0 else j
            out[i:j] = " " * (j - i)
            i = j
        else:
            i += 1
    return "".join(out)


def space(text: str, i: int) -> int:
    while i < len(text) and text[i].isspace():
        i += 1
    return i


def group(text: str, i: int, opening: str = "{") -> tuple[str, int, int]:
    i = space(text, i)
    if i >= len(text) or text[i] != opening:
        raise ValueError(f"expected {opening!r} at offset {i}")
    closing = "}" if opening == "{" else "]"
    depth, j = 1, i + 1
    while j < len(text):
        if text[j] == "\\":
            m = COMMAND.match(text, j)
            j = m.end() if m else j + 1
            continue
        if text[j] == opening:
            depth += 1
        elif text[j] == closing:
            depth -= 1
            if depth == 0:
                return text[i + 1:j], j + 1, i
        j += 1
    raise ValueError(f"unclosed group at offset {i}")


def optional(text: str, i: int) -> tuple[str | None, int]:
    i = space(text, i)
    if i < len(text) and text[i] == "[":
        value, i, _ = group(text, i, "[")
        return value, i
    return None, i


class Inventory:
    def __init__(self, project: Path, source: Path = SOURCE, main: str = MAIN):
        self.project, self.root, self.main = project, project / source, main
        self.raw: dict[str, str] = {}
        self.line_offsets: dict[str, list[int]] = {}
        self.files: list[dict] = []
        self.includes: list[dict] = []
        self.class_support_includes: list[dict] = []
        self.segments: list[tuple[int, int, str, int]] = []
        self.parts: list[str] = []
        self.length = 0
        self.warnings: list[dict] = []
        self.exclusions: list[dict] = []
        self.macros: dict[str, str] = {}
        self.environment_definitions: dict[str, dict] = {}
        self.entries: list[dict] = []
        self.references: list[dict] = []
        self.labels: list[dict] = []
        self.counters = defaultdict(int)
        self.resets = {"equation": "chapter", "algocf": "chapter", "figure": "chapter", "table": "chapter"}
        self.sections = [0] * 6
        self.headings: dict[int, dict] = {}
        self.open_envs: list[dict] = []
        self.subequations: list[dict] = []
        self.last_result = None
        self.in_document = False
        self.appendix = False

    def load(self, path: str) -> str:
        if path not in self.raw:
            data = (self.root / path).read_bytes()
            self.raw[path] = data.decode("utf-8")
            self.line_offsets[path] = [0] + [m.end() for m in re.finditer("\n", self.raw[path])]
            self.files.append({"path": (SOURCE / path).as_posix(), "sha256": digest(data), "lines": len(data.decode("utf-8").splitlines()), "role": "included_tex"})
        return self.raw[path]

    def local(self, path: str, start: int, end: int | None = None) -> dict:
        result = {"file": (SOURCE / path).as_posix(), "line_start": bisect_right(self.line_offsets[path], start)}
        result["line_end"] = bisect_right(self.line_offsets[path], max(start, (end if end is not None else start + 1) - 1))
        return result

    def warn(self, code: str, message: str, path: str | None = None, offset: int = 0):
        item = {"code": code, "message": message}
        if path is not None:
            item["source"] = self.local(path, offset)
        self.warnings.append(item)

    def preprocess(self, path: str) -> str:
        text = uncomment(self.load(path))
        out = list(text)
        i = 0
        while i < len(text):
            m = COMMAND.match(text, i)
            if not m:
                i += 1
                continue
            cmd, j = m.group(1), m.end()
            try:
                if cmd in DEFINERS:
                    if j < len(text) and text[j] == "*":
                        j += 1
                    if text[space(text, j):].startswith("{"):
                        name, j, _ = group(text, j)
                    else:
                        k = COMMAND.match(text, space(text, j))
                        if not k:
                            raise ValueError("missing macro name")
                        name, j = k.group(), k.end()
                    argc, j = optional(text, j)
                    _, j = optional(text, j)
                    body, j, _ = group(text, j)
                    name = name.lstrip("\\")
                    if argc == "1" and body.strip() in {"", "#1"}:
                        self.macros[name] = "discard" if not body.strip() else "identity"
                    out[i:j] = blank(text[i:j])
                    i = j
                    continue
                if cmd == "begin":
                    env, j, _ = group(text, j)
                    if env in {"comment", "verbatim", "verbatim*", "lstlisting", "minted"}:
                        stop = re.search(r"\\end\s*\{" + re.escape(env) + r"\}", text[j:])
                        if not stop:
                            raise ValueError(f"unclosed {env} environment")
                        end = j + stop.end()
                        self.exclusions.append({"kind": env, **self.local(path, i, end)})
                        out[i:end] = blank(text[i:end])
                        i = end
                        continue
                if cmd in self.macros:
                    body, end, opening = group(text, j)
                    if self.macros[cmd] == "discard":
                        out[i:end] = blank(text[i:end])
                    else:
                        out[i:opening + 1] = blank(text[i:opening + 1])
                        out[end - 1] = " "
                    # Inspect the identity body for nested invocations.
                    i = end if self.macros[cmd] == "discard" else opening + 1
                    continue
                if cmd.startswith("if") or cmd in {"else", "fi", "includeonly", "newenvironment", "renewenvironment", "def", "edef", "let", "excludecomment", "includecomment"}:
                    self.warn("unsupported_tex_control", f"\\{cmd} needs manual interpretation; scanner does not execute arbitrary TeX.", path, i)
            except ValueError as error:
                self.warn("parse_error", str(error), path, i)
            i = max(j, m.end())
        return "".join(out)

    def append(self, text: str, path: str, start: int):
        if text:
            self.segments.append((self.length, self.length + len(text), path, start))
            self.parts.append(text)
            self.length += len(text)

    def expand(self, path: str, stack: tuple[str, ...] = ()):
        if path in stack:
            raise ValueError(f"recursive include: {stack!r} -> {path}")
        text = self.preprocess(path)
        cursor = 0
        for m in re.finditer(r"\\(input|include)\s*\{([^{}]+)\}", text):
            self.append(text[cursor:m.start()], path, cursor)
            self.append(blank(text[m.start():m.end()]), path, m.start())
            requested = m.group(2).strip()
            target = requested if Path(requested).suffix else requested + ".tex"
            # TeX is invoked from the main-file directory, not the input's directory.
            candidates = [self.root / target, self.root / Path(path).parent / target]
            resolved = next((p.resolve() for p in candidates if p.is_file()), None)
            record = {"command": m.group(1), "requested": requested, "source": self.local(path, m.start(), m.end()), "order": len(self.includes) + 1}
            if resolved is None or not resolved.is_relative_to(self.root.resolve()):
                record["resolved"] = None
                self.warn("missing_include", f"cannot resolve include {requested!r}", path, m.start())
            else:
                child = resolved.relative_to(self.root.resolve()).as_posix()
                record["resolved"] = (SOURCE / child).as_posix()
                self.includes.append(record)
                self.expand(child, stack + (path,))
                cursor = m.end()
                continue
            self.includes.append(record)
            cursor = m.end()
        self.append(text[cursor:], path, cursor)

    def locate(self, offset: int) -> dict:
        ix = bisect_right(self.segment_starts, min(offset, len(self.text) - 1)) - 1
        start, _, path, local = self.segments[ix]
        return self.local(path, local + offset - start)

    def ranges(self, start: int, end: int) -> list[dict]:
        result = []
        for lo, hi, path, local in self.segments:
            a, b = max(start, lo), min(end, hi)
            if a < b:
                item = self.local(path, local + a - lo, local + b - lo)
                if result and result[-1]["file"] == item["file"] and item["line_start"] <= result[-1]["line_end"] + 1:
                    result[-1]["line_end"] = max(result[-1]["line_end"], item["line_end"])
                else:
                    result.append(item)
        return result

    def theorem_definition(self, text: str, i: int) -> tuple[dict, int]:
        star = text[i:i + 1] == "*"
        i += star
        name, i, _ = group(text, i)
        shared, i = optional(text, i)
        title, i, _ = group(text, i)
        within, i = optional(text, i)
        return {"environment": name, "title_tex": title, "counter": shared or name, "reset_within": within, "numbered": not star}, i

    def load_class(self):
        main = uncomment(self.load(self.main))
        m = re.search(r"\\documentclass(?:\[[^\]]*\])?\s*\{([^}]+)\}", main)
        if not m or not (self.root / (m.group(1) + ".cls")).is_file():
            raise ValueError("local document class required to determine theorem declarations")
        path = m.group(1) + ".cls"
        text = uncomment(self.load(path))
        self.files[-1]["role"] = "class_counter_metadata_only"
        # Literal class input data is provenance, not mathematical document text.
        for include in re.finditer(r"\\input\s*\{([^{}\\]+)\}", text):
            target = include.group(1)
            target = target if Path(target).suffix else target + ".tex"
            if (self.root / target).is_file():
                self.load(target)
                self.files[-1]["role"] = "class_support_metadata_only"
                self.class_support_includes.append({"source": self.local(path, include.start(), include.end()), "resolved": (SOURCE / target).as_posix(), "policy": "hashed only; class support text is excluded from mathematical inventory"})
        for declaration in re.finditer(r"\\newtheorem\b", text):
            definition, end = self.theorem_definition(text, declaration.end())
            definition["source"] = self.local(path, declaration.start(), end)
            self.environment_definitions[definition["environment"]] = definition
            if definition["reset_within"]:
                self.resets[definition["counter"]] = definition["reset_within"]
        self.base_class = "book" if re.search(r"\\LoadClass(?:\[[^\]]*\])?\s*\{book\}", text) else "unknown"
        if self.base_class != "book":
            self.warn("counter_base_class", "Equation/chapter counter assumptions require manual review; base class is not recognized as book.")

    def chapter_number(self) -> str:
        n = self.sections[0]
        return chr(64 + n) if self.appendix and 0 < n < 27 else str(n)

    def counter(self, name: str) -> str:
        self.counters[name] += 1
        n = self.counters[name]
        within = self.resets.get(name)
        if within == "chapter":
            return f"{self.chapter_number()}.{n}"
        if within in HEADING_LEVEL:
            k = HEADING_LEVEL[within]
            return ".".join(map(str, self.sections[:k + 1] + [n]))
        return str(n)

    def equation_number(self) -> str:
        if self.subequations:
            parent = self.subequations[-1]
            parent["child"] += 1
            n = parent["child"]
            # amsmath's \alph has the same finite range; flag rather than guess.
            if n > 26:
                self.warn("subequation_alphabet", f"more than 26 children for {parent['number']}")
            return parent["number"] + (chr(96 + n) if n <= 26 else f"[child {n}]")
        return self.counter("equation")

    def add(self, kind: str, start: int, **extra) -> dict:
        entry = {"kind": kind, "chapter": self.chapter_number(), "section_path": [self.headings[k]["title_tex"] for k in sorted(self.headings)], "status": "unformalized", "review_status": "unreviewed", "labels": [], "_start": start, **extra}
        self.entries.append(entry)
        return entry

    def finish(self, entry: dict, end: int):
        entry["_end"] = end
        entry["source_ranges"] = self.ranges(entry["_start"], end)
        body = self.text[entry["_start"]:end]
        entry["active_text_sha256"] = digest(body.encode())

    def capture_links(self, start: int, end: int, owner: dict):
        """Read metadata in titles skipped as a balanced group by the parser."""
        for m in COMMAND.finditer(self.text, start, end):
            cmd, j = m.group(1), m.end()
            if cmd == "label":
                label, _, _ = group(self.text, j)
                owner["labels"].append(label)
                self.labels.append({"label": label, "source": self.locate(m.start()), "_owner": owner, "_offset": m.start()})
            elif cmd in {"ref", "eqref", "cref", "Cref", "autoref", "pageref"} or cmd.startswith("cite"):
                if self.text[j:j + 1] == "*":
                    j += 1
                _, j = optional(self.text, j)
                _, j = optional(self.text, j)
                targets, _, _ = group(self.text, j)
                self.references.append({"kind": "citation" if cmd.startswith("cite") else "cross_reference", "command": cmd, "targets": [v.strip() for v in targets.split(",")], "source": self.locate(m.start()), "_owner": owner})

    def owner(self) -> dict | None:
        for env in reversed(self.open_envs):
            if env.get("entry"):
                return env["entry"]
        return self.headings[max(self.headings)] if self.headings else None

    def rows(self, start: int, end: int) -> list[tuple[int, int]]:
        """Split at top-level \\\\; cases/arrays and braced macros do not split."""
        rows, cursor, i, depth, envs = [], start, start, 0, []
        while i < end:
            m = COMMAND.match(self.text, i)
            if m:
                cmd = m.group(1)
                if cmd in {"begin", "end"}:
                    name, j, _ = group(self.text, m.end())
                    if cmd == "begin":
                        envs.append(name)
                    elif envs and envs[-1] == name:
                        envs.pop()
                    i = j
                    continue
                if cmd == "\\" and depth == 0 and not envs:
                    rows.append((cursor, i))
                    i = m.end()
                    if self.text[i:i + 1] == "*":
                        i += 1
                    _, i = optional(self.text, i)
                    cursor = i
                    continue
                i = m.end()
            else:
                if self.text[i] == "{":
                    depth += 1
                elif self.text[i] == "}":
                    depth -= 1
                i += 1
        if self.text[cursor:end].strip():
            rows.append((cursor, end))
        return rows

    def display_close(self, env: dict, closing_start: int, end: int):
        entry, name = env["entry"], env["name"]
        numbered = not name.endswith("*") and name not in {"displaymath", "\\[", "$$"}
        base = name.rstrip("*")
        spans = self.rows(env["content_start"], closing_start) if base in {"align", "gather", "flalign", "alignat", "eqnarray"} else [(env["content_start"], closing_start)]
        rows = []
        for a, b in spans:
            value = self.text[a:b]
            tag = re.search(r"\\tag\*?\s*\{([^}]+)\}", value)
            suppress = bool(re.search(r"\\(?:nonumber|notag)\b", value))
            number = self.equation_number() if numbered and not suppress and not tag else None
            rows.append({"number": tag.group(1) if tag else number, "number_kind": "explicit_tag" if tag else ("simulated_counter" if number else "unnumbered"), "labels": re.findall(r"\\label\s*\{([^}]+)\}", value), "source_ranges": self.ranges(a, b)})
        entry["rows"] = rows
        entry["numbered_rows"] = sum(r["number"] is not None for r in rows)
        entry["number"] = rows[0]["number"] if len(rows) == 1 else None
        entry["definition_notation_candidate"] = bool(DEFINITION_CUE.search(self.text[env["content_start"]:closing_start]))
        self.finish(entry, end)

    def parse(self):
        i = 0
        while i < len(self.text):
            if self.text.startswith("$$", i) and self.in_document:
                if self.open_envs and self.open_envs[-1]["name"] == "$$":
                    self.display_close(self.open_envs.pop(), i, i + 2)
                else:
                    self.open_envs.append({"name": "$$", "content_start": i + 2, "entry": self.add("display", i, environment="$$")})
                i += 2
                continue
            m = COMMAND.match(self.text, i)
            if not m:
                i += 1
                continue
            cmd, j = m.group(1), m.end()
            try:
                if cmd == "newtheorem":
                    definition, j = self.theorem_definition(self.text, j)
                    definition["source"] = self.locate(i)
                    self.environment_definitions[definition["environment"]] = definition
                    if definition["reset_within"]:
                        self.resets[definition["counter"]] = definition["reset_within"]
                elif cmd == "numberwithin":
                    name, j, _ = group(self.text, j)
                    within, j, _ = group(self.text, j)
                    self.resets[name] = within
                elif cmd in {"setcounter", "addtocounter"}:
                    name, j, _ = group(self.text, j)
                    value, j, _ = group(self.text, j)
                    try:
                        if cmd == "setcounter":
                            self.counters[name] = int(value)
                        else:
                            self.counters[name] += int(value)
                        if name in HEADING_LEVEL:
                            self.sections[HEADING_LEVEL[name]] = self.counters[name]
                    except ValueError:
                        self.warn("symbolic_counter", f"cannot evaluate {cmd} {name} {value}")
                elif cmd == "appendix" and self.in_document:
                    self.appendix, self.sections = True, [0] * 6
                elif cmd in HEADING_LEVEL and self.in_document:
                    level = HEADING_LEVEL[cmd]
                    star = self.text[j:j + 1] == "*"
                    j += star
                    _, j = optional(self.text, j)
                    title, j, title_open = group(self.text, j)
                    if not star:
                        self.sections[level] += 1
                        self.sections[level + 1:] = [0] * (5 - level)
                        for name, within in self.resets.items():
                            if within == cmd:
                                self.counters[name] = 0
                    self.headings = {k: v for k, v in self.headings.items() if k < level}
                    number = ".".join([self.chapter_number()] + list(map(str, self.sections[1:level + 1]))) if level <= 3 and not star else None
                    entry = self.add("heading", i, environment=cmd, title_tex=title, level=level, number=number, starred=star, proof_region_candidate=bool(PROOF_CUE.search(title)))
                    self.headings[level] = entry
                    self.finish(entry, j)
                    self.capture_links(title_open + 1, j - 1, entry)
                elif cmd in {"begin", "end"}:
                    name, j, _ = group(self.text, j)
                    if name == "document":
                        self.in_document = cmd == "begin"
                    elif self.in_document and cmd == "begin":
                        entry = None
                        opt_start = space(self.text, j)
                        title, opt_end = optional(self.text, j)
                        if name in self.environment_definitions:
                            definition = self.environment_definitions[name]
                            number = self.counter(definition["counter"]) if definition["numbered"] else None
                            entry = self.add(name, i, environment=name, title_tex=title, number=number, counter=definition["counter"])
                            self.last_result = entry if name in {"theorem", "lemma", "proposition", "corollary", "claim"} else self.last_result
                            j = opt_end
                        elif name in {"algorithm", "algorithm*"}:
                            entry = self.add("algorithm", i, environment=name, title_tex=title, number=self.counter("algocf"))
                            j = opt_end
                        elif name == "proof":
                            entry = self.add("proof", i, environment=name, title_tex=title, number=None, adjacent_result_candidate=self.last_result)
                            j = opt_end
                        elif name.rstrip("*") in DISPLAY:
                            entry = self.add("display", i, environment=name)
                        elif name == "subequations":
                            number = self.equation_number()
                            entry = self.add("subequations", i, environment=name, number=number)
                            self.subequations.append({"number": number, "child": 0})
                        elif name in {"figure", "figure*", "table", "table*"}:
                            # Figures are context; captions drive their actual TeX counters.
                            entry = self.add(name.rstrip("*"), i, environment=name, number=None)
                        if entry and title is not None and j == opt_end:
                            self.capture_links(opt_start + 1, opt_end - 1, entry)
                        self.open_envs.append({"name": name, "entry": entry, "content_start": j})
                    elif self.in_document and cmd == "end":
                        if not self.open_envs or self.open_envs[-1]["name"] != name:
                            self.warn("unbalanced_environment", f"unexpected end of {name} at {self.locate(i)}")
                        else:
                            env = self.open_envs.pop()
                            if env["entry"]:
                                if name.rstrip("*") in DISPLAY:
                                    self.display_close(env, i, j)
                                else:
                                    self.finish(env["entry"], j)
                            if name == "subequations":
                                self.subequations.pop()
                elif cmd in {"[", "]"} and self.in_document:
                    if cmd == "[":
                        self.open_envs.append({"name": "\\[", "content_start": j, "entry": self.add("display", i, environment="\\[")})
                    elif self.open_envs and self.open_envs[-1]["name"] == "\\[":
                        self.display_close(self.open_envs.pop(), i, j)
                    else:
                        self.warn("unbalanced_display", f"unexpected \\] at {self.locate(i)}")
                elif cmd == "label" and self.in_document:
                    label, j, _ = group(self.text, j)
                    owner = self.owner()
                    record = {"label": label, "source": self.locate(i), "_owner": owner, "_offset": i}
                    self.labels.append(record)
                    if owner:
                        owner["labels"].append(label)
                elif self.in_document and (cmd in {"ref", "eqref", "cref", "Cref", "autoref", "pageref"} or cmd.startswith("cite")):
                    if self.text[j:j + 1] == "*":
                        j += 1
                    _, j = optional(self.text, j)
                    _, j = optional(self.text, j)
                    targets, j, _ = group(self.text, j)
                    self.references.append({"kind": "citation" if cmd.startswith("cite") else "cross_reference", "command": cmd, "targets": [v.strip() for v in targets.split(",")], "source": self.locate(i), "_owner": self.owner()})
            except ValueError as error:
                self.warn("parse_error", f"{error} near {self.locate(i)}")
            i = max(j, m.end())
        for env in self.open_envs:
            self.warn("unclosed_environment", f"unclosed environment {env['name']}")

    def finalize(self) -> dict:
        # Heading-based proof/analysis regions deliberately remain candidates.
        headings = [e for e in self.entries if e["kind"] == "heading"]
        for n, entry in enumerate(headings):
            if entry["proof_region_candidate"]:
                end = next((h["_start"] for h in headings[n + 1:] if h["level"] <= entry["level"]), len(self.text))
                region = self.add("proof_region", entry["_start"], title_tex=entry["title_tex"], number=entry["number"], detection="heading_keyword_candidate")
                region["chapter"], region["section_path"] = entry["chapter"], entry["section_path"]
                self.finish(region, end)
        # Inline definitions are not restricted to formal definition environments.
        definition_lines = set()
        for match in DEFINITION_CUE.finditer(self.text):
            if not any(e["kind"] == "heading" and e["_start"] <= match.start() < e["_end"] for e in headings):
                a = max(self.text.rfind("\n\n", 0, match.start()) + 2, self.text.rfind("\n", 0, match.start()) + 1)
                b = self.text.find("\n", match.end())
                b = len(self.text) if b < 0 else b
                if (a, b) in definition_lines:
                    continue
                definition_lines.add((a, b))
                entry = self.add("definition_candidate", a, number=None, detection="notation_or_prose_keyword", matched_cue=match.group())
                # Look up context at this position, not at end of document.
                context = next((h for h in reversed(headings) if h["_start"] <= a), None)
                if context:
                    entry["chapter"], entry["section_path"] = context["chapter"], context["section_path"] + [context["title_tex"]]
                self.finish(entry, b)
        omission_lines = set()
        for match in OMISSION_CUE.finditer(self.text):
            a = self.text.rfind("\n", 0, match.start()) + 1
            b = self.text.find("\n", match.end())
            b = len(self.text) if b < 0 else b
            if (a, b) in omission_lines:
                continue
            omission_lines.add((a, b))
            entry = self.add("source_gap_candidate", a, number=None, detection="omission_or_external_proof_keyword", interpretation="Manual review required: this may be an internal deferral, exposition choice, or external proof dependency, not a mathematical error.")
            context = next((h for h in reversed(headings) if h["_start"] <= a), None)
            if context:
                entry["chapter"], entry["section_path"] = context["chapter"], context["section_path"] + [context["title_tex"]]
            self.finish(entry, b)
        self.entries.sort(key=lambda e: (e["_start"], e["kind"]))
        ids = Counter()
        for entry in self.entries:
            fallback = f"ch{entry['chapter']}-{entry['kind']}-{entry.get('number') or entry['active_text_sha256'][:12]}"
            base = "label:" + entry["labels"][0] if entry["labels"] else fallback
            ids[base] += 1
            entry["id"] = base if ids[base] == 1 else f"{base}~{ids[base]}"
        for entry in self.entries:
            if "adjacent_result_candidate" in entry:
                candidate = entry["adjacent_result_candidate"]
                entry["adjacent_result_candidate"] = candidate["id"] if candidate else None
        declared = defaultdict(list)
        for label in self.labels:
            owner = label.pop("_owner")
            label.pop("_offset")
            label["owner_id"] = owner["id"] if owner else None
            declared[label["label"]].append(label)
        for name, occurrences in declared.items():
            if len(occurrences) > 1:
                self.warn("duplicate_label", f"label {name!r} declared {len(occurrences)} times")
        for ref in self.references:
            owner = ref.pop("_owner")
            ref["owner_id"] = owner["id"] if owner else None
            if ref["kind"] == "cross_reference":
                for target in ref["targets"]:
                    if target not in declared:
                        self.warn("unresolved_cross_reference", f"{target!r} referenced at {ref['source']}")
        for entry in self.entries:
            entry.pop("_start", None)
            entry.pop("_end", None)
        counts = Counter(e["kind"] for e in self.entries)
        chapters = [{"number": e["number"], "title_tex": e["title_tex"], "source": e["source_ranges"][0], "counts": dict(sorted(Counter(x["kind"] for x in self.entries if x["chapter"] == e["chapter"]).items()))} for e in self.entries if e["kind"] == "heading" and e["environment"] == "chapter"]
        included = {f["path"] for f in self.files}
        unreferenced = [(SOURCE / p.relative_to(self.root)).as_posix() for p in sorted(self.root.rglob("*.tex")) if (SOURCE / p.relative_to(self.root)).as_posix() not in included]
        return {"schema_version": 1, "source": {"arxiv_id": "2610.41903v1", "main": (SOURCE / self.main).as_posix(), "main_sha256": digest(self.raw[self.main].encode()), "base_class": self.base_class}, "coverage_claim": "Lexical source checklist only. No statement, definition, proof, or complete mathematical coverage has been certified.", "status_policy": "All entries initialize unformalized and unreviewed; this inventory never infers Lean proof status.", "counter_policy": "Simulated chapter/shared theorem/algorithm/amsmath row counters from local class and preamble; compare rendered PDF before relying on printed numbers.", "counts": {"entries": len(self.entries), "by_kind": dict(sorted(counts.items())), "numbered_display_rows": sum(e.get("numbered_rows", 0) for e in self.entries), "labels": len(self.labels), "unique_labels": len(declared), "citations": sum(r["kind"] == "citation" for r in self.references), "cross_references": sum(r["kind"] == "cross_reference" for r in self.references), "warnings": len(self.warnings)}, "files": self.files, "include_order": self.includes, "class_support_includes": self.class_support_includes, "unreferenced_tex_files": unreferenced, "environment_definitions": list(self.environment_definitions.values()), "recognized_wrapper_macros": self.macros, "excluded_regions": self.exclusions, "chapters": chapters, "warnings": self.warnings, "entries": self.entries, "labels": self.labels, "references": self.references}

    def run(self) -> dict:
        self.load_class()
        self.expand(self.main)
        self.text = "".join(self.parts)
        self.segment_starts = [s[0] for s in self.segments]
        self.parse()
        return self.finalize()


def markdown(data: dict) -> str:
    counts = data["counts"]
    lines = ["# Source inventory", "", "Generated by `python3 scripts/inventory.py`. Verify reproducibility with `python3 scripts/inventory.py --check`.", "", data["coverage_claim"], "", "Every entry is **unformalized / unreviewed**. Numbered theorem environments, numbered and unnumbered displays, definitions, assumptions, algorithms, explicit proofs, and candidate proof/analysis regions are source work items, not Lean results. A full chapter-by-chapter semantic review is still required.", "", f"Source: `{data['source']['arxiv_id']}`, main `{data['source']['main']}`.", f"Main SHA-256: `{data['source']['main_sha256']}`.", "", "## Counts", "", "| Kind | Entries |", "| --- | ---: |"]
    lines += [f"| {k} | {v} |" for k, v in counts["by_kind"].items()]
    lines += ["", f"Total: **{counts['entries']}** entries; **{counts['numbered_display_rows']}** simulated numbered display rows; **{counts['labels']}** label declarations (**{counts['unique_labels']}** unique); **{counts['citations']}** citation commands; **{counts['cross_references']}** cross-reference commands.", "", "## Chapters in actual include order", "", "| Chapter | Title (TeX) | Named results¹ | Algorithms | Displays | Proof environments | Proof-region candidates |", "| --- | --- | ---: | ---: | ---: | ---: | ---: |"]
    for ch in data["chapters"]:
        c = ch["counts"]
        named = sum(c.get(k, 0) for k in ["theorem", "lemma", "proposition", "corollary", "claim"])
        lines.append(f"| {ch['number']} | {ch['title_tex'].replace('|', ' / ')} | {named} | {c.get('algorithm', 0)} | {c.get('display', 0)} | {c.get('proof', 0)} | {c.get('proof_region', 0)} |")
    lines += ["", "¹ Named results excludes separately counted definitions, assumptions, remarks and examples. Proof-region candidates can overlap explicit proofs or one another, and are not additive proof counts.", "", "## Included source tree", "", "| Order | Include location | Target |", "| ---: | --- | --- |"]
    for inc in data["include_order"]:
        src = inc["source"]
        lines.append(f"| {inc['order']} | `{src['file']}:{src['line_start']}` | `{inc['resolved']}` |")
    lines += ["", "## What the scanner does", "", "- Follows braced `input`/`include` commands in execution order from the main source. Hashes included files and the local class. Reads the local class for theorem counter declarations; class/package rendering macros are not included as mathematical content.", "- Masks percent comments, comment environments and macro definitions without losing source line positions. Recognizes one-argument empty/identity wrappers (including this source's `arxiv`/`book` choices). The wrapper semantics follow the active source definitions, regardless of the macro names.", "- Reads theorem environment definitions and shared counters; resets chapter counters; distinguishes equation rows, suppression (`notag`/`nonumber`), subequation letters and explicit tags. Numbering is a simulation, not a compiled `.aux` certificate.", "- Records all supported displays, including unlabeled and unnumbered ones. Records labels and cross-reference/citation sites, explicit proof environments and headings matching proof/analysis/step cues.", "- Adds notation/prose definition candidates. These may duplicate surrounding work items and require semantic classification. Labels are preferred IDs; unlabeled IDs use chapter/kind/number or a content hash rather than line numbers.", "", "## Limits and remaining coverage work", "", "- This is a lexical scanner, not a general TeX interpreter. Arbitrary macro expansion, package-specific counters, conditionals, catcode changes, dynamically generated input paths, and all possible custom environments are unsupported. Unsupported control commands are reported when detected. Only simple wrapper macros are expanded.", "- Counter predictions must be checked against the authoritative rendered PDF. An align environment can contain several numbered rows; row count differs from display-environment count. Figures/tables are context entries and their printed numbering is not predicted.", "- Keywords cannot decide mathematical importance or identify every inline definition, unnamed lemma, standing assumption, proof gap, cited external premise or substantive proof step. Every source paragraph, including exposition, must still receive independent semantic review. No count here certifies exhaustive mathematics coverage.", "- Proof-heading regions end at the next heading of equal/higher level. Adjacent-result links are search hints only; no statement-to-proof pairing or dependency edge is certified.", "- The inventory initializes every item as unformalized; it does not inspect Lean implementations, create frozen anchors, or satisfy the source dependency graph's approval/audit gates.", "- Rerunning regenerates the source checklist and resets statuses. Keep formalization evidence in a separate reviewed ledger keyed to source IDs. IDs without labels can change when the source changes.", "", "## Warnings and potential source issues", ""]
    if data["warnings"]:
        for warning in data["warnings"]:
            source = warning.get("source")
            suffix = f" (`{source['file']}:{source['line_start']}`)" if source else ""
            lines.append(f"- **{warning['code']}**: {warning['message']}{suffix}")
    else:
        lines.append("No scanner warnings. This does not imply there are no mathematical source gaps.")
    lines += ["", "Unreferenced `.tex` files: " + (", ".join(f"`{p}`" for p in data["unreferenced_tex_files"]) or "none") + ".", "", f"Excluded explicit comment/verbatim regions: **{len(data['excluded_regions'])}** (locations in JSON). Percent-commented lines are masked separately.", "", "### Omission / external-proof candidates", "", "The following keyword hits require source review. Internal proof deferrals, deliberately abbreviated exposition, external dependencies, and mathematical gaps are different dispositions; these are not error verdicts. The JSON contains source hashes and context for each candidate.", ""]
    for e in data["entries"]:
        if e["kind"] == "source_gap_candidate":
            lines.append("- " + "; ".join(f"`{r['file']}:{r['line_start']}-{r['line_end']}`" for r in e["source_ranges"]))
    lines += ["", "## Named statements and algorithms", "", "The JSON contains every entry, every display row and its source ranges, labels and references. This compact table lists theorem-like environments and algorithms for review.", "", "| ID | Kind | Predicted number | Source |", "| --- | --- | --- | --- |"]
    kinds = {"theorem", "lemma", "corollary", "proposition", "claim", "definition", "assumption", "algorithm", "remark", "example"}
    for e in data["entries"]:
        if e["kind"] in kinds:
            loc = "; ".join(f"{r['file']}:{r['line_start']}-{r['line_end']}" for r in e["source_ranges"])
            lines.append(f"| `{e['id'].replace('|', ' / ')}` | {e['kind']} | {e.get('number') or '—'} | `{loc}` |")
    return "\n".join(lines) + "\n"


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="fail if generated artifacts differ; write nothing")
    args = parser.parse_args()
    data = Inventory(PROJECT).run()
    outputs = {PROJECT / "docs/source-inventory.json": json.dumps(data, ensure_ascii=False, indent=2) + "\n", PROJECT / "docs/source-inventory.md": markdown(data)}
    for path, value in outputs.items():
        if args.check:
            if not path.exists() or path.read_text() != value:
                print(f"out of date: {path.relative_to(PROJECT)}", file=sys.stderr)
                return 1
        else:
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(value)
    print(json.dumps(data["counts"], sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
