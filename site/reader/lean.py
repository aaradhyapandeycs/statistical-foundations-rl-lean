"""Lean side of the reader, read from one pinned git commit.

Everything comes from `git show <commit>:<path>`, so line numbers match the
GitHub links and uncommitted work in the checkout is never shown. Status is
taken only from the reviewed ledger (`docs/named-result-status.json`); a
statement entry without a ledger record is shown as unrecorded, not proved.
"""

from __future__ import annotations

import html
import json
import re
import subprocess
from dataclasses import dataclass, field
from pathlib import Path

REPO = "https://github.com/aaradhyapandeycs/statistical-foundations-rl-lean"

STATUS = {
    "original": ("Proved as printed", "st-proved"),
    "corrected": ("Proved in corrected form", "st-corrected"),
    "restricted": ("Proved for a restricted case", "st-restricted"),
    "unrecorded": ("Statement entry, no reviewed status recorded", "st-unrecorded"),
    "partial": ("Partial (coverage ledger)", "st-partial"),
    "ledger": ("Ledger note, not a proved result", "st-ledger"),
    "none": ("Not yet formalized", "st-none"),
}
STATUS_ORDER = ["original", "corrected", "restricted", "unrecorded", "partial", "ledger", "none"]


def esc(t: str) -> str:
    return html.escape(t, quote=False)


def attr(t: str) -> str:
    return html.escape(t, quote=True)


class Git:
    def __init__(self, root: Path, rev: str):
        self.root = root
        self.rev = self.run("rev-parse", rev).strip()
        self.cache: dict = {}

    def run(self, *args) -> str:
        r = subprocess.run(["git", "-C", str(self.root), *args], capture_output=True, text=True)
        if r.returncode != 0:
            raise RuntimeError(f"git {' '.join(args)}: {r.stderr.strip()}")
        return r.stdout

    def show(self, path: str) -> str:
        if path not in self.cache:
            self.cache[path] = self.run("show", f"{self.rev}:{path}")
        return self.cache[path]

    def ls(self, prefix: str) -> list:
        return [l for l in self.run("ls-tree", "-r", "--name-only", self.rev, "--", prefix).splitlines() if l]

    def grep(self, pattern: str, prefix: str) -> list:
        r = subprocess.run(["git", "-C", str(self.root), "grep", "-n", "-E", pattern, self.rev, "--", prefix],
                           capture_output=True, text=True)
        out = []
        for line in r.stdout.splitlines():
            _, path, num, text = line.split(":", 3)
            out.append((path, int(num), text))
        return out

    def blob(self, path: str, a: int | None = None, b: int | None = None) -> str:
        frag = f"#L{a}-L{b}" if a and b and b != a else (f"#L{a}" if a else "")
        return f"{REPO}/blob/{self.rev}/{path}{frag}"


@dataclass
class Entry:
    name: str
    full: str
    file: str
    line_start: int
    line_end: int
    source: str
    labels: list
    ranges: list
    proof: dict | None = None
    record: dict | None = None
    status: str = "unrecorded"
    exports: list = field(default_factory=list)
    issues: list = field(default_factory=list)


RANGE_RE = re.compile(r"`?((?:[\w-]+/)*[\w-]+\.tex):(\d+)(?:[–-](\d+))?`?")
LABEL_RE = re.compile(r"`([A-Za-z][\w-]*:[^`\s]+)`")
DECL_RE = re.compile(r"/--(?P<doc>.*?)-/\s*\n(?P<decl>(?:noncomputable\s+)?def\s+(?P<name>[\w']+)\b.*?)"
                     r"(?=\n\s*\n|\n/--|\nend\b|\Z)", re.S)
TOP_DECL = re.compile(r"^(?:@\[|/--|theorem |lemma |def |noncomputable |private |protected |instance |"
                      r"structure |class |abbrev |inductive |namespace |section |end\b|open |variable |"
                      r"example |set_option |#|universe |attribute )")


def namespace_at(text: str, upto: int) -> str:
    stack = []
    for line in text.splitlines()[:upto - 1]:
        m = re.match(r"namespace\s+([\w.]+)", line)
        if m:
            stack.append(m.group(1))
            continue
        m = re.match(r"end\s+([\w.]+)\s*$", line)
        if m and stack and stack[-1] == m.group(1):
            stack.pop()
    return ".".join(stack)


def decl_extent(lines: list, start: int, cap: int = 400):
    """Declaration at 1-based line `start`, with its attributes and docstring."""
    a = start
    while a > 1 and lines[a - 2].startswith("@["):
        a -= 1
    if a > 1 and lines[a - 2].rstrip().endswith("-/"):
        k = a - 1
        while k >= 1 and "/-" not in lines[k - 1]:
            k -= 1
        if k >= 1:
            a = k
            while a > 1 and lines[a - 2].startswith("@["):
                a -= 1
    b = start
    while b < len(lines) and not TOP_DECL.match(lines[b]):
        b += 1
    while b > start and not lines[b - 1].strip():
        b -= 1
    truncated = b - a + 1 > cap
    if truncated:
        b = a + cap - 1
    return a, b, truncated


class LeanIndex:
    def __init__(self, git: Git, inventory_labels: set):
        self.git = git
        self.inv_labels = inventory_labels
        self.entries: list = []
        self.status = json.loads(git.show("docs/named-result-status.json"))
        self.issue_slugs = self.parse_issues(git.show("docs/SOURCE-ISSUES.md"))
        self.coverage = self.parse_coverage(git.show("docs/COVERAGE.md"))
        self.load_entries()

    # parsing ------------------------------------------------------------------
    def load_entries(self):
        files = [f for f in self.git.ls("Formalization/Statements")
                 if re.search(r"/Ch\d+\.lean$", f)]
        records = {}
        for kind in ("certified_named_results", "proved_variants"):
            for rec in self.status.get(kind, []):
                records[rec["lean_statement"]] = (kind, rec)
        for f in sorted(files, key=lambda x: int(re.search(r"Ch(\d+)", x).group(1))):
            text = self.git.show(f)
            proofs = self.parse_proofs(f.replace(".lean", "Proofs.lean"))
            for m in DECL_RE.finditer(text):
                doc = m.group("doc")
                start = text.count("\n", 0, m.start()) + 1
                end = text.count("\n", 0, m.end("decl")) + 1
                name = m.group("name")
                ns = namespace_at(text, start)
                full = f"{ns}.{name}" if ns else name
                labels = [l for l in LABEL_RE.findall(doc) if ".tex" not in l]
                ranges = [{"file": r[0], "line_start": int(r[1]), "line_end": int(r[2] or r[1])}
                          for r in RANGE_RE.findall(doc)]
                e = Entry(name, full, f, start, end, text[m.start():m.end("decl")], labels, ranges)
                e.proof = proofs.get(name)
                rec = records.get(full)
                if rec:
                    kind, e.record = rec
                    e.status = classify(name, kind, e.record.get("statement_scope", ""))
                    lab = e.record.get("source_label")
                    if lab and lab not in e.labels:
                        e.labels.append(lab)
                    exp = e.record.get("component_exports") or e.record.get("lean_export", "")
                    if isinstance(exp, list):
                        exp = " ".join(map(str, exp))
                    # Hide only the statement-index wrappers (Statements.*_holds), not library
                    # theorems that happen to end in `_holds`.
                    e.exports = [x for x in self.locate_exports(exp)
                                 if not (x["name"].endswith("_holds") and ".Statements." in "." + x["name"])]
                scope = (e.record or {}).get("statement_scope", "") + " " + doc
                e.issues = [c for c in dict.fromkeys(re.findall(r"\bC(\d+)\b", scope)) if c in self.issue_slugs]
                self.entries.append(e)

    def parse_proofs(self, path: str) -> dict:
        try:
            text = self.git.show(path)
        except RuntimeError:
            return {}
        lines = text.splitlines()
        out = {}
        for i, line in enumerate(lines, 1):
            m = re.match(r"(?:noncomputable\s+)?theorem\s+([\w']+)_holds\b", line)
            if m:
                a, b, trunc = decl_extent(lines, i, cap=200)
                out[m.group(1)] = {"file": path, "line_start": a, "line_end": b,
                                   "source": "\n".join(lines[a - 1:b]), "truncated": trunc,
                                   "name": f"{m.group(1)}_holds"}
        return out

    def locate_exports(self, text: str) -> list:
        names = [n.rstrip(".,;") for n in re.findall(r"[A-Za-z_][\w'.]*\.[\w']+", text)]
        out = []
        for full in dict.fromkeys(names):
            short = full.rsplit(".", 1)[-1]
            # POSIX classes: git grep -E has no \\b or \\w.
            hits = self.git.grep(r"^(private |protected )?(noncomputable )?(theorem|lemma|def) "
                                 rf"([[:alnum:]_.']*\.)?{re.escape(short)}([[:space:]]|$)", "Formalization")
            found = None
            for path, num, line in hits:
                text_ = self.git.show(path)
                m = re.match(r"(?:private |protected )?(?:noncomputable )?(?:theorem|lemma|def) ([\w.']+)", line)
                decl = m.group(1) if m else short
                ns = namespace_at(text_, num)
                cand = f"{ns}.{decl}" if ns else decl
                if cand == full or cand.endswith("." + full) or full.endswith("." + cand):
                    found = (path, num)
                    break
            if not found:
                out.append({"name": full, "file": None})
                continue
            path, num = found
            lines = self.git.show(path).splitlines()
            a, b, trunc = decl_extent(lines, num)
            out.append({"name": full, "file": path, "line_start": a, "line_end": b,
                        "source": "\n".join(lines[a - 1:b]), "truncated": trunc})
        return out

    @staticmethod
    def parse_issues(text: str) -> dict:
        out = {}
        for line in text.splitlines():
            m = re.match(r"#+\s+(.*\bC(\d+)\b.*)$", line)
            if m and m.group(2) not in out:
                title = m.group(1)
                slug = re.sub(r"[^\w\- ]", "", title.lower()).replace(" ", "-")
                out[m.group(2)] = {"title": title, "slug": slug}
        return out

    def parse_coverage(self, text: str) -> dict:
        out: dict = {}
        for line in text.splitlines():
            if not line.startswith("| ") or line.startswith("| ---") or line.startswith("| Source item"):
                continue
            cells = split_md_row(line)
            if len(cells) < 3:
                continue
            labels = [l for l in re.findall(r"`([^`]+)`", cells[0]) if l in self.inv_labels]
            for lab in labels:
                out.setdefault(lab, []).append({"item": cells[0], "evidence": cells[1], "scope": cells[2]})
        return out

    # rendering -----------------------------------------------------------------
    def md(self, text: str, base: str = "docs/") -> str:
        """Tiny Markdown subset: links, bold, code."""
        parts = re.split(r"(`[^`]*`)", text)
        out = []
        for p in parts:
            if p.startswith("`") and p.endswith("`") and len(p) > 1:
                out.append(f"<code>{esc(p[1:-1])}</code>")
                continue
            p = esc(p)
            p = re.sub(r"\*\*(.+?)\*\*", r"<strong>\1</strong>", p)

            def link(m):
                href = m.group(2)
                if not re.match(r"https?://", href):
                    target = str((Path(base) / href).as_posix())
                    parts_ = []
                    for seg in target.split("/"):
                        if seg == "..":
                            parts_ and parts_.pop()
                        elif seg and seg != ".":
                            parts_.append(seg)
                    path, _, frag = "/".join(parts_).partition("#")
                    href = self.git.blob(path) + (f"#{frag}" if frag else "")
                return f'<a href="{attr(href)}">{m.group(1)}</a>'

            p = re.sub(r"\[([^\]]+)\]\(([^)]+)\)", link, p)
            out.append(p)
        return "".join(out)

    def issue_links(self, ids: list) -> str:
        links = []
        for c in ids:
            info = self.issue_slugs[c]
            links.append(f'<a href="{attr(self.git.blob("docs/SOURCE-ISSUES.md"))}#{attr(info["slug"])}" '
                         f'title="{attr(info["title"])}">source issue C{c}</a>')
        return " · ".join(links)

    def card(self, e: Entry) -> str:
        word, cls = STATUS[e.status]
        rec = e.record or {}
        meta = [f'<a href="{attr(self.git.blob(e.file, e.line_start, e.line_end))}">'
                f'{esc(e.file.rsplit("/", 1)[-1])}:{e.line_start}–{e.line_end}</a>']
        if rec.get("evidence"):
            meta.append(f'<a href="{attr(self.git.blob(rec["evidence"]))}">review record</a>')
        if e.issues:
            meta.append(self.issue_links(e.issues))
        scope = f'<p class="scope">{self.md(link_paths(rec["statement_scope"]))}</p>' if rec.get("statement_scope") else ""
        if e.status == "unrecorded":
            scope += ('<p class="scope">This statement entry has no record in the reviewed status ledger, '
                      "so the reader does not show it as proved.</p>")
        parts = [f'<article class="lean-card" id="lean-{attr(e.name)}">',
                 f'<header><span class="status {cls}">{esc(word)}</span>'
                 f'<code class="decl" title="{attr(e.full)}">{esc(e.name)}</code></header>',
                 f'<div class="meta">{" · ".join(meta)}</div>', scope,
                 '<details open><summary>Lean statement</summary>',
                 code_block(e.source, e.line_start), "</details>"]
        if e.proof:
            pr = e.proof
            parts.append(f'<details><summary>Proof <code>{esc(pr["name"])}</code></summary>'
                         f'<div class="meta"><a href="{attr(self.git.blob(pr["file"], pr["line_start"], pr["line_end"]))}">'
                         f'{esc(pr["file"].rsplit("/", 1)[-1])}:{pr["line_start"]}–{pr["line_end"]}</a>'
                         f'{" · applies the library theorem below" if e.exports else ""}</div>'
                         f'{code_block(pr["source"], pr["line_start"])}</details>')
        for ex in e.exports:
            if not ex.get("file"):
                parts.append(f'<details><summary>Library theorem <code>{esc(ex["name"])}</code></summary>'
                             '<p class="scope">Source location not found automatically at this commit.</p></details>')
                continue
            note = " · first 400 lines shown" if ex["truncated"] else ""
            parts.append(f'<details><summary>Library theorem <code>{esc(ex["name"].rsplit(".", 1)[-1])}</code></summary>'
                         f'<div class="meta"><a href="{attr(self.git.blob(ex["file"], ex["line_start"], ex["line_end"]))}">'
                         f'{esc(ex["file"])}:{ex["line_start"]}–{ex["line_end"]}</a>{note}</div>'
                         f'{code_block(ex["source"], ex["line_start"])}</details>')
        parts.append("</article>")
        return "".join(parts)

    def ledger_card(self, label: str, rows: list) -> str:
        cards = []
        for row in rows:
            scope = row["scope"]
            st = "partial" if re.match(r"\s*\*\*Partial", scope) else "ledger"
            word, cls = STATUS[st]
            cards.append(f'<article class="lean-card ledger"><header><span class="status {cls}">{esc(word)}</span>'
                         f'<code class="decl">{esc(label)}</code></header>'
                         f'<p class="scope">{self.md(scope)}</p>'
                         f'<div class="meta">Lean evidence: {self.md(row["evidence"])} · '
                         f'<a href="{attr(self.git.blob("docs/COVERAGE.md"))}">coverage ledger</a></div></article>')
        return "".join(cards)


def classify(name: str, ledger_kind: str, scope: str) -> str:
    """Never show a variant as the printed result, even when the ledger certifies it."""
    low = name.lower()
    if "corrected" in low:
        return "corrected"
    if re.search(r"positiven|restricted|causal|_k\d", low) or scope.strip().lower().startswith("restricted"):
        return "restricted"
    return "original" if ledger_kind == "certified_named_results" else "restricted"


def link_paths(text: str) -> str:
    """Turn bare `docs/...md#frag` mentions into Markdown links (resolved by LeanIndex.md)."""
    return re.sub(r"(?<![(\[`/])(docs/[\w./-]+\.md(?:#[\w-]+)?)", lambda m: f"[{m.group(1)}](../{m.group(1)})", text)


def split_md_row(line: str) -> list:
    cells, cur, tick = [], [], False
    for ch in line.strip().strip("|"):
        if ch == "`":
            tick = not tick
        if ch == "|" and not tick:
            cells.append("".join(cur).strip())
            cur = []
        else:
            cur.append(ch)
    cells.append("".join(cur).strip())
    return cells


KEYWORDS = re.compile(r"(?<![\w.'])(theorem|lemma|def|noncomputable|fun|by|have|show|exact|intro|obtain|refine|"
                      r"calc|let|in|with|match|at|simp|rw|simpa|constructor|rcases|rintro|apply|linarith|"
                      r"nlinarith|positivity|gcongr|field_simp|ring|norm_num|omega|classical|open|namespace|"
                      r"end|where|structure|instance|Prop|Type|Sort|if|then|else|do|return|sorry)(?![\w'])")


def code_block(src: str, first: int) -> str:
    rows = []
    in_comment = False
    for k, line in enumerate(src.splitlines()):
        text = esc(line)
        if in_comment or line.lstrip().startswith(("/-", "--")) or "/--" in line:
            cls = "c"
            if "/-" in line and "-/" not in line.split("/-", 1)[1]:
                in_comment = True
            if "-/" in line:
                in_comment = False if line.rstrip().endswith("-/") or "/-" not in line else in_comment
            body = f'<span class="c">{text}</span>'
        else:
            body = KEYWORDS.sub(r'<span class="k">\1</span>', text)
        rows.append(f'<span class="ln">{first + k}</span>{body}')
    return f'<pre class="lean"><code>{chr(10).join(rows)}</code></pre>'
