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
import sys
from dataclasses import dataclass, field
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "scripts"))
import gen_nodes  # noqa: E402  (one classifier for the reader and the node graph)

REPO = "https://github.com/aaradhyapandeycs/statistical-foundations-rl-lean"

# Exactly four reader labels (plus markers), defined once in scripts/gen_nodes.py and read from the
# node graph; the reader never classifies a status on its own.
LABELS = gen_nodes.SITE_LABELS
MARKERS = gen_nodes.MARKERS
# Marker filter toggles (checkbox id suffix, marker key) in display order; site/static/app.js reads the same ids.
FILTER_MARKERS = (("refuted", "refuted"), ("boundary", "boundary"), ("reading", "reading-dependent"),
                  ("domain", "domain"), ("illposed", "ill-posed"), ("paper", "fails-paper"))


def marker_toggles() -> str:
    """The marker filter checkboxes of the results index and the graph's node table."""
    return "\n".join(f'<label class="toggle"><input type="checkbox" id="f-{i}"> '
                     f'<span class="marker mk-{m}">{html.escape(MARKERS[m], quote=False)}</span></label>'
                     for i, m in FILTER_MARKERS)
# A statement entry (never an item) may also be a supporting entry: its `_holds` wrapper proves it in Lean,
# but the item's ledger record is another entry, so it is not counted for the item. Items keep exactly
# the four labels above; this chip appears only on entry cards.
ENTRY_LABELS = dict(LABELS, supporting=("supporting entry, proved in Lean", "st-supporting"))
# Internal order of a statement entry's own classification (for sorting cards only; never shown).
ENTRY_ORDER = ["original", "corrected", "restricted", "cov-printed", "cov-corrected", "cov-restricted",
               "unrecorded", "partial"]


def chip(label, markers=(), sub: str = "", issues: str = "") -> str:
    """Status chip: one of the four labels (or none), then markers and the incomplete sub-reason."""
    out = []
    if label == "supporting":
        # Not one of the four status labels: plain muted text, never a badge.
        note = "Supporting Lean entry (not a status)" + (f": {sub}" if sub else "")
        out.append(f'<span class="entry-note">{esc(note)}</span>')
        sub = ""
    elif label:
        word, cls = ENTRY_LABELS[label]
        out.append(f'<span class="status {cls}">{esc(word)}</span>')
    for m in markers:
        out.append(f'<span class="marker mk-{m}">{esc(MARKERS[m])}</span>')
    if sub and label in ("incomplete", None):
        out.append(f'<span class="subreason">{esc(sub)}</span>')
    if issues:
        out.append(f'<span class="issues">{issues}</span>')
    return "".join(out)


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
        cov_text = git.show("docs/COVERAGE.md")
        self.coverage = self.parse_coverage(cov_text)
        self.coverage_rows = gen_nodes.parse_coverage(cov_text)
        self.disclosures = self.parse_disclosures(git.show("docs/SOURCE-ISSUES.md"))
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
                    e.status = classify(name, kind, e.record.get("statement_scope", ""),
                                        e.record.get("statement_variant"))
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
                elif gen_nodes.coverage_partial(name, self.coverage_rows):
                    e.status = "partial"
                elif gen_nodes.coverage_variant(name, self.coverage_rows):
                    # No named-ledger record, but the coverage ledger (the reviewed ledger for
                    # prose claims, remarks and displays) records this entry as proved.
                    e.status = "cov-" + gen_nodes.classify(name, None, "", self.coverage_rows)
                scope = (e.record or {}).get("statement_scope", "") + " " + doc
                e.issues = [c for c in dict.fromkeys(gen_nodes.CID_RE.findall(scope)) if c in self.issue_slugs]
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

    @staticmethod
    def parse_disclosures(text: str) -> list:
        """Bullets of SOURCE-ISSUES.md's "Statement-index scope disclosures" section."""
        m = re.search(r"^## Statement-index scope disclosures\n(.*?)(?=^## )", text, re.S | re.M)
        if not m:
            return []
        out, cur = [], None
        for line in m.group(1).splitlines():
            if line.startswith("- "):
                cur = [line[2:].strip()]
                out.append(cur)
            elif cur is not None and line.strip():
                cur.append(line.strip())
            elif not line.strip():
                cur = None
        return [" ".join(b) for b in out]

    def disclosure_for(self, e) -> str:
        """The scope-disclosure bullet that names this entry (or, failing that, its source label)."""
        keys = [f"`{e.name}`"] + [f"`{l}`" for l in ((e.record or {}).get("source_label"),) if l] \
            + ([f"`{e.labels[0]}`"] if e.labels and not e.record else [])
        for key in keys:
            for b in self.disclosures:
                if key in b:
                    return b
        return ""

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
    def md(self, text: str, base: str = "docs/", doc: str | None = None) -> str:
        """Tiny Markdown subset: links, bold, code. Ledger shorthand is reworded for readers.
        `doc` is the Markdown file the text was taken from: a bare `#anchor` link points into it."""
        parts = re.split(r"(`[^`]*`)", reader_wording(text))
        out = []
        for p in parts:
            if p.startswith("`") and p.endswith("`") and len(p) > 1:
                out.append(f"<code>{esc(p[1:-1])}</code>")
                continue
            p = re.sub(r"(?<![\\$])\$([^$\n]+?)\$", lambda m: "\\(" + m.group(1) + "\\)", p)
            p = esc(p)

            def link(m):
                href = m.group(2)
                if href.startswith("#") and doc:
                    href = self.git.blob(doc) + href
                elif not re.match(r"https?://", href):
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
        return bold("".join(out))

    def issue_links(self, ids: list) -> str:
        links = []
        for c in ids:
            info = self.issue_slugs[c]
            links.append(f'<a href="{attr(self.git.blob("docs/SOURCE-ISSUES.md"))}#{attr(info["slug"])}" '
                         f'title="{attr(info["title"])}">source issue C{c}</a>')
        return " · ".join(links)

    def card(self, e: Entry, view: dict) -> str:
        """One Lean entry, math first: label and markers; what is proved (the ledger's display_note,
        TeX rendered); origin; links; then closed disclosures with the Lean code and the full scope."""
        rec = e.record or {}
        scope_text = rec.get("statement_scope", "")
        links = [f'<a href="{attr(self.git.blob(e.file, e.line_start, e.line_end))}">Lean statement '
                 f'({esc(e.file.rsplit("/", 1)[-1])}:{span(e.line_start, e.line_end)})</a>']
        if view.get("tex"):
            links.insert(0, view["tex"])
        if rec.get("evidence"):
            links.append(f'<a href="{attr(self.git.blob(rec["evidence"]))}">review record (AI agent)</a>')
        if view.get("audit"):
            links.append(view["audit"])
        if e.issues or view.get("node_issues"):
            links.append(self.issue_links(e.issues or view["node_issues"]))
        note = view.get("note") or ""
        body = []
        if note:
            body.append(f'<p class="what tex2jax_process"><strong>What is proved.</strong> {self.md(note)}</p>')
        elif scope_text:
            # No reader note in the ledger yet: show the reviewed scope itself, beside the result.
            body.append(f'<p class="what tex2jax_process"><strong>What is proved</strong> (reviewed ledger '
                        f'scope). {self.md(link_paths(scope_text))}</p>')
        elif view.get("cov_note"):
            # A remark or display: its reviewed record is the coverage-ledger row, shown in full.
            body.append(f'<p class="what tex2jax_process"><strong>What is proved</strong> (reviewed coverage-ledger '
                        f'row). {self.md(view["cov_note"])}</p>')
        if view.get("refuted"):
            body.append(f'<p class="refuted-line">{view["refuted"]}</p>')
        if view.get("correction"):
            body.append(f'<p class="ours">{esc(view["correction"])}</p>')
        if view.get("origin"):
            body.append(f'<p class="origin">{view["origin"]}</p>')
        d = self.disclosure_for(e) if "statement-index-scope-disclosures" in scope_text else ""
        d = d or view.get("disclosure") or ""
        if d:
            href = f'{attr(self.git.blob("docs/SOURCE-ISSUES.md"))}#statement-index-scope-disclosures'
            first, rest = split_first_sentence(d)
            more = (f'<details class="more"><summary>Full disclosure</summary><p class="scope tex2jax_process">'
                    f'{self.md(d, doc="docs/SOURCE-ISSUES.md")}</p></details>' if rest else "")
            body.append(f'<p class="scope disclosure tex2jax_process"><strong>Disclosed restriction</strong> '
                        f'(<a href="{href}">source issues: scope disclosures</a>): {self.md(first, doc="docs/SOURCE-ISSUES.md")}'
                        f'{" …" if rest else ""}</p>{more}')
        if view.get("explain"):
            body.append(f'<p class="scope">{view["explain"]}</p>')
        parts = [f'<article class="lean-card" id="lean-{attr(e.name)}">',
                 f'<header>{chip(view.get("label"), view.get("markers", ()), view.get("sub", ""))}'
                 f'<code class="decl" title="{attr(e.full)}">{esc(e.name)}</code></header>',
                 "".join(body), f'<div class="meta">{" · ".join(links)}</div>',
                 '<details><summary>Lean statement</summary>', code_block(e.source, e.line_start), "</details>"]
        if e.proof:
            pr = e.proof
            parts.append(f'<details><summary>Proof <code>{esc(pr["name"])}</code></summary>'
                         f'<div class="meta"><a href="{attr(self.git.blob(pr["file"], pr["line_start"], pr["line_end"]))}">'
                         f'{esc(pr["file"].rsplit("/", 1)[-1])}:{span(pr["line_start"], pr["line_end"])}</a>'
                         f'{" · applies the library theorem below" if e.exports else ""}</div>'
                         f'{code_block(pr["source"], pr["line_start"])}</details>')
        for ex in e.exports:
            if not ex.get("file"):
                parts.append(f'<details><summary>Library theorem <code>{esc(ex["name"])}</code></summary>'
                             '<p class="scope">Source location not found automatically at this commit.</p></details>')
                continue
            tnote = " · first 400 lines shown" if ex["truncated"] else ""
            parts.append(f'<details><summary>Library theorem <code>{esc(ex["name"].rsplit(".", 1)[-1])}</code></summary>'
                         f'<div class="meta"><a href="{attr(self.git.blob(ex["file"], ex["line_start"], ex["line_end"]))}">'
                         f'{esc(ex["file"])}:{span(ex["line_start"], ex["line_end"])}</a>{tnote}</div>'
                         f'{code_block(ex["source"], ex["line_start"])}</details>')
        if note and scope_text:
            parts.append(f'<details><summary>Full ledger scope</summary><p class="scope tex2jax_process">'
                         f'{self.md(link_paths(scope_text))}</p></details>')
        parts.append("</article>")
        return "".join(parts)

    def ledger_card(self, label: str, rows: list, view: dict) -> str:
        """A coverage-ledger row with no statement entry beside it; the label comes from the node."""
        cards = []
        for row in rows:
            cards.append(f'<article class="lean-card ledger"><header><code class="decl">{esc(label)}</code> '
                         f'{chip(view.get("label"), view.get("markers", ()), view.get("sub", ""))}</header>'
                         f'<p class="scope tex2jax_process">{self.md(row["scope"])}</p>'
                         f'<div class="meta">Lean evidence: {self.md(row["evidence"])} · '
                         f'<a href="{attr(self.git.blob("docs/COVERAGE.md"))}">coverage ledger</a></div></article>')
        return "".join(cards)


def bold(html_text: str) -> str:
    """Markdown **bold** outside <code> spans, also when it spans inline code (**Implied by `X`**)."""
    parts = re.split(r"(<code>.*?</code>)", html_text)
    if sum(p.count("**") for i, p in enumerate(parts) if i % 2 == 0) % 2:
        return html_text  # unbalanced: leave as is
    out, on = [], False
    for i, p in enumerate(parts):
        if i % 2 == 0:
            bits = p.split("**")
            for k, b in enumerate(bits):
                if k:
                    out.append("</strong>" if on else "<strong>")
                    on = not on
                out.append(b)
        else:
            out.append(p)
    return "".join(out)


def split_first_sentence(text: str) -> tuple:
    """(first sentence, rest) at the first '. ' outside backticks and parentheses, after 60 characters."""
    depth, tick = 0, False
    for i, ch in enumerate(text):
        if ch == "`":
            tick = not tick
        elif not tick and ch in "([":
            depth += 1
        elif not tick and ch in ")]":
            depth = max(0, depth - 1)
        elif ch == "." and not tick and depth == 0 and i >= 60 and text[i + 1:i + 2] == " " \
                and not re.search(r"(?:e\.g|i\.e|cf|resp|Thm|Eq|Lemma|eq)$", text[max(0, i - 6):i]):
            return text[:i + 1], text[i + 1:].strip()
    return text, ""


def classify(name: str, ledger_kind: str, scope: str, declared: str | None = None) -> str:
    """Never show a variant as the printed result, even when the ledger records it.
    Same rule as scripts/gen_nodes.py `classify` (shared code)."""
    v = gen_nodes.classify(name, ledger_kind, scope, declared=declared)
    return "original" if v == "printed" else v


# Display-only rewording of internal ledger shorthand (the ledgers keep their machine-checked anchors,
# e.g. the dated `user decision YYYY-MM-DD` that gen_nodes requires). Never changes a status.
READER_WORDING = [
    (r"Independently plan-checked and source-reviewed", "Independently reviewed by AI agents (plan and source review)"),
    (r"Independently critic-reviewed", "Independently reviewed by an AI agent"),
    (r"\bcritic-reviewed\b", "independently reviewed"),
    (r"\bopen source-fidelity finding\b", "open source issue"),
    (r"\bsource-fidelity finding\b", "source issue"),
    (r"\buser decision (\d{4}-\d{2}-\d{2})(?: \(cited-results rule\))?", r"project decision (\1)"),
    (r"\bUser decision (\d{4}-\d{2}-\d{2})(?: \(cited-results rule\))?", r"Project scope decision (\1)"),
    (r"\bby (?:a |the )?project decision \((\d{4}-\d{2}-\d{2})\)", r"by a project decision (\1)"),
    # the "no author approval" banner is on every page; keep the per-card point about the printed theorem
    (r"Not author-approved; this does not prove the printed theorem\.", "This does not prove the printed theorem."),
    (r"(?<=[.)]) Not author-approved\.", ""),
    (r"\[(?:P\d+ review|m\d+[^\]]*)\]\(", "[review]("),
]


def reader_wording(text: str) -> str:
    for pat, rep in READER_WORDING:
        text = re.sub(pat, rep, text)
    return text


def span(a: int, b: int) -> str:
    return f"{a}" if a == b else f"{a}–{b}"


def link_paths(text: str) -> str:
    """Turn bare `docs/...md#frag` mentions into Markdown links (resolved by LeanIndex.md)."""
    return re.sub(r"(?<![(\[`/])(docs/[\w./-]+\.md(?:#[\w-]+)?)", lambda m: f"[{m.group(1)}](../{m.group(1)})", text)


def split_md_row(line: str) -> list:
    """Cells of a Markdown table row. `|` inside backticks, or escaped as `\\|`, is literal."""
    cells, cur, tick = [], [], False
    for ch in line.strip().strip("|"):
        if ch == "`":
            tick = not tick
        if ch == "|" and cur and cur[-1] == "\\":
            cur[-1] = "|"
        elif ch == "|" and not tick:
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
# Binders and big operators, highlighted like keywords so quantifier structure stands out.
BINDERS = re.compile(r"([∀∃λ∑∏∫⨆⨅])")


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
            body = BINDERS.sub(r'<span class="k">\1</span>', KEYWORDS.sub(r'<span class="k">\1</span>', text))
        rows.append(f'<span class="ln">{first + k}</span>{body}')
    return f'<pre class="lean"><code>{chr(10).join(rows)}</code></pre>'
