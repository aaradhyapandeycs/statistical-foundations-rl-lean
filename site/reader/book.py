"""Book model: pinned TeX + source inventory -> chapters, pages and labels."""

from __future__ import annotations

import hashlib
import html
import json
import re
import shutil
import subprocess
from dataclasses import dataclass, field
from pathlib import Path

from .tex import Block, FileConverter, assemble, label_id, mask_comments, mathjax_compat, parse_macros, read_group

TEX = "source/upstream/tex"
MAIN = "StatisticalRL-nowplain.tex"
ENV_NAMES = {"theorem": "Theorem", "lemma": "Lemma", "corollary": "Corollary",
             "proposition": "Proposition", "definition": "Definition", "assumption": "Assumption",
             "claim": "Claim", "example": "Example", "remark": "Remark", "conjecture": "Conjecture",
             "fact": "Fact"}
# Macros that MathJax lacks or that only matter for layout.
MATH_OVERRIDES = {"xspace": (0, None, ""), "mathds": (1, None, "\\mathbb{#1}"),
                  "bm": (1, None, "\\boldsymbol{#1}"), "ensuremath": (1, None, "#1"),
                  "mycommentbegin": (0, None, ""), "mycommentend": (0, None, ""),
                  "arxiv": (1, None, ""), "book": (1, None, "#1"),
                  "yxc": (1, None, ""), "yc": (1, None, ""), "yuting": (1, None, ""), "yly": (1, None, "")}


def esc(t: str) -> str:
    return html.escape(t, quote=False)


def attr(t: str) -> str:
    return html.escape(t, quote=True)


@dataclass
class Page:
    id: str
    title: str
    number: str | None
    chapter: str | None
    level: int
    blocks: list = field(default_factory=list)


class Book:
    def __init__(self, root: Path, out: Path):
        self.root = root
        self.out = out
        self.tex_root = root / TEX
        self.provenance = json.loads((root / "source/provenance.json").read_text())
        self.verify_source()
        self.inventory = json.loads((root / "docs/source-inventory.json").read_text())
        self.by_pos: dict = {}
        for e in self.inventory["entries"]:
            r = e["source_ranges"][0]
            self.by_pos.setdefault((r["file"], r["line_start"]), []).append(e)
        self.by_id = {e["id"]: e for e in self.inventory["entries"]}
        # The inventory leaves figure numbers empty. The class loads `book`,
        # which numbers figures within chapters; computed here, disclosed on About.
        fig_count: dict = {}
        for e in self.inventory["entries"]:
            if e["kind"] == "figure" and not e.get("number"):
                fig_count[e["chapter"]] = fig_count.get(e["chapter"], 0) + 1
                e["number"] = f'{e["chapter"]}.{fig_count[e["chapter"]]}'
        self.label_owner = {l["label"]: self.by_id.get(l["owner_id"]) for l in self.inventory["labels"]}
        self.macros = self.load_macros()
        self.bib = self.load_bib()
        self.cited: dict = {}
        self.unknown: dict = {}
        self.warnings: list = []
        self.footnotes = 0
        self.images: dict = {}
        self.used_pos: dict = {}

    # source ----------------------------------------------------------------
    def verify_source(self):
        bad = []
        for name, digest in self.provenance["source_files"].items():
            path = self.tex_root / name
            if not path.is_file() or hashlib.sha256(path.read_bytes()).hexdigest() != digest:
                bad.append(name)
        if bad:
            raise SystemExit(f"Pinned TeX missing or modified ({', '.join(bad[:5])}); "
                             "run `python3 scripts/fetch_source.py` first.")

    def rel(self, path: Path) -> str:
        return path.relative_to(self.root).as_posix()

    def load_macros(self) -> dict:
        texts = [(self.tex_root / "chapters/commands.tex").read_text()]
        main = (self.tex_root / MAIN).read_text()
        texts.append(main.split("\\begin{document}")[0])
        for f in sorted((self.tex_root / "chapters").glob("*.tex")):
            if f.name != "commands.tex":
                texts.append(f.read_text())
        macros = {}
        for t in texts:
            macros.update(parse_macros(t))
        macros.update(MATH_OVERRIDES)
        return macros

    def mathjax_macros(self) -> dict:
        out = {}
        for name, (n, default, body) in self.macros.items():
            body = mathjax_compat(body)
            if "\\begin{comment}" in body or "\\end{comment}" in body:
                continue
            if n == 0:
                out[name] = body
            elif default is None:
                out[name] = [body, n]
            else:
                out[name] = [body, n, default]
        return out

    # inventory ---------------------------------------------------------------
    def inventory_at(self, file: str, line: int, kinds: tuple):
        cands = [e for e in self.by_pos.get((file, line), []) if e["kind"] in kinds]
        if not cands:
            return None
        key = (file, line, kinds)
        k = self.used_pos.get(key, 0)
        self.used_pos[key] = k + 1
        return cands[k] if k < len(cands) else cands[-1]

    def label_number(self, label: str):
        owner = self.label_owner.get(label)
        if not owner:
            return None, None
        if owner["kind"] == "display":
            for row in owner.get("rows", []):
                if label in row.get("labels", []):
                    return row.get("number"), "equation"
            return owner.get("number"), "equation"
        return owner.get("number"), owner["kind"]

    def env_title(self, kind: str) -> str:
        return ENV_NAMES.get(kind, kind.capitalize())

    # includes, figures, citations ---------------------------------------------
    def include(self, path: str) -> list:
        path = path if path.endswith(".tex") else path + ".tex"
        target = self.tex_root / path
        if not target.is_file():
            self.warn(f"missing include {path}")
            return []
        conv = FileConverter(self, self.rel(target), target.read_text())
        return conv.convert()

    def image(self, path: str) -> str:
        src = None
        for cand in (path, path + ".png", path + ".pdf", path + ".jpg"):
            if (self.tex_root / cand).is_file():
                src = self.tex_root / cand
                break
        if src is None:
            self.warn(f"figure file not in the arXiv source: {path}")
            return f'<span class="missing-figure">Figure file <code>{esc(path)}</code> is not in the arXiv source.</span>'
        name = src.stem + ".png"
        dest = self.out / "figures" / name
        if name not in self.images:
            dest.parent.mkdir(parents=True, exist_ok=True)
            if src.suffix.lower() == ".pdf":
                if shutil.which("pdftoppm"):  # Linux CI (poppler-utils)
                    cmd = ["pdftoppm", "-png", "-r", "216", "-singlefile", str(src), str(dest.with_suffix(""))]
                elif shutil.which("sips"):  # macOS
                    cmd = ["sips", "-s", "format", "png", "-s", "dpiWidth", "216", "-s", "dpiHeight", "216",
                           str(src), "--out", str(dest)]
                else:
                    cmd = None
                r = subprocess.run(cmd, capture_output=True, text=True) if cmd else None
                if r is None or r.returncode != 0 or not dest.exists():
                    why = (r.stderr or r.stdout).strip().splitlines()[-1:] if r else ["no converter found"]
                    self.warn(f"could not convert {src.name} to PNG: {' '.join(why) or 'no output file'}")
                    return f'<span class="missing-figure">Figure <code>{esc(path)}</code> could not be converted.</span>'
            else:
                shutil.copyfile(src, dest)
            self.images[name] = src.name
        return f'<img src="figures/{attr(name)}" alt="Figure from the book ({attr(src.name)})" loading="lazy">'

    def load_bib(self) -> dict:
        text = (self.tex_root / "StatisticalRL_merged.bib").read_text()
        out = {}
        for m in re.finditer(r"@(\w+)\s*\{\s*([^,\s]+)\s*,", text):
            key = m.group(2)
            start = m.end()
            depth, p = 1, start
            while p < len(text) and depth:
                if text[p] == "{":
                    depth += 1
                elif text[p] == "}":
                    depth -= 1
                p += 1
            body = text[start:p - 1]
            fields = {}
            for f in re.finditer(r"(\w+)\s*=\s*", body):
                q = f.end()
                if q < len(body) and body[q] == "{":
                    a, b, _ = read_group(body, q, len(body))
                    val = body[a:b]
                elif q < len(body) and body[q] == '"':
                    end = body.find('"', q + 1)
                    val = body[q + 1:end]
                else:
                    val = re.match(r"[^,\n]*", body[q:]).group(0)
                fields.setdefault(f.group(1).lower(), val)
            out[key] = {"type": m.group(1).lower(), **fields}
        return out

    @staticmethod
    def detex(text: str) -> str:
        text = re.sub(r"\\[`'^\"~=.uvHckr]\s*\{?\\?([A-Za-z])\}?", r"\1", text)
        text = re.sub(r"\\&", "&", text)
        text = re.sub(r"\\[A-Za-z]+\s*", "", text)
        text = text.replace("{", "").replace("}", "").replace("~", " ").replace("--", "–")
        return re.sub(r"\s+", " ", text).strip()

    def authors(self, key: str):
        e = self.bib.get(key)
        if not e:
            return key, ""
        names = [n.strip() for n in re.split(r"\s+and\s+", e.get("author", e.get("editor", ""))) if n.strip()]
        lasts = []
        for n in names:
            n = self.detex(n)
            lasts.append(n.split(",")[0].strip() if "," in n else n.split()[-1] if n.split() else n)
        if not lasts:
            who = self.detex(e.get("title", key))[:40]
        elif len(lasts) == 1:
            who = lasts[0]
        elif len(lasts) == 2:
            who = f"{lasts[0]} and {lasts[1]}"
        else:
            who = f"{lasts[0]} et al."
        return who, self.detex(e.get("year", ""))

    def cite(self, cmd: str, keys: list, opts: list) -> str:
        items = []
        for k in keys:
            self.cited[k] = True
            who, year = self.authors(k)
            link = f'<a class="cite" href="references.html#ref-{attr(k)}">'
            if cmd.startswith("citet") or cmd == "citeauthor":
                txt = who if cmd == "citeauthor" else f"{esc(who)} ({esc(year)})"
            elif cmd == "citeyear":
                txt = esc(year)
            else:
                txt = f"{esc(who)}, {esc(year)}" if year else esc(who)
            items.append(f"{link}{txt}</a>")
        pre = post = ""
        if len(opts) == 1:
            post = opts[0]
        elif len(opts) == 2:
            pre, post = opts
        body = "; ".join(items)
        if cmd.startswith("citet") or cmd in ("citeauthor", "citeyear"):
            return body + (f" ({post})" if post else "")
        inner = (f"{pre} " if pre else "") + body + (f", {post}" if post else "")
        return inner if cmd == "citealp" else f"({inner})"

    def cite_plain(self, keys: str) -> str:
        out = []
        for k in [k.strip() for k in keys.split(",") if k.strip()]:
            self.cited[k] = True
            who, year = self.authors(k)
            out.append(f"{who}, {year}")
        return "(" + "; ".join(out) + ")"

    def next_footnote(self) -> int:
        self.footnotes += 1
        return self.footnotes

    def warn(self, msg: str):
        self.warnings.append(msg)

    # chapters and pages --------------------------------------------------------
    def chapter_files(self) -> list:
        main = mask_comments((self.tex_root / MAIN).read_text())
        body = main.split("\\begin{document}", 1)[1]
        return re.findall(r"\\input\{([^}]*)\}", body)

    def convert_all(self):
        """Return (front, chapters) where chapters is a list of block lists."""
        files = self.chapter_files()
        front, chapters, back = [], [], []
        for f in files:
            parts = self.include(f)
            blocks = assemble(parts)
            name = Path(f).stem
            if name == "abstract":
                front = blocks
            elif name == "ack":
                back = blocks
            else:
                chapters.append(blocks)
        return front, chapters, back

    def paginate(self, chapters: list) -> list:
        pages = []
        for blocks in chapters:
            cur = None
            chap_no = None
            for b in blocks:
                if b.kind == "heading" and b.level is not None and b.level <= 1:
                    if b.level == 0:
                        chap_no = b.number
                        pid = f"ch{b.number}" if b.number else f"ch-{len(pages)}"
                    else:
                        pid = f"ch{b.number.replace('.', '-')}" if b.number else f"{pages[-1].id}-s{len(pages)}"
                    cur = Page(pid, b.title, b.number, chap_no, b.level)
                    pages.append(cur)
                if cur is None:
                    cur = Page(f"front-{len(pages)}", "Front matter", None, None, 0)
                    pages.append(cur)
                cur.blocks.append(b)
        return pages
