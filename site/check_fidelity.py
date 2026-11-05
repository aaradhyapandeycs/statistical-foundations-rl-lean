#!/usr/bin/env python3
"""Check that the built site reproduces the book faithfully.

    python3 site/check_fidelity.py [--build site/_build]

Two independent checks, neither using the site's own converter:

1. Prose, against the arXiv PDF (source/upstream/2610.41903v1.pdf, hash-pinned).
   Every prose word on the site must be found, in order, in the PDF's text, and
   every word of the PDF body that the TeX uses as a prose word must be found,
   in order, on the site.
   Comparison is letter-level, so PDF line breaks, hyphenation and glued words
   do not matter; chunks are aligned locally, and any residual run is settled
   by an in-order search of the whole other side.
2. Formulas, against the TeX: every formula extracted from the chapter files by
   a separate scanner must appear verbatim on the site, modulo the intended
   changes (labels removed, equation tags added, references resolved).

Exit status 1 if anything is unresolved. Needs `pdftotext` (poppler) or, on
macOS, Swift with PDFKit (site/tools/pdftext.swift).
"""

from __future__ import annotations

import argparse
import glob
import html
import re
import shutil
import subprocess
import sys
import os
import unicodedata
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
PDF = ROOT / "source/upstream/2610.41903v1.pdf"
TEX = ROOT / "source/upstream/tex/chapters"


def letters(t: str) -> str:
    return re.sub(r"[^a-z]", "", unicodedata.normalize("NFKC", t).lower())


def pdf_text() -> str:
    if shutil.which("pdftotext"):
        # -raw keeps content-stream order, which follows the typeset order of the
        # TeX; poppler's default reading-order heuristic reorders math and floats.
        return subprocess.run(["pdftotext", "-raw", "-enc", "UTF-8", str(PDF), "-"], capture_output=True,
                              text=True, check=True).stdout
    if shutil.which("swift"):
        return subprocess.run(["swift", str(HERE / "tools/pdftext.swift"), str(PDF)], capture_output=True,
                              text=True, check=True).stdout
    raise SystemExit("need pdftotext (poppler-utils) or swift (macOS) to read the PDF")


# ---------------------------------------------------------------- site text
def page_order(build: Path) -> list:
    order = ["index"]
    for h in re.findall(r'<a href="(ch[\d-]+)\.html"', (build / "ch1.html").read_text()):
        if h not in order:
            order.append(h)
    return order + ["acknowledgements"]


def site_prose(build: Path, page: str) -> str:
    s = (build / f"{page}.html").read_text()
    if page == "index":
        m = re.search(r'<section class="abstract">(.*?)</section>', s, re.S)
        s = m.group(1) if m else ""
    else:
        s = re.search(r'<main id="main">(.*)</main>', s, re.S).group(1)
        s = re.sub(r'<aside class="lean-col".*?</aside>', " ", s, flags=re.S)
        s = re.sub(r'<div class="cols-head">.*?</div>|<nav class="pager">.*?</nav>', " ", s, flags=re.S)
    s = re.sub(r'<details class="tex-src">.*?</details>', " ", s, flags=re.S)
    s = re.sub(r'<span class="tex2jax_process">.*?</span>', " ", s, flags=re.S)
    s = re.sub(r'<div class="md[^"]*">.*?</div>', " ", s, flags=re.S)
    s = re.sub(r'<a class="(?:cite|ref)"[^>]*>.*?</a>', " ", s, flags=re.S)
    s = re.sub(r'<span class="fn-text"[^>]*>.*?</span></span>', " ", s, flags=re.S)
    return html.unescape(re.sub(r"<[^>]+>", " ", s))


# ---------------------------------------------------------------- alignment
def scan(words: list, stream: str, chunk: int = 40, gap: int = 5000) -> list:
    """Words of each chunk must appear in order near the chunk's rarest long word."""
    misses = []
    for c0 in range(0, len(words), chunk):
        ch = words[c0:c0 + chunk]
        longs = [(stream.count(w), j) for j, w in enumerate(ch) if len(w) >= 7]
        longs = [x for x in longs if x[0] > 0] or longs
        if not longs or longs[0][0] == 0 and len(longs) == 1:
            misses.extend(range(c0, c0 + len(ch)))
            continue
        _, ja = min(longs)
        best, start = None, 0
        for _ in range(60):
            occ = stream.find(ch[ja], start)
            if occ < 0:
                break
            start = occ + 1
            miss, pos = [], occ
            for j in range(ja - 1, -1, -1):
                i = stream.rfind(ch[j], max(0, pos - gap), pos)
                if i < 0:
                    miss.append(j)
                else:
                    pos = i
            pos = occ + len(ch[ja])
            for j in range(ja + 1, len(ch)):
                i = stream.find(ch[j], pos, pos + gap)
                if i < 0:
                    miss.append(j)
                else:
                    pos = i + len(ch[j])
            if best is None or len(miss) < len(best):
                best = miss
                if not miss:
                    break
        misses.extend(c0 + j for j in (best if best is not None else range(len(ch))))
    return sorted(misses)


def runs(idx: list) -> list:
    out, cur = [], []
    for k in idx:
        if cur and k != cur[-1] + 1:
            out.append(cur)
            cur = []
        cur.append(k)
    if cur:
        out.append(cur)
    return out


def in_order_anywhere(ws: list, stream: str, gap: int = 3000) -> bool:
    for m in re.finditer(re.escape(ws[0]), stream):
        p, ok = m.end(), True
        for w in ws[1:]:
            i = stream.find(w, p, p + gap)
            if i < 0:
                ok = False
                break
            p = i + len(w)
        if ok:
            return True
    return False


# ---------------------------------------------------------------- formulas
ENV = r"(equation|align|gather|multline|flalign|alignat|eqnarray|displaymath)(\*?)"


def drop_group(t: str, cmd: str) -> str:
    out, i = [], 0
    while True:
        j = t.find(cmd + "{", i)
        if j < 0:
            return "".join(out) + t[i:]
        out.append(t[i:j])
        k, d = j + len(cmd) + 1, 1
        while k < len(t) and d:
            if t[k - 1] != "\\":
                d += {"{": 1, "}": -1}.get(t[k], 0)
            k += 1
        i = k


def norm_math(m: str) -> str:
    m = drop_group(m, "\\arxiv")
    m = re.sub(r"\\label\s*\{[^{}]*\}", "", m)
    m = re.sub(r"\\(nonumber|notag)(?![A-Za-z])", "", m)
    m = re.sub(r"\\tag\{[^{}]*\}", "", m)
    m = re.sub(r"\\(eqref|ref|cref|Cref)\s*\{[^{}]*\}", "", m)
    m = re.sub(r"\\text\{\(?[0-9][0-9.a-z]*\)?\}", "", m)
    m = re.sub(r"\\cite[a-z]*\*?(\[[^\]]*\])*\s*\{[^{}]*\}", "", m)
    m = re.sub(r"\\text\{\([^{}]*\d{4}[a-z]?\)\}", "", m)
    m = re.sub(r"\\mathop\s*(\\(?:mathbb|mathrm|mathsf|mathcal|mathbf|mathds|operatorname)\s*\{[^{}]*\})",
               r"\\mathop{\1}", m)
    m = re.sub(r"\\(begin|end)\{" + ENV + r"\}(\{[^{}]*\})?", "", m)
    return re.sub(r"\s+", "", m)


def tex_formulas() -> list:
    out = []
    for f in sorted(glob.glob(str(TEX / "*.tex"))):
        if f.endswith("commands.tex"):
            continue
        t = Path(f).read_text()
        t = re.sub(r"(?<!\\)%[^\n]*", "", t)
        t = re.sub(r"\\begin\{comment\}.*?\\end\{comment\}", "", t, flags=re.S)
        t = drop_group(t, "\\arxiv")
        display = r"\$\$(.+?)\$\$|(?<!\\)\\\[(.+?)\\\]|\\begin\{" + ENV + r"\}(.+?)\\end\{\3\4\}"
        for m in re.finditer(display, t, re.S):
            out.append((Path(f).name, m.group(1) or m.group(2) or m.group(5)))
        rest = re.sub(display, " ", t, flags=re.S)
        for m in re.finditer(r"(?<!\\)\$(.+?)(?<!\\)\$|\\\((.+?)\\\)", rest, re.S):
            out.append((Path(f).name, m.group(1) or m.group(2)))
    return out


KEY_ARGS = r"\\(?:cite[a-z]*|[a-z]*ref|label|input|include|includegraphics|url|href|bibliography[a-z]*)\*?(?:\[[^\]]*\])*\{[^}]*\}"


def tex_vocabulary() -> set:
    """Prose words of the book's TeX: everything outside math, comments,
    command names and key arguments (citation keys, labels, file names).
    Used to drop PDF tokens that are glued math or citation text, so the
    check does not depend on an operating-system word list."""
    words = set()
    for f in sorted(glob.glob(str(TEX / "*.tex")) + glob.glob(str(TEX.parent / "*.tex"))):
        if f.endswith("commands.tex"):
            continue
        t = Path(f).read_text()
        t = re.sub(r"(?<!\\)%[^\n]*", "", t)
        t = re.sub(r"\\begin\{comment\}.*?\\end\{comment\}", "", t, flags=re.S)
        t = re.sub(r"\$\$.+?\$\$|(?<!\\)\\\[.+?\\\]|\\begin\{" + ENV + r"\}.+?\\end\{\1\2\}", " ", t, flags=re.S)
        t = re.sub(r"(?<!\\)\$.+?(?<!\\)\$|\\\(.+?\\\)", " ", t, flags=re.S)
        t = re.sub(KEY_ARGS, " ", t)
        t = re.sub(r"\\[A-Za-z]+", " ", t)
        words.update(w.lower() for w in re.findall(r"[A-Za-z]+", t))
    return words


def site_math(build: Path) -> str:
    parts = []
    for f in glob.glob(str(build / "*.html")):
        s = Path(f).read_text()
        for m in re.finditer(r'<span class="tex2jax_process">(.*?)</span>|<div class="md[^"]*">(.*?)</div>', s, re.S):
            parts.append(html.unescape(re.sub(r"<[^>]+>", "", m.group(1) if m.group(1) is not None else m.group(2))))
    return norm_math("\n".join(parts))


# ---------------------------------------------------------------- main
LOG: list = []


def out(line: str) -> None:
    print(line)
    LOG.append(line)


def annotate(failures: int) -> None:
    """In GitHub Actions, repeat the report as an annotation: annotations are
    readable through the public API, step logs need a signed-in account."""
    if os.environ.get("GITHUB_ACTIONS") == "true":
        level = "error" if failures else "notice"
        body = "\n".join(LOG)[:30000].replace("%", "%25").replace("\r", "%0D").replace("\n", "%0A")
        print(f"::{level} title=Fidelity check::{body}")


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--build", default=str(HERE / "_build"))
    ap.add_argument("--dump-pdf-text", help="also write the extracted PDF text here, for debugging")
    args = ap.parse_args()
    build = Path(args.build)
    failures = 0

    order = page_order(build)
    pages = [site_prose(build, p) for p in order]
    site_words = [w.lower() for p in pages for w in re.findall(r"[A-Za-z]+", p) if len(w) >= 4]
    site_l = letters(" ".join(pages))
    everything_l = letters(" ".join(html.unescape(Path(f).read_text()) for f in glob.glob(str(build / "*.html"))))

    raw = pdf_text()
    if args.dump_pdf_text:
        Path(args.dump_pdf_text).write_text(raw)
    raw = raw.replace("\f", "\n")  # pdftotext puts no newline before a page break
    raw = re.sub(r"(?m)^\d+\s+Chapter\s+\d+\..*$", " ", raw)
    raw = re.sub(r"(?m)^\d+(?:\.\d+)+\.?\s[^\n]{3,90}?\s\d{1,3}$", " ", raw)
    raw = re.sub(r"-\n", "", raw)
    pdf_l = letters(raw)

    # 1a. site -> PDF
    miss = scan(site_words, pdf_l)
    bad = [r for r in runs(miss) if not in_order_anywhere([site_words[k] for k in r], pdf_l)]
    out(f"prose site->PDF: {len(site_words)} words, {len(miss)} not aligned locally, "
          f"{len(bad)} runs not found in order anywhere in the PDF")
    for r in bad[:20]:
        out("    " + " ".join(site_words[k] for k in r))
    failures += len(bad)

    # 1b. PDF -> site (body only; TeX prose words; bibliography is on its own page)
    dictionary = tex_vocabulary()
    out(f"PDF text via {'pdftotext' if shutil.which('pdftotext') else 'PDFKit'}: {len(raw)} chars; "
        f"TeX prose vocabulary: {len(dictionary)} words")
    tokens = re.findall(r"[A-Za-z]{7,}", unicodedata.normalize("NFKC", raw))
    pdf_words = [w.lower() for w in tokens
                 if any(w.lower()[:len(w) - k] in dictionary for k in (0, 1, 2, 3))]
    ref_at = next((n for n, w in enumerate(pdf_words) if w == "references" and n > len(pdf_words) * 0.8),
                  len(pdf_words))
    miss2 = [k for k in scan(pdf_words, site_l) if 300 <= k < ref_at]
    bad2 = [r for r in runs(miss2) if len(r) >= 2 and not in_order_anywhere([pdf_words[k] for k in r], everything_l)]
    out(f"prose PDF->site: {ref_at - 300} body words, {len(miss2)} not aligned locally, "
          f"{len(bad2)} multi-word runs not found in order anywhere on the site")
    for r in bad2[:20]:
        out("    " + " ".join(pdf_words[k] for k in r))
    failures += len(bad2)

    # 2. formulas
    stream = site_math(build)
    formulas = tex_formulas()
    missing = [(f, m) for f, m in formulas if norm_math(m) and norm_math(m) not in stream]
    out(f"formulas: {len(formulas)} in the TeX, {len(missing)} not found verbatim on the site")
    for f, m in missing[:20]:
        out(f"    {f}: {m.strip()[:120]!r}")
    failures += len(missing)

    out("FIDELITY OK" if not failures else f"FIDELITY PROBLEMS: {failures}")
    annotate(failures)
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
