"""Tests for site/check_macros.py, the reader's raw/undefined TeX macro check.

Fixture pages exercise each rule; a source-level test checks that every macro
used in a formula of the pinned book TeX is defined for MathJax (by the book's
own definitions, as the site loads them, or by MathJax itself). The built-site
check runs in site/check_fidelity.py.
"""

import json
import os
import sys
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "site"))
import check_macros as cm  # noqa: E402

CFG = {"tex": {"macros": {"cC": "{\\mathcal{C}}", "sA": "\\mathscr{A}", "norm": ["\\left\\|{#1}\\right\\|", 1]}}}


def page(body: str, cfg=CFG) -> str:
    script = f"<script>window.MathJax = {json.dumps(cfg)};\n</script>" if cfg is not None else ""
    return (f"<!doctype html><html><head><title>\\sA page</title>{script}"
            f'<script defer src="https://cdn.jsdelivr.net/npm/mathjax@3.2.2/es5/tex-chtml-full.js"></script></head>'
            f'<body class="tex2jax_ignore"><main>{body}</main></body></html>')


class Fixtures(unittest.TestCase):
    def run_check(self, pages: dict, cfg=CFG) -> list:
        with tempfile.TemporaryDirectory() as d:
            build = Path(d)
            (build / "assets").mkdir()
            (build / "assets/mathjax-config.js").write_text("window.MathJax = " + json.dumps(CFG) + ";\n")
            for name, text in pages.items():
                (build / name).write_text(text)
            return cm.check(build)

    def test_clean_page(self):
        body = ('<p>Algorithm <span class="tex2jax_process">\\(\\sA\\)</span> uses '
                '<span class="tex2jax_process">\\(\\cC = \\{t_r\\}_{r=1}^R\\)</span>.</p>'
                '<div class="md tex2jax_process">\\begin{align*}\\norm{x} \\le 1\\end{align*}</div>'
                '<details class="tex-src"><summary>TeX source</summary><pre>\\fedsyncq \\sA</pre></details>'
                '<pre><code>theorem foo : \\forall x</code></pre>')
        self.assertEqual(self.run_check({"a.html": page(body)}), [])

    def test_raw_macro_in_ignored_text(self):
        # math delimiters outside any tex2jax_process element are never typeset
        probs = self.run_check({"a.html": page("<td>A generic algorithm \\(\\sA\\)</td>")})
        self.assertIn(("a.html", "raw macro outside math", "\\sA"), probs)

    def test_raw_macro_in_processed_text_outside_delimiters(self):
        probs = self.run_check({"a.html": page('<ol class="tex2jax_process"><li>run \\fedsyncq on \\(x\\)</li></ol>')})
        self.assertEqual([p[2] for p in probs], ["\\fedsyncq"])

    def test_undefined_math_macro(self):
        probs = self.run_check({"a.html": page('<span class="tex2jax_process">\\(\\cD \\subseteq \\cC\\)</span>')})
        self.assertEqual(probs, [("a.html", "undefined in math", "\\cD")])

    def test_undefined_environment(self):
        probs = self.run_check({"a.html": page('<div class="md tex2jax_process">\\begin{foo}x\\end{foo}</div>')})
        self.assertEqual(probs, [("a.html", "undefined in math", "{foo}")])

    def test_page_without_configuration(self):
        probs = self.run_check({"a.html": page('<span class="tex2jax_process">\\(x\\)</span>', cfg=None)})
        self.assertEqual(probs, [("a.html", "no MathJax configuration", "page loads no macro definitions")])

    def test_stale_inline_configuration(self):
        stale = {"tex": {"macros": {"cC": "{\\mathcal{C}}"}}}
        probs = self.run_check({"a.html": page('<span class="tex2jax_process">\\(\\cC\\)</span>', cfg=stale)})
        self.assertEqual([p[1] for p in probs], ["stale MathJax configuration"])

    def test_external_configuration_accepted(self):
        text = page('<span class="tex2jax_process">\\(\\cC\\)</span>', cfg=None).replace(
            "</title>", '</title><script src="assets/mathjax-config.js"></script>')
        self.assertEqual(self.run_check({"a.html": text}), [])

    def test_escaped_closing_tag_in_inline_configuration(self):
        cfg = {"tex": {"macros": dict(CFG["tex"]["macros"])}}
        text = page('<span class="tex2jax_process">\\(\\cC\\)</span>').replace(
            "<script>window.MathJax = " + json.dumps(cfg), "<script>window.MathJax = " + json.dumps(cfg).replace("</", "<\\/"))
        self.assertEqual(self.run_check({"a.html": text}), [])

    def test_undefined_in_configured_body(self):
        with tempfile.TemporaryDirectory() as d:
            build = Path(d)
            (build / "assets").mkdir()
            bad = {"tex": {"macros": {"cite": "\\nowfnt@authorlist"}}}
            (build / "assets/mathjax-config.js").write_text("window.MathJax = " + json.dumps(bad) + ";")
            probs = cm.check(build)
        self.assertEqual(probs, [("mathjax-config.js", "macro body", "\\cite uses undefined \\nowfnt")])


@unittest.skipUnless((ROOT / "source/upstream/tex/chapters/commands.tex").is_file(),
                     "pinned TeX not restored (python3 scripts/fetch_source.py)")
class BookSource(unittest.TestCase):
    def test_every_formula_macro_is_defined(self):
        import check_fidelity as cf
        from reader.book import MATH_OVERRIDES
        from reader.tex import parse_macros
        tex = ROOT / "source/upstream/tex"
        texts = [(tex / "chapters/commands.tex").read_text(),
                 (tex / "StatisticalRL-nowplain.tex").read_text().split("\\begin{document}")[0]]
        texts += [f.read_text() for f in sorted((tex / "chapters").glob("*.tex")) if f.name != "commands.tex"]
        macros = {}
        for t in texts:
            macros.update(parse_macros(t))
        macros.update(MATH_OVERRIDES)
        builtin, envs = cm.builtins()
        defined = builtin | set(macros)
        missing = sorted({(f, n) for f, m in cf.tex_formulas() for n in cm.undefined(m, defined, envs)})
        self.assertEqual(missing, [])


if __name__ == "__main__":
    unittest.main()
