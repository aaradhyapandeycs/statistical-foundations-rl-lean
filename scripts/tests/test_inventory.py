"""Adversarial lexical fixtures; these do not certify mathematical coverage."""
import importlib.util
from pathlib import Path
import tempfile
import unittest


SPEC = importlib.util.spec_from_file_location("source_inventory", Path(__file__).resolve().parents[1] / "inventory.py")
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


CLASS = r"""\LoadClass{book}
\newtheorem{theorem}{Theorem}[chapter]
\newtheorem{lemma}[theorem]{Lemma}
\newtheorem{definition}{Definition}[chapter]
\newtheorem{remark}{Remark}[chapter]
"""


class InventoryTests(unittest.TestCase):
    def scan(self, body, files=None, preamble=""):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        project = Path(temporary.name)
        root = project / MODULE.SOURCE
        root.mkdir(parents=True)
        (root / "local.cls").write_text(CLASS)
        (root / "main.tex").write_text("\\documentclass{local}\n" + preamble + "\n\\begin{document}\n" + body + "\n\\end{document}\n")
        for name, text in (files or {}).items():
            path = root / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(text)
        return MODULE.Inventory(project, main="main.tex").run()

    def test_comments_macro_definitions_and_include_order(self):
        data = self.scan(r"""% \input{missing}
\chapter{Start}
\input{chapters/one}
\begin{comment}
\begin{theorem}\label{bad}False\end{theorem}
\input{missing}
\end{comment}
\input{chapters/two.tex}
""", {
            "chapters/one.tex": r"\begin{lemma}\label{first}A\end{lemma}\input{chapters/nested}",
            "chapters/nested.tex": r"\begin{theorem}\label{second}B\end{theorem}",
            "chapters/two.tex": r"\begin{definition}\label{third}C\end{definition}",
        }, preamble=r"\newcommand{\fake}[1]{\begin{theorem}\label{phantom}#1\end{theorem}}")
        self.assertEqual([e["requested"] for e in data["include_order"]], ["chapters/one", "chapters/nested", "chapters/two.tex"])
        self.assertEqual([e["label"] for e in data["labels"]], ["first", "second", "third"])
        self.assertFalse(data["warnings"])
        self.assertEqual(data["counts"]["by_kind"]["lemma"], 1)

    def test_shared_counters_independent_counters_and_resets(self):
        data = self.scan(r"""\chapter{First}
\begin{lemma}A\end{lemma}
\begin{definition}B\end{definition}
\begin{theorem}C\end{theorem}
\chapter{Second}
\begin{lemma}D\end{lemma}
""")
        results = [(e["kind"], e.get("number")) for e in data["entries"] if e["kind"] in {"theorem", "lemma", "definition"}]
        self.assertEqual(results, [("lemma", "1.1"), ("definition", "1.1"), ("theorem", "1.2"), ("lemma", "2.1")])

    def test_display_rows_nested_cases_wrappers_and_subequations(self):
        data = self.scan(r"""\chapter{First}
\begin{subequations}\label{group}
\begin{align}
x &= 1\label{a}\\
y &= 2\notag\\
z &= \begin{cases}1 & a \\ 2 & b\end{cases}\label{b}
\end{align}
\end{subequations}
\begin{align}
w &= 3 \arxiv{\notag\\ ignored}\label{c}\\
v &= 4\book{\label{d}}
\end{align}
\begin{equation*}q=5\end{equation*}
$$ x=1 $$
\[y=2\]
""", preamble=r"\newcommand{\arxiv}[1]{}\newcommand{\book}[1]{#1}")
        displays = [e for e in data["entries"] if e["kind"] == "display"]
        self.assertEqual([r["number"] for r in displays[0]["rows"]], ["1.1a", None, "1.1b"])
        self.assertEqual([r["number"] for r in displays[1]["rows"]], ["1.2", "1.3"])
        self.assertEqual(data["counts"]["numbered_display_rows"], 4)
        self.assertEqual(len(displays), 5)
        self.assertFalse(data["warnings"])

    def test_links_in_heading_and_proof_title_are_not_lost(self):
        data = self.scan(r"""\chapter{First}\label{chapter:first}
\begin{theorem}\label{target}A\end{theorem}
\section{Proof of Theorem~\ref{target} (see \citep{source})}
\begin{proof}[Proof of \Cref{target}]
\begin{equation}\label{equation}x=1\end{equation}
\end{proof}
""")
        self.assertEqual(data["counts"]["cross_references"], 2)
        self.assertEqual(data["counts"]["citations"], 1)
        self.assertFalse(data["warnings"])
        proof = next(e for e in data["entries"] if e["kind"] == "proof")
        self.assertEqual(proof["adjacent_result_candidate"], "label:target")
        self.assertTrue(all(e["status"] == "unformalized" and e["review_status"] == "unreviewed" for e in data["entries"]))

    def test_source_locators_survive_comment_masking_and_includes(self):
        data = self.scan(r"\chapter{First}\input{child}", {"child.tex": "% discarded\n\n\\begin{lemma}\nA\n\\end{lemma}\n"})
        lemma = next(e for e in data["entries"] if e["kind"] == "lemma")
        self.assertEqual(lemma["source_ranges"], [{"file": "source/upstream/tex/child.tex", "line_start": 3, "line_end": 5}])

    def test_warning_evidence_for_unknown_controls_and_bad_references(self):
        data = self.scan(r"""\chapter{First}
\iftrue A\fi
\label{twice}\label{twice}\ref{missing}
""")
        codes = [w["code"] for w in data["warnings"]]
        self.assertIn("unsupported_tex_control", codes)
        self.assertIn("duplicate_label", codes)
        self.assertIn("unresolved_cross_reference", codes)

    def test_uncomment_escaped_percent_and_even_backslashes(self):
        text = "a \\% literal % removed\nb \\\\% removed\nc"
        masked = MODULE.uncomment(text)
        self.assertIn(r"\% literal", masked)
        self.assertNotIn("removed", masked)
        self.assertEqual(text.count("\n"), masked.count("\n"))

    def test_include_cycle_is_an_error(self):
        with self.assertRaisesRegex(ValueError, "recursive include"):
            self.scan(r"\input{loop}", {"loop.tex": r"\input{loop}"})


if __name__ == "__main__":
    unittest.main()
