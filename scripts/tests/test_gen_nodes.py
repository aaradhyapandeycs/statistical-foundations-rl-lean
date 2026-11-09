"""Fixture tests for scripts/gen_nodes.py (no live-tree data)."""

import json
import os
import shutil
import sys
import tempfile
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))
sys.path.insert(0, str(HERE.parents[1] / "site"))
import gen_nodes as gn  # noqa: E402

TEX = "source/upstream/tex/chapters/prelim.tex"


def entry(id_, kind, number, a, b, labels=(), **extra):
    e = {"id": id_, "kind": kind, "chapter": "2", "number": number, "labels": list(labels),
         "source_ranges": [{"file": TEX, "line_start": a, "line_end": b}]}
    e.update(extra)
    return e


def inventory():
    entries = [
        entry("label:lem:a", "lemma", "2.1", 10, 20, ["lem:a"]),
        entry("ch2-proof-a", "proof", None, 21, 30, adjacent_result_candidate="label:lem:a"),
        entry("label:lem:b", "lemma", "2.2", 40, 50, ["lem:b"]),
        entry("label:thm:c", "theorem", "2.3", 60, 70, ["thm:c"]),
        entry("ch2-proof-c", "proof", None, 71, 90, title_tex="Proof of Theorem~\\ref{thm:c}"),
        entry("label:lem:d", "lemma", "2.4", 100, 110, ["lem:d"]),
        entry("ch2-remark-2.1", "remark", "2.1", 120, 125),
        entry("label:alg:x", "algorithm", "2.1", 130, 140, ["alg:x"]),
        entry("label:eq:p", "display", "2.5", 150, 152, ["eq:p"]),
        entry("label:eq:q", "display", "2.6", 154, 156, ["eq:q"]),
    ]
    refs = [
        {"kind": "cross_reference", "targets": ["lem:b"], "source": {"file": TEX, "line_start": 25, "line_end": 25}},
        {"kind": "cross_reference", "targets": ["lem:a", "alg:x"],
         "source": {"file": TEX, "line_start": 80, "line_end": 80}},
        {"kind": "cross_reference", "targets": ["lem:d"], "source": {"file": TEX, "line_start": 85, "line_end": 85}},
        {"kind": "citation", "targets": ["x"], "source": {"file": TEX, "line_start": 85, "line_end": 85}},
    ]
    labels = [{"label": l, "source": {"file": TEX, "line_start": e["source_ranges"][0]["line_start"],
                                      "line_end": e["source_ranges"][0]["line_start"]}, "owner_id": e["id"]}
              for e in entries for l in e["labels"]]
    return {"source": {"arxiv_id": "test", "main_sha256": "0"},
            "counts": {"by_kind": {"theorem": 1, "lemma": 3, "claim": 0, "algorithm": 1, "definition": 0,
                                   "assumption": 0, "source_gap_candidate": 0}},
            "entries": entries, "labels": labels, "references": refs}


LEDGER = {"certified_named_results": [
    {"name": "Lemma 2.1", "source_label": "lem:a", "lean_statement": "StatisticalRL.Statements.Lemma2_1",
     "lean_export": "StatisticalRL.Foo.lemma_a", "statement_scope": "", "evidence": "docs/critic-a.md"},
    {"name": "Lemma 2.2", "source_label": "lem:b", "lean_statement": "StatisticalRL.Statements.Lemma2_2",
     "lean_export": "StatisticalRL.Foo.lemma_b", "statement_scope": "", "evidence": "docs/critic-b.md"}],
    "proved_variants": [
    {"name": "Theorem 2.3 (corrected)", "source_label": "thm:c", "lean_statement": "StatisticalRL.Statements.Thm2_3_corrected",
     "lean_export": "StatisticalRL.Foo.thm_c", "statement_scope": "See C7.", "evidence": "docs/critic-c.md"}]}

CH2 = '''namespace StatisticalRL.Statements

/-- `lem:a`, `chapters/prelim.tex:10–20`. -/
def Lemma2_1 : Prop := True

/-- `lem:b`, `chapters/prelim.tex:40–50`. -/
def Lemma2_2 : Prop := True

/-- `thm:c`, `chapters/prelim.tex:60–70`. Corrected, C7. -/
def Thm2_3_corrected : Prop := True

/-- Remark 2.1, `chapters/prelim.tex:120–125`. -/
def Remark2_1 : Prop := True

/-- Joint display claim, `eq:p` and `eq:q`, `chapters/prelim.tex:150–156`. -/
def Eq_p_q : Prop := True

end StatisticalRL.Statements
'''

CH2_PROOFS = '''namespace StatisticalRL.Statements

theorem Lemma2_1_holds : Lemma2_1 := StatisticalRL.Foo.lemma_a

theorem Lemma2_2_holds : Lemma2_2 := StatisticalRL.Foo.lemma_b

theorem Thm2_3_corrected_holds : Thm2_3_corrected := StatisticalRL.Foo.thm_c

theorem Remark2_1_holds : Remark2_1 := StatisticalRL.Foo.remark

theorem Eq_p_q_holds : Eq_p_q := StatisticalRL.Foo.pq

end StatisticalRL.Statements
'''

COVERAGE = '''| Source item | Lean evidence | Reviewed scope |
| --- | --- | --- |
| Remark 2.1, prelim lines 120–125 | x | **Proved** (`Remark2_1`). |
| Lemma 2.4, `lem:d` | x | **Printed statement refuted; corrected open.** `not_lemma2_4_printed` |
| Theorem 2.3, `thm:c` | x | **Corrected variant proved.** Printed form false: `not_thm2_3_printed`. |
| Displays `eq:p` and `eq:q` | x | **Proved** (`Eq_p_q`). |
'''


class GenNodesTest(unittest.TestCase):
    def setUp(self):
        self.tmp = Path(tempfile.mkdtemp())
        files = {"docs/source-inventory.json": json.dumps(inventory()),
                 "docs/named-result-status.json": json.dumps(LEDGER),
                 "docs/COVERAGE.md": COVERAGE,
                 "docs/SOURCE-ISSUES.md": "## Candidate C7: something\n",
                 "Formalization/Statements/Ch2.lean": CH2,
                 "Formalization/Statements/Ch2Proofs.lean": CH2_PROOFS}
        for p, t in files.items():
            (self.tmp / p).parent.mkdir(parents=True, exist_ok=True)
            (self.tmp / p).write_text(t)

    def tearDown(self):
        shutil.rmtree(self.tmp)

    def test_regexes_match_reader(self):
        from reader import lean
        for name in ("RANGE_RE", "LABEL_RE", "DECL_RE"):
            self.assertEqual(getattr(gn, name).pattern, getattr(lean, name).pattern, name)

    def test_statuses_edges_and_closure(self):
        data = gn.build(gn.Reader(self.tmp))
        n = {x["id"]: x for x in data["nodes"]}
        self.assertEqual(n["label:lem:a"]["statement_status"], "printed")
        self.assertEqual(n["label:thm:c"]["statement_status"], "corrected")
        self.assertEqual(n["label:thm:c"]["issues"], ["C7"])
        self.assertEqual(n["label:lem:d"]["statement_status"], "refuted")
        self.assertEqual(n["label:lem:d"]["proof_status"], "refuted")
        self.assertEqual(n["ch2-remark-2.1"]["statement_status"], "printed")
        self.assertEqual(n["ch2-remark-2.1"]["proof_status"], "proved")
        # lem:a's proof cites lem:b; thm:c's proof region cites lem:a, alg:x (context) and lem:d
        self.assertEqual([u["id"] for u in n["label:lem:a"]["uses"]], ["label:lem:b"])
        uses_c = {u["id"]: u for u in n["label:thm:c"]["uses"]}
        self.assertEqual(set(uses_c), {"label:lem:a", "label:alg:x", "label:lem:d"})
        self.assertEqual(uses_c["label:alg:x"]["target"], "context")
        self.assertTrue(all(not u["reviewed"] for u in uses_c.values()))
        self.assertTrue(n["label:lem:a"]["printed_with_cited_printed"])
        self.assertFalse(n["label:thm:c"]["printed_with_cited_printed"])
        self.assertEqual(data["summary"]["named_results_with_ledger_record"], 3)
        self.assertEqual(n["label:lem:a"]["proof_wrappers"], ["StatisticalRL.Statements.Lemma2_1_holds"])
        # R1: a proved node citing a refutation stays proved; the name is recorded as data only
        self.assertEqual(n["label:thm:c"]["proof_status"], "proved")
        self.assertEqual(n["label:thm:c"]["refutations_cited"], ["not_thm2_3_printed"])
        self.assertNotIn("printed_refuted", n["label:thm:c"])

    def test_joint_entry_attaches_to_every_cited_display(self):
        n = {x["id"]: x for x in gn.build(gn.Reader(self.tmp))["nodes"]}
        for nid in ("label:eq:p", "label:eq:q"):
            self.assertEqual([e["name"] for e in n[nid]["statement_entries"]], ["StatisticalRL.Statements.Eq_p_q"])
            self.assertEqual((n[nid]["statement_status"], n[nid]["proof_status"]), ("printed", "proved"))

    def test_refuted_needs_a_cited_refutation(self):
        cov = COVERAGE.replace(" `not_lemma2_4_printed`", "")
        (self.tmp / "docs/COVERAGE.md").write_text(cov)
        n = {x["id"]: x for x in gn.build(gn.Reader(self.tmp))["nodes"]}
        self.assertEqual(n["label:lem:d"]["statement_status"], "open")

    def test_partial_headline_overrides_proved(self):
        cov = COVERAGE.replace("**Proved** (`Remark2_1`).", "**Partial:** only one clause (`Remark2_1`).")
        (self.tmp / "docs/COVERAGE.md").write_text(cov)
        data = gn.build(gn.Reader(self.tmp))
        n = {x["id"]: x for x in data["nodes"]}
        self.assertEqual((n["ch2-remark-2.1"]["statement_status"], n["ch2-remark-2.1"]["proof_status"]),
                         ("partial", "open"))
        self.assertTrue(any("headline wins" in w for w in data["warnings"]))

    def test_classify_agrees_with_reader(self):
        from reader import lean
        names = ["Lemma2_1", "Thm3_2_positiveN", "Lemma2_1_iterationCount", "Thm3_9_causal_positiveN", "Lemma5_7_K2_corrected",
                 "Thm7_6_restricted", "Lemma6_4", "Thm7_12_corrected_local", "Thm4_7"]
        to_reader = {"printed": "original", "corrected": "corrected", "restricted": "restricted"}
        for kind in ("certified_named_results", "proved_variants"):
            for name in names:
                for scope in ("", "Restricted to N>0."):
                    self.assertEqual(to_reader[gn.classify(name, kind, scope)], lean.classify(name, kind, scope),
                                     (name, kind, scope))

    def test_unsuffixed_prose_entry_status_comes_from_coverage(self):
        # An unrecorded entry with a non-restriction suffix is classified by the coverage row
        # that names it, not by its name: proved -> printed; partial-sentence headline -> restricted.
        rows = gn.parse_coverage('''| Source item | Lean evidence | Reviewed scope |
| --- | --- | --- |
| Iteration count after Lemma 2.1 | x | **Prose claim proved** (`Lemma2_1_iterationCount`): every k ... |
| Constant rate after Theorem 4.6 | x | **Prose claim proved with the Õ made explicit** (`Thm4_6_constantRate`): ... |
| Remarks | x | **Proved** (`Remark4_1`, `Remark4_2`): ... |
| Remark 4.5 | x | **First two sentences proved** (`Remark4_5`), ... |
| Theorem 4.7 | x | **Printed result proved** (`Thm4_7`) ... `Thm4_7_case_i` is a reading aid. |
| Remark 5.12 | x | **Restricted variant proved (lower bound unrestricted).** `Remark5_12_lowerBound`: ... |
| Theorem 7.11 | x | **Printed statement refuted; corrected theorem open.** (`Thm7_11_x`) |
''')
        self.assertEqual(gn.classify("Lemma2_1_iterationCount", None, "", rows), "printed")
        self.assertEqual(gn.classify("Thm4_6_constantRate", None, "", rows), "printed")
        self.assertEqual(gn.classify("Remark4_2", None, "", rows), "printed")
        # proving only part of a remark is partial, not a restricted case
        self.assertIsNone(gn.coverage_variant("Remark4_5", rows))
        self.assertTrue(gn.coverage_partial("Remark4_5", rows))
        self.assertFalse(gn.coverage_partial("Remark4_1", rows))
        self.assertEqual(gn.classify("Remark5_12_lowerBound", None, "", rows), "restricted")
        # not the row's subject: falls back to the name rule (suffix -> restricted)
        self.assertIsNone(gn.coverage_variant("Thm4_7_case_i", rows))
        self.assertEqual(gn.classify("Thm4_7_case_i", None, "", rows), "restricted")
        # refuted with nothing proved: no proved variant
        self.assertIsNone(gn.coverage_variant("Thm7_11_x", rows))
        # name markers still win over a "proved" coverage headline
        rows2 = gn.parse_coverage("| a | b | **Prose claim proved** (`Thm3_2_approxPlanner_positiveN`) |\n")
        self.assertEqual(gn.classify("Thm3_2_approxPlanner_positiveN", None, "", rows2), "restricted")
        # and the named-ledger record wins over coverage
        self.assertEqual(gn.classify("Lemma2_1_iterationCount", "proved_variants", "", rows), "restricted")

    def test_unsuffixed_prose_entry_in_graph(self):
        ch2 = CH2.replace("def Remark2_1 : Prop := True", "def Remark2_1_iterationCount : Prop := True")
        (self.tmp / "Formalization/Statements/Ch2.lean").write_text(ch2)
        (self.tmp / "docs/COVERAGE.md").write_text(COVERAGE.replace("**Proved** (`Remark2_1`)",
                                                                    "**Prose claim proved** (`Remark2_1_iterationCount`)"))
        n = {x["id"]: x for x in gn.build(gn.Reader(self.tmp))["nodes"]}
        self.assertEqual(n["ch2-remark-2.1"]["statement_status"], "printed")
        self.assertEqual(n["ch2-remark-2.1"]["statement_entries"][0]["variant"], "printed")

    def test_issue_ids_ignore_constants(self):
        # COVERAGE row for Theorems 7.2/7.4 uses constants "C1 log(...) (C1 = 2, C2 = 10⁶)"
        cov = COVERAGE.replace("**Corrected variant proved.** Printed form false: `not_thm2_3_printed`.",
                               "**Corrected variant proved.** iterations at least C1 log(N) (C1 = 2, C2 = 10), "
                               "see [C7](SOURCE-ISSUES.md#C7). Printed form false: `not_thm2_3_printed`.")
        (self.tmp / "docs/COVERAGE.md").write_text(cov)
        (self.tmp / "docs/SOURCE-ISSUES.md").write_text("## Candidate C1: a\n## Candidate C2: b\n## Candidate C7: c\n")
        n = {x["id"]: x for x in gn.build(gn.Reader(self.tmp))["nodes"]}
        self.assertEqual(n["label:thm:c"]["issues"], ["C7"])
        self.assertEqual(gn.CID_RE.findall("C1 = 2, C2 ≤ 3, see C37"), ["37"])

    def test_escaped_pipe_stays_in_cell(self):
        cells = gn.split_md_row("| a | b | **Refuted.** \\|E f(x) − E f(Z)\\| ≤ 1, `|x|` |")
        self.assertEqual(len(cells), 3)
        self.assertEqual(cells[2], "**Refuted.** |E f(x) − E f(Z)| ≤ 1, `|x|`")
        from reader import lean
        self.assertEqual(lean.split_md_row("| a | b | c \\| d |"), gn.split_md_row("| a | b | c \\| d |"))

    def test_reader_places_cards_at_their_own_item(self):
        """B1: an entry is shown at the source item it formalizes, not the first item it cites;
        the cited algorithm gets a link and no status."""
        from reader import render
        from reader.lean import Entry
        from types import SimpleNamespace as NS

        def blk(kind, kind_name, entry_id, labels, number):
            b = NS(kind=kind, kind_name=kind_name, entry={"id": entry_id, "labels": labels}, labels=labels,
                   children=[], anchor="E-" + entry_id, file=None, line_start=None, number=number)
            return b
        alg = blk("algorithm", None, "label:alg:q", ["alg:q"], "4.2")
        alg.kind_name = None
        thm = blk("env", "theorem", "label:thm:lb", ["thm:lb"], "4.7")
        page = NS(id="ch4-3", blocks=[alg, thm])
        e = Entry("Thm4_7", "S.Thm4_7", "F/Ch4.lean", 1, 2, "", ["alg:q", "thm:lb"], [],
                  record={"source_label": "thm:lb"}, status="original")
        site = object.__new__(render.Site)
        site.book = NS(label_owner={"alg:q": {}, "thm:lb": {}})
        site.lean = NS(entries=[e], coverage={})
        site.pages = [page]
        site.entry_node = {"S.Thm4_7": "label:thm:lb"}
        site.inv_by_id = {"label:thm:lb": {"labels": ["thm:lb"], "kind": "theorem", "number": "4.7"}}
        site.place()
        self.assertEqual(site.placed["Thm4_7"][1], "E-label:thm:lb")
        self.assertEqual(site.placement_problems(), [])
        self.assertEqual(site.statuses(thm), ["original"])
        self.assertEqual(site.statuses(alg), [])
        self.assertIn(e, site.matches[id(alg)])
        self.assertNotIn(id(alg), site.home)

    def test_check_mode_and_next(self):
        self.assertEqual(gn.main(["--root", str(self.tmp)]), 0)
        self.assertEqual(gn.main(["--root", str(self.tmp), "--check"]), 0)
        nxt = (self.tmp / gn.NEXT_PATH).read_text()
        self.assertIn("INCOMPLETE", nxt)
        self.assertIn("Lemma 2.4 `lem:d`", nxt)
        (self.tmp / "docs/COVERAGE.md").write_text(COVERAGE.replace("refuted", "noted"))
        self.assertEqual(gn.main(["--root", str(self.tmp), "--check"]), 1)

    def test_inventory_count_mismatch_fails(self):
        inv = inventory()
        inv["counts"]["by_kind"]["lemma"] = 4
        (self.tmp / "docs/source-inventory.json").write_text(json.dumps(inv))
        with self.assertRaises(SystemExit):
            gn.build(gn.Reader(self.tmp))

    def test_ledger_record_without_inventory_entry_fails(self):
        ledger = json.loads(json.dumps(LEDGER))
        ledger["proved_variants"][0]["source_label"] = "thm:missing"
        (self.tmp / "docs/named-result-status.json").write_text(json.dumps(ledger))
        with self.assertRaises(SystemExit):
            gn.build(gn.Reader(self.tmp))



ROOT = HERE.parents[1]


@unittest.skipUnless((ROOT / "source/upstream/tex/StatisticalRL-nowplain.tex").is_file(),
                     "pinned TeX not restored (python3 scripts/fetch_source.py)")
class ReaderPlacementTest(unittest.TestCase):
    """Regression test on the real book and the committed ledgers (Lean revision HEAD): each Lean
    card sits at the result it formalizes, never at an algorithm or definition it cites."""

    @classmethod
    def setUpClass(cls):
        from reader.book import Book
        from reader.lean import Git, LeanIndex
        from reader.render import Site
        cls.tmp = Path(tempfile.mkdtemp())
        book = Book(ROOT, cls.tmp)
        lean = LeanIndex(Git(ROOT, os.environ.get("SITE_TEST_REV", "HEAD")),
                         {l["label"] for l in book.inventory["labels"]})
        front, chapters, back = book.convert_all()
        cls.site = Site(book, lean, book.paginate(chapters), front, back)
        cls.blocks = {id(b): (p, b) for p in cls.site.pages for t in p.blocks for b in cls.site.units(t)}

    @classmethod
    def tearDownClass(cls):
        shutil.rmtree(cls.tmp)

    def home(self, name):
        _, _, _, bid = self.site.placed[name]
        return self.blocks[bid][1]

    def test_no_unplaced_cards_and_ledger_items_hold_their_cards(self):
        self.assertEqual([e.name for e in self.site.unplaced], [])
        self.assertEqual(self.site.placement_problems(), [])

    def test_concrete_placements(self):
        b = self.home("Thm4_7")
        self.assertIn("thm:LB-example-Q-generative", b.labels)       # Theorem 4.7, not Algorithm 4.2
        self.assertNotEqual(self.site.kind_of(b), "algorithm")
        b = self.home("Thm7_6_restricted")
        self.assertIn("thm:sample-complexity-plug-in-marl", b.labels)  # Theorem 7.6, not eq:defn-Nash-E / CCE
        for name in ("Eq_PAC_from_regret_conversion_corrected", "Eq_PAC_from_regret_conversion_restricted"):
            if name in {e.name for e in self.site.lean.entries}:
                self.assertIn('id="L-eq:PAC-from-regret-conversion"', self.home(name).html)

    def test_theorem_7_2_issues(self):
        n = {x["id"]: x for x in self.site.node_data["nodes"]}
        self.assertEqual(n["label:thm:l1-upper-bound"]["issues"], ["C37"])

    def test_context_items_carry_no_status(self):
        for _, b in self.blocks.values():
            if self.site.kind_of(b) in ("algorithm", "assumption", "definition"):
                self.assertEqual(self.site.statuses(b), [], b.labels)
                self.assertNotIn(id(b), self.site.home, b.labels)


if __name__ == "__main__":
    unittest.main()
