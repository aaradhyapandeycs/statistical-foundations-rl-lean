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

    def test_declared_restricted_variant_wins(self):
        from reader import lean
        # an entry named `_corrected` that the ledger declares restricted counts as restricted
        self.assertEqual(gn.classify("Thm7_11_corrected_halfspace", "proved_variants", "Corrected and restricted",
                                     declared="restricted"), "restricted")
        self.assertEqual(lean.classify("Thm7_11_corrected_halfspace", "proved_variants", "", "restricted"),
                         "restricted")
        self.assertEqual(gn.classify("Thm7_11_corrected_halfspace", "proved_variants", ""), "corrected")
        # the field may only downgrade; it can never declare the printed statement
        for bad in ("printed", "corrected"):
            with self.assertRaises(SystemExit):
                gn.classify("Lemma2_1", "certified_named_results", "", declared=bad)

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


    def test_card_for_display_inside_algorithm_follows_the_algorithm(self):
        """A display inside an algorithm (e.g. eq:online_RBMLE in the VPO algorithm): its card is not
        shown beside the algorithm but in a row of its own right after it, so the algorithm keeps no
        status and the book text stays contiguous; the algorithm row links to the card."""
        from reader import render
        from reader.lean import Entry
        from types import SimpleNamespace as NS
        alg = NS(kind="algorithm", kind_name=None, entry={"id": "label:alg:vpo", "labels": ["alg:vpo"]},
                 labels=["alg:vpo"], children=[], anchor="E-label:alg:vpo", file=None, line_start=None,
                 number="7.4", in_proof=False, tex="", title="",
                 html='<div id="E-label:alg:vpo">Obtain the preference <span id="L-eq:upd"></span></div>')
        para = NS(kind="para", kind_name=None, entry=None, labels=[], children=[], anchor=None, file=None,
                  line_start=None, number=None, in_proof=False, tex="", title="", html="<p>The next theorem</p>")
        page = NS(id="ch7-5", blocks=[alg, para])
        e = Entry("Eq_upd_restricted", "S.Eq_upd_restricted", "F/Ch7.lean", 1, 2, "", ["eq:upd"], [],
                  status="cov-restricted")
        site = object.__new__(render.Site)
        site.book = NS(label_owner={"eq:upd": {}})
        site.lean = NS(entries=[e], coverage={}, card=lambda e: f'<article id="lean-{e.name}">CARD</article>')
        site.pages = [page]
        site.entry_node = {"S.Eq_upd_restricted": "label:eq:upd"}
        site.inv_by_id = {"label:eq:upd": {"labels": ["eq:upd"], "kind": "display", "number": "7.62"}}
        site.nodes = {}
        site.place()
        self.assertEqual(site.unplaced, [])
        self.assertEqual(site.statuses(alg), [])
        body = site.page_body(page)
        a, c, t = body.find("Obtain the preference"), body.find("CARD"), body.find("The next theorem")
        self.assertTrue(0 <= a < c < t, body)
        self.assertIn('row paired lean-after', body)
        self.assertIn('href="#lean-Eq_upd_restricted"', body[:c])
        self.assertNotIn("CARD", body[:body.find('row paired lean-after')])

    def test_fidelity_fallback_stream_ignores_lean_cards(self):
        import check_fidelity
        page = ('<div class="row"><div class="book-col">outcome</div><aside class="lean-col">theorem foo '
                '</aside></div><p>theorem assumption</p>')
        text = check_fidelity.without_lean(page)
        self.assertNotIn("foo", text)
        run = ["outcome", "theorem", "assumption"]
        self.assertTrue(check_fidelity.in_order_anywhere(run, check_fidelity.letters(text)))

    # -- batch T: closing statuses, wrapper bodies, remark attachment ---------------------------

    def write_inventory(self, extra_entries=(), extra_refs=()):
        inv = inventory()
        inv["entries"] += list(extra_entries)
        inv["labels"] += [{"label": l, "source": {"file": TEX, "line_start": e["source_ranges"][0]["line_start"],
                                                  "line_end": e["source_ranges"][0]["line_start"]},
                           "owner_id": e["id"]} for e in extra_entries for l in e["labels"]]
        inv["references"] += list(extra_refs)
        (self.tmp / "docs/source-inventory.json").write_text(json.dumps(inv))

    def test_wrapper_body_ends_at_next_command(self):
        """Regression: names in an `open ... in` line or the next docstring are not exports of the
        preceding wrapper."""
        proofs = CH2_PROOFS.replace(
            "theorem Remark2_1_holds : Remark2_1 := StatisticalRL.Foo.remark\n",
            "theorem Remark2_1_holds : Remark2_1 := StatisticalRL.Foo.remark\n\n"
            "open StatisticalRL.Bleed.Namespace in\n"
            "/-- From `StatisticalRL.Bleed.other_export`. -/\n")
        (self.tmp / "Formalization/Statements/Ch2Proofs.lean").write_text(proofs)
        n = {x["id"]: x for x in gn.build(gn.Reader(self.tmp))["nodes"]}
        self.assertEqual(n["ch2-remark-2.1"]["library_exports"], ["StatisticalRL.Foo.remark"])
        self.assertEqual(n["label:eq:p"]["library_exports"], ["StatisticalRL.Foo.pq"])
        text = "theorem A_holds : A := by\n  exact X.y\n-- note X.z\ntheorem B_holds : B := X.w\n"
        self.assertEqual(text[:gn.wrapper_end(text, 10)], "theorem A_holds : A := by\n  exact X.y\n")

    def test_entry_citing_a_display_inside_its_remark_attaches_to_the_remark(self):
        self.write_inventory([entry("ch2-remark-2.2", "remark", "2.2", 160, 170),
                              entry("label:eq:r", "display", "2.7", 163, 165, ["eq:r"])])
        ch2 = CH2.replace("end StatisticalRL.Statements",
                          "/-- Remark 2.2 (`chapters/prelim.tex:160–170`; coefficient `eq:r`, `:163–165`). -/\n"
                          "def Remark2_2 : Prop := True\n\nend StatisticalRL.Statements")
        (self.tmp / "Formalization/Statements/Ch2.lean").write_text(ch2)
        (self.tmp / "Formalization/Statements/Ch2Proofs.lean").write_text(CH2_PROOFS.replace(
            "end StatisticalRL.Statements", "theorem Remark2_2_holds : Remark2_2 := StatisticalRL.Foo.r2\n\n"
            "end StatisticalRL.Statements"))
        (self.tmp / "docs/COVERAGE.md").write_text(COVERAGE + "| Remark 2.2, prelim lines 160–170 | x | **Proved** (`Remark2_2`). |\n")
        n = {x["id"]: x for x in gn.build(gn.Reader(self.tmp))["nodes"]}
        self.assertEqual([e["name"] for e in n["ch2-remark-2.2"]["statement_entries"]],
                         ["StatisticalRL.Statements.Remark2_2"])
        self.assertEqual(n["ch2-remark-2.2"]["proof_status"], "proved")
        self.assertNotIn("label:eq:r", n)

    def test_long_first_range_does_not_capture_a_numbered_result(self):
        """The inner-result rule is for remarks only: an entry whose first range is a long span
        containing a lemma is not attached to that lemma."""
        ch2 = CH2.replace("end StatisticalRL.Statements",
                          "/-- Prose claim after the proof, `chapters/prelim.tex:95–115`. -/\n"
                          "def Lemma2_4_tail : Prop := True\n\nend StatisticalRL.Statements")
        (self.tmp / "Formalization/Statements/Ch2.lean").write_text(ch2)
        n = {x["id"]: x for x in gn.build(gn.Reader(self.tmp))["nodes"]}
        self.assertEqual(n["label:lem:d"]["statement_entries"][0]["name"], "StatisticalRL.Statements.Lemma2_4_tail")
        # (with a range containing the whole lemma, the lemma is the overlap target as before; the
        # inner-result shortcut only ever picks remarks)

    def test_joint_entry_attaches_paired_label_confirmed_by_coverage(self):
        self.write_inventory([entry("label:eq:s", "display", "2.8", 200, 202, ["eq:s"]),
                              entry("label:eq:t", "display", "2.9", 210, 212, ["eq:t"])])
        ch2 = CH2.replace("end StatisticalRL.Statements",
                          "/-- `eq:s`, `chapters/prelim.tex:200–202`, with `eq:t`, `chapters/prelim.tex:209–213`. -/\n"
                          "def Eq_s : Prop := True\n\nend StatisticalRL.Statements")
        (self.tmp / "Formalization/Statements/Ch2.lean").write_text(ch2)
        (self.tmp / "Formalization/Statements/Ch2Proofs.lean").write_text(CH2_PROOFS.replace(
            "end StatisticalRL.Statements", "theorem Eq_s_holds : Eq_s := StatisticalRL.Foo.s\n\n"
            "end StatisticalRL.Statements"))
        (self.tmp / "docs/COVERAGE.md").write_text(COVERAGE + "| `eq:s` and `eq:t` | `Eq_s` | **Proved** (`Eq_s`). |\n")
        n = {x["id"]: x for x in gn.build(gn.Reader(self.tmp))["nodes"]}
        self.assertEqual(n["label:eq:t"]["proof_status"], "proved")
        # a label in parentheses after the item is context, not a confirmation
        (self.tmp / "docs/COVERAGE.md").write_text(COVERAGE + "| `eq:s` (with `eq:t`) | `Eq_s` | **Proved** (`Eq_s`). |\n")
        n = {x["id"]: x for x in gn.build(gn.Reader(self.tmp))["nodes"]}
        self.assertEqual(n["label:eq:t"]["statement_entries"], [])
        self.assertEqual(n["label:eq:t"]["proof_status"], "open")
        # without the confirming row the paired label is context only
        (self.tmp / "docs/COVERAGE.md").write_text(COVERAGE + "| `eq:s` | `Eq_s` | **Proved** (`Eq_s`). |\n")
        n = {x["id"]: x for x in gn.build(gn.Reader(self.tmp))["nodes"]}
        self.assertNotIn("label:eq:t", n)

    def closing_fixture(self, rows: str):
        self.write_inventory(
            [entry("ch2-remark-2.3", "remark", "2.3", 180, 182, ["rem:o"]),
             entry("ch2-remark-2.4", "remark", "2.4", 184, 186, ["rem:i"]),
             entry("ch2-remark-2.5", "remark", "2.5", 188, 190, ["rem:e"]),
             entry("ch2-remark-2.6", "remark", "2.6", 192, 196, ["rem:u"])],
            [{"kind": "cross_reference", "targets": ["rem:o"], "source": {"file": TEX, "line_start": 194, "line_end": 194}},
             {"kind": "cross_reference", "targets": ["rem:i", "rem:e"],
              "source": {"file": TEX, "line_start": 195, "line_end": 195}}])
        (self.tmp / "docs/COVERAGE.md").write_text(COVERAGE + rows)
        return gn.build(gn.Reader(self.tmp))

    ROWS = ("| Remark 2.3, prelim lines 180–182 | none | **Out of scope: cited result** [x2020]; "
            "user decision 2026-11-09. |\n"
            "| Remark 2.4, prelim lines 184–186 | none | **Implied by `Thm2_3_corrected`** (corrected clause). |\n"
            "| Remark 2.5, prelim lines 188–190 | none | **Explanatory (no mathematical claim)** attribution. |\n"
            "| Read-off after Theorem 2.3, prelim line 87 | none | **Implied by `Lemma2_1`** (Õ form not a Prop). |\n")

    def test_closing_statuses_never_count_as_proved(self):
        data = self.closing_fixture(self.ROWS)
        n = {x["id"]: x for x in data["nodes"]}
        self.assertEqual(n["ch2-remark-2.3"]["statement_status"], "cited-out-of-scope")
        self.assertEqual(n["ch2-remark-2.3"]["decision_anchors"], ["2026-11-09"])
        self.assertEqual(n["ch2-remark-2.4"]["statement_status"], "implied")
        self.assertEqual(n["ch2-remark-2.4"]["implied_variant"], "corrected")   # inherits the entry's suffix
        self.assertEqual(n["ch2-remark-2.4"]["implied_by"], ["StatisticalRL.Statements.Thm2_3_corrected"])
        self.assertEqual(n["ch2-remark-2.5"]["statement_status"], "explanatory")
        for nid in ("ch2-remark-2.3", "ch2-remark-2.4", "ch2-remark-2.5"):
            self.assertEqual(n[nid]["proof_status"], "open")
            self.assertFalse(n[nid]["printed_with_cited_printed"])
        s = data["summary"]
        self.assertEqual(s["closing_not_proved"]["implied"], {"nodes": 1, "rows_without_node": 1})
        self.assertEqual(s["closing_not_proved"]["explanatory"], {"nodes": 1, "rows_without_node": 0})
        self.assertEqual(s["closing_not_proved"]["cited-out-of-scope"], {"nodes": 1, "rows_without_node": 0})
        self.assertEqual(s["named_results_with_ledger_record"], 3)
        self.assertEqual(sum(s["prose_by_statement_status"][k] for k in ("printed", "corrected", "restricted")), 3)
        # the unlabelled read-off row (Theorem 2.3 mentioned after the item start) is not attached to Theorem 2.3
        self.assertEqual([r["line"] for r in data["closing_rows_without_node"]], [10])
        self.assertNotIn(10, n["label:thm:c"]["coverage_rows"])
        self.assertEqual(data["warnings"], [])
        nxt = gn.render_next(data)
        self.assertIn("INCOMPLETE", nxt)
        self.assertIn("statement `implied (corrected)` · by `Thm2_3_corrected`", nxt)
        # Remark 2.6 uses the out-of-scope remark: blocked; implied/explanatory uses do not block
        blocked = nxt.split("### Blocked", 1)[1].split("##", 1)[0]
        self.assertIn("Remark 2.6", blocked)
        self.assertIn("waits on Remark 2.3", blocked)
        self.assertNotIn("Remark 2.4", blocked)
        ready = nxt.split("### Remarks and displayed claims", 1)[1].split("###", 1)[0]
        for r in ("Remark 2.3", "Remark 2.4", "Remark 2.5"):
            self.assertNotIn(r, ready)
        self.assertIn("## Cited results out of scope (user decision) (1 nodes, 0 unlabelled rows)", nxt)

    def test_closing_row_classifies_a_display_a_joint_entry_cites(self):
        """A step-definition display cited by a joint entry (eq:RBMLE_online) is classified by its own
        reviewed row: an explanatory row never makes the attached entry count as a proof of it."""
        cov = COVERAGE.replace("| Displays `eq:p` and `eq:q` | x | **Proved** (`Eq_p_q`). |\n",
                               "| Display `eq:p` | x | **Proved** (`Eq_p_q`). |\n"
                               "| Step definition `eq:q` | none | **Explanatory (no mathematical claim).** |\n")
        (self.tmp / "docs/COVERAGE.md").write_text(cov)
        n = {x["id"]: x for x in gn.build(gn.Reader(self.tmp))["nodes"]}
        self.assertEqual((n["label:eq:q"]["statement_status"], n["label:eq:q"]["proof_status"]),
                         ("explanatory", "open"))
        self.assertEqual(n["label:eq:p"]["proof_status"], "proved")

    def test_closing_rows_fail_closed(self):
        with self.assertRaises(SystemExit):   # no dated user-decision anchor
            self.closing_fixture("| Remark 2.3 | none | **Out of scope: cited result** [x2020]. |\n")
        with self.assertRaises(SystemExit):   # names no statement entry
            self.closing_fixture("| Remark 2.4 | none | **Implied by `NoSuchEntry`** |\n")
        with self.assertRaises(SystemExit):   # a numbered result can never be closed
            self.closing_fixture("| Lemma 2.4, `lem:d` | none | **Explanatory (no mathematical claim).** |\n")
        with self.assertRaises(SystemExit):   # names an entry whose node is not proved
            self.closing_fixture("| Remark 2.4 | none | **Implied by `Eq_p_q`** |\n"
                                 "| Displays `eq:p` | x | **Partial:** one clause. |\n")

    def test_reader_words_for_closing_statuses(self):
        from reader import graph, lean
        for k in gn.CLOSING_STATUSES:
            self.assertIn(k, graph.STATEMENT_WORDS)
            word = graph.STATEMENT_WORDS[k].lower()   # each says in words that nothing is proved for it
            self.assertTrue("not proved" in word or "not separately proved" in word or "no mathematical claim" in word)
            self.assertIn(k, lean.STATUS)
            self.assertTrue(any(w in lean.STATUS[k][0].lower() for w in ("not proved", "not separately proved",
                                                                             "nothing proved")))
            self.assertNotIn(k, lean.PROVED)
        self.assertEqual(lean.coverage_status("**Implied by `X`** ..."), "implied")
        self.assertEqual(lean.coverage_status("**Explanatory (no mathematical claim)** ..."), "explanatory")
        self.assertEqual(lean.coverage_status("**Out of scope: cited result** ..."), "cited-out-of-scope")


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
        """Algorithms, assumptions and definitions never carry a status or a card in their own row.
        They may be the home only of an entry whose item is a display inside them (for example
        eq:online_RBMLE inside the VPO algorithm); that card is rendered right after the block."""
        from reader.tex import label_id
        tops = {id(t): p for p in self.site.pages for t in p.blocks}
        for page, b in self.blocks.values():
            if self.site.kind_of(b) not in ("algorithm", "assumption", "definition"):
                continue
            self.assertEqual(self.site.statuses(b), [], b.labels)
            for e in self.site.home.get(id(b), []):
                inv = self.site.inv_by_id.get(self.site.entry_node.get(e.full, ""), {})
                self.assertIn(inv.get("kind"), ("display", "subequations"), (b.labels, e.name))
                self.assertTrue(any(f'id="{label_id(lab)}"' in b.html for lab in inv.get("labels", [])),
                                (b.labels, e.name))
            if id(b) in tops:
                col, after = self.site.lean_columns(page, b)
                self.assertNotIn('class="lean-card"', col, b.labels)
                for e in self.site.home.get(id(b), []):
                    self.assertIn(f'id="lean-{e.name}"', after, (b.labels, e.name))


if __name__ == "__main__":
    unittest.main()
