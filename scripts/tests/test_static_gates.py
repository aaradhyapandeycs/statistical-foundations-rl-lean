"""Fixture tests for scripts/static_gates.py (one passing and one failing tree per gate)."""

import io
import json
import os
import shutil
import sys
import tempfile
import unittest

# STATIC_GATES_DIR lets a reviewer run these tests against another copy of the
# script (for example a pre-fix version) to confirm the bypass tests fail there.
sys.path.insert(0, os.environ.get("STATIC_GATES_DIR")
                or os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))
import static_gates as sg  # noqa: E402

CH2 = '''import Mathlib.Data.Real.Basic
import Formalization.Probability.Defs

/-! Statement index, chapter 2. -/

namespace StatisticalRL.Statements

/-- `lem:foo`, `chapters/prelim.tex:10–20`. Corrected variant, see C1. -/
def Lemma2_1 : Prop := ∀ x : ℝ, x = x

end StatisticalRL.Statements
'''

CH2_PROOFS = '''import Formalization.Statements.Ch2
namespace StatisticalRL.Statements
theorem Lemma2_1_holds : Lemma2_1 := fun _ => rfl
end StatisticalRL.Statements
'''

LIB = '''import Mathlib.Data.Real.Basic
/-! Library; this lemma admits a short proof (no sorry here). -/
namespace StatisticalRL.Probability
-- sorry in a comment is fine
/-- docstring mentioning axiom and opaque is fine -/
theorem helper : True := by
  trivial
def name : String := "sorry"
end StatisticalRL.Probability
'''

LEDGER = {
    "certified_named_results": [{
        "name": "Lemma 2.1",
        "lean_export": "StatisticalRL.Probability.helper",
        "lean_statement": "StatisticalRL.Statements.Lemma2_1",
        "lean_statement_proof": "StatisticalRL.Statements.Lemma2_1_holds",
        "statement_scope": "See C1.",
    }],
    "proved_variants": [],
}

ISSUES = "# Source issues\n\n## Candidate C1: something\n"
COVERAGE = "| Lemma 2.1 | `StatisticalRL.Statements.Lemma2_1` proved; see C1 |\n"


class GateFixture(unittest.TestCase):
    def setUp(self):
        self.root = tempfile.mkdtemp(prefix="static-gates-")
        self.files = {
            "Formalization/Statements/Ch2.lean": CH2,
            "Formalization/Statements/Ch2Proofs.lean": CH2_PROOFS,
            "Formalization/Probability/Defs.lean": LIB,
            "docs/SOURCE-ISSUES.md": ISSUES,
            "docs/COVERAGE.md": COVERAGE,
            "docs/named-result-status.json": json.dumps(LEDGER),
        }
        self.write_all()
        self.bootstrap()

    def bootstrap(self):
        """Create the initial allowlists for the fixture tree (growth from empty)."""
        try:
            code = sg.run(self.root, list(sg.GATES), write=True, out=io.StringIO(), allow_grow=True)
        except TypeError:  # pre-fix script without allow_grow
            code = sg.run(self.root, list(sg.GATES), write=True, out=io.StringIO())
        self.assertEqual(code, 0)

    def tearDown(self):
        shutil.rmtree(self.root)

    def write_all(self):
        for rel, txt in self.files.items():
            p = os.path.join(self.root, rel)
            if not os.path.isdir(os.path.dirname(p)):
                os.makedirs(os.path.dirname(p))
            with open(p, "w", encoding="utf-8") as fh:
                fh.write(txt)

    def put(self, rel, txt):
        self.files[rel] = txt
        self.write_all()

    def gate(self, g):
        out = io.StringIO()
        code = sg.run(self.root, [g], out=out)
        return code, out.getvalue()

    def assertPass(self, g):
        code, out = self.gate(g)
        self.assertEqual(code, 0, out)

    def assertFail(self, g, needle):
        code, out = self.gate(g)
        self.assertEqual(code, 1, out)
        self.assertIn(needle, out)


class TestG1(GateFixture):
    def test_pass(self):
        self.assertPass("G1")

    def test_fail_sorry(self):
        self.put("Formalization/Probability/Bad.lean",
                 "namespace StatisticalRL\ntheorem t : 1 = 2 := by\n  sorry\nend StatisticalRL\n")
        self.assertFail("G1", "Bad.lean:3: forbidden token not on frozen allowlist scripts/gates/g1_forbidden_tokens.txt (Formalization/Probability/Bad.lean: sorry;")

    def test_fail_axiom(self):
        self.put("Formalization/Probability/Bad.lean", "namespace StatisticalRL\naxiom bad : False\nend StatisticalRL\n")
        self.assertFail("G1", "axiom declaration")


class TestG2(GateFixture):
    def test_pass(self):
        self.assertPass("G2")

    def test_fail_new_statement_import(self):
        self.put("Formalization/Statements/Ch2.lean", "import Formalization.Probability.Heavy\n" + CH2)
        self.assertFail("G2", "not on frozen allowlist scripts/gates/g2_statement_imports.txt")

    def test_fail_bare_mathlib(self):
        self.put("Formalization/Probability/New.lean", "import Mathlib\nnamespace StatisticalRL\nend StatisticalRL\n")
        self.assertFail("G2", "bare `import Mathlib`")

    def test_fail_stale(self):
        self.put("Formalization/Statements/Ch2.lean", CH2.replace("import Formalization.Probability.Defs\n", ""))
        self.assertFail("G2", "stale entry")


class TestG3(GateFixture):
    def test_pass(self):
        self.assertPass("G3")

    def test_fail_missing_holds(self):
        self.put("Formalization/Statements/Ch2Proofs.lean", "import Formalization.Statements.Ch2\n")
        self.assertFail("G3", "has 0 `theorem Lemma2_1_holds`")

    def test_fail_unknown_cid(self):
        self.put("docs/SOURCE-ISSUES.md", "# Source issues\n")
        self.assertFail("G3", "cites C1")

    def test_fail_ledger_name(self):
        led = json.loads(json.dumps(LEDGER))
        led["certified_named_results"][0]["lean_statement"] = "StatisticalRL.Statements.Lemma2_9"
        self.put("docs/named-result-status.json", json.dumps(led))
        self.assertFail("G3", "lean_statement StatisticalRL.Statements.Lemma2_9 is not")

    def test_fail_no_tex_range(self):
        self.put("Formalization/Statements/Ch2.lean", CH2.replace("`chapters/prelim.tex:10–20`", "somewhere"))
        self.assertFail("G3", "cites no `.tex:a-b` line range")


class TestG4(GateFixture):
    def test_pass(self):
        self.assertPass("G4")

    def test_fail_unresolved(self):
        self.put("docs/COVERAGE.md", COVERAGE + "| x | `StatisticalRL.Probability.missing_lemma` |\n")
        self.assertFail("G4", "cited Lean name not declared in Formalization/ not on frozen allowlist scripts/gates/g4_unresolved_names.txt (StatisticalRL.Probability.missing_lemma")


class TestG6(GateFixture):
    def test_pass(self):
        self.assertPass("G6")

    def test_fail_outside_namespace(self):
        self.put("Formalization/Probability/Escape.lean", "namespace Foo\ntheorem t : True := trivial\nend Foo\n")
        self.assertFail("G6", "Escape.lean:2: declaration outside namespace StatisticalRL (not covered by Audit.lean) not on frozen allowlist scripts/gates/g6_namespace_exceptions.txt (Formalization/Probability/Escape.lean: Foo.t")


NS = "namespace StatisticalRL\n%s\nend StatisticalRL\n"


class TestG1Bypasses(GateFixture):
    """Review REVIEW-static-gates.md, fixtures A1-A4."""

    def bad(self, body):
        self.put("Formalization/Probability/Bad.lean", NS % body)

    def test_a1_char_literal_quote(self):
        self.bad("def q : Char := '\"'\ntheorem t1 : False := by sorry\ndef z : String := \"x\"")
        self.assertFail("G1", "sorry")

    def test_a1_char_literal_escaped_quote(self):
        self.bad("def q : Char := '\\''\ndef r : Char := '\"'\ntheorem t1 : False := by sorry")
        self.assertFail("G1", "sorry")

    def test_a2_raw_string_hash(self):
        self.bad('def s : String := r#"a"b"#\ntheorem t2 : False := by sorry\ndef z2 : String := "x"')
        self.assertFail("G1", "sorry")

    def test_a2_raw_string_plain_and_double_hash(self):
        self.bad('def s : String := r"a\\"\ndef u : String := r##"x"#y"##\ntheorem t : False := by sorry')
        self.assertFail("G1", "sorry")

    def test_prime_identifier_not_char_literal(self):
        # `f'` followed by a string must not be read as a char literal.
        self.bad("def f' : String := \"a'b\"\ndef g := f'\ntheorem t : True := trivial")
        self.assertPass("G1")

    def test_a3_extern_in_attribute_list(self):
        self.bad('@[simp, extern "foo"] def e3 : Nat := 1')
        self.assertFail("G1", "extern")

    def test_a3_run_cmd_add_decl(self):
        self.bad("run_cmd Lean.addDecl (.axiomDecl { name := `ax, levelParams := [], "
                 "type := .const `False [], isUnsafe := false })")
        self.assertFail("G1", "addDecl/axiomDecl")

    def test_a3_decide_native(self):
        self.bad("theorem t3 : 2 = 2 := by decide +native")
        self.assertFail("G1", "decide +native")

    def test_a3_decide_native_config(self):
        self.bad("theorem t3 : 2 = 2 := by decide (config := {native := true})")
        self.assertFail("G1", "native := true")

    def test_a3_of_reduce_bool(self):
        self.bad("theorem t3b : True := Lean.ofReduceBool _ _ rfl")
        self.assertFail("G1", "ofReduceBool")

    def test_a3_eval_command(self):
        self.bad("#eval 1")
        self.assertFail("G1", "metaprogramming command")

    def test_a4_set_option_in_admit(self):
        self.bad("set_option maxHeartbeats 0 in theorem t4c : False := by admit")
        self.assertFail("G1", "admit")

    def test_no_lean_files(self):
        shutil.rmtree(os.path.join(self.root, "Formalization"))
        self.assertFail("G1", "no Lean files")

    def test_count_per_file(self):
        # One allowlisted occurrence does not license a second one in the same file.
        self.put("scripts/gates/g1_forbidden_tokens.txt", "Formalization/Probability/Bad.lean: sorry\n")
        self.bad("theorem a : False := by sorry\ntheorem b : False := by sorry")
        self.assertFail("G1", "2 found, 1 allowed")


class TestDeltaBypasses(GateFixture):
    """Delta review fixtures B1/B2 and the Audit.lean exemption."""

    def bad(self, body):
        self.put("Formalization/Probability/Bad.lean", NS % body)

    def test_b1_interpolated_string_char_literal(self):
        self.bad('def z : String := s!"{\'"\'}"\ntheorem b1 : False := by sorry')
        self.assertFail("G1", "sorry")

    def test_b1_interpolated_nested_string(self):
        self.bad('def z (x : Nat) : String := m!"{f "q"} {x}"\ntheorem b1 : False := by sorry')
        self.assertFail("G1", "sorry")

    def test_b1_sorry_inside_interpolation(self):
        self.bad('def z : String := s!"{(sorry : Nat)}"')
        self.assertFail("G1", "sorry")

    def test_plain_string_with_brace_ok(self):
        self.bad('def z : String := "a{b\'"\ntheorem t : True := trivial')
        self.assertPass("G1")

    def test_b2_command_mid_line(self):
        self.bad('theorem ok3 : True := trivial run_cmd Lean.logInfo "x"')
        self.assertFail("G1", "metaprogramming command")

    def test_b2_end_then_declaration(self):
        self.put("Formalization/Probability/Escape.lean",
                 "namespace StatisticalRL\nend StatisticalRL theorem leakedB2 : True := trivial\n")
        self.assertFail("G6", "mid-line `theorem`")

    def test_audit_single_run_cmd_exempt(self):
        self.put("Audit.lean", "import Formalization\nrun_cmd do\n  pure ()\n")
        self.assertPass("G1")

    def test_audit_second_run_cmd_fails(self):
        self.put("Audit.lean", "import Formalization\nrun_cmd do\n  pure ()\n#eval 1\n")
        self.assertFail("G1", "Audit.lean: metaprogramming command")


class TestG3Bypass(GateFixture):
    def test_holds_wrapper_with_other_type(self):
        self.put("Formalization/Statements/Ch2Proofs.lean", CH2_PROOFS.replace(
            "theorem Lemma2_1_holds : Lemma2_1 := fun _ => rfl",
            "theorem Lemma2_1_holds : Lemma2_1 → False := fun h => h"))
        self.assertFail("G3", "must have type exactly")

    def test_holds_with_universe_passes(self):
        self.put("Formalization/Statements/Ch2Proofs.lean", CH2_PROOFS.replace(
            "theorem Lemma2_1_holds : Lemma2_1 :=", "theorem Lemma2_1_holds.{u} : Lemma2_1.{u} :="))
        self.assertPass("G3")


class TestWriteShrinkOnly(GateFixture):
    def test_write_does_not_grow_g1(self):
        self.put("Formalization/Probability/Bad.lean", NS % "theorem t : False := by sorry")
        code = sg.run(self.root, ["G1"], write=True, out=io.StringIO(), allow_grow=True)
        self.assertEqual(code, 1)
        self.assertFail("G1", "sorry")

    def test_write_does_not_grow_without_flag(self):
        self.put("Formalization/Probability/New.lean", "import Mathlib\n" + NS % "")
        self.assertEqual(sg.run(self.root, ["G2"], write=True, out=io.StringIO()), 1)
        self.assertFail("G2", "bare `import Mathlib`")

    def test_write_grows_with_flag(self):
        self.put("Formalization/Probability/New.lean", "import Mathlib\n" + NS % "")
        self.assertEqual(sg.run(self.root, ["G2"], write=True, out=io.StringIO(), allow_grow=True), 0)
        self.assertPass("G2")

    def test_write_shrinks(self):
        self.put("Formalization/Statements/Ch2.lean", CH2.replace("import Formalization.Probability.Defs\n", ""))
        self.assertFail("G2", "stale entry")
        self.assertEqual(sg.run(self.root, ["G2"], write=True, out=io.StringIO()), 0)
        self.assertPass("G2")

    def test_missing_allowlist_fails(self):
        os.remove(os.path.join(self.root, "scripts", "gates", "g6_namespace_exceptions.txt"))
        self.assertFail("G6", "missing allowlist")


class TestG6Bypasses(GateFixture):
    """Review fixtures A5/A6: declarations escaping namespace StatisticalRL."""

    def leak(self, body):
        self.put("Formalization/Probability/Escape.lean", NS % "" + body + "\n")

    def test_open_in_prefix(self):
        self.leak("open Nat in theorem leaked1 : True := trivial")
        self.assertFail("G6", "leaked1")

    def test_set_option_in_prefix(self):
        self.leak("set_option maxHeartbeats 400 in theorem leaked2 : True := trivial")
        self.assertFail("G6", "leaked2")

    def test_nested_attribute_brackets(self):
        self.leak("@[simp, aesop safe (rule_sets := [X])] theorem leaked3 : True := trivial")
        self.assertFail("G6", "leaked3")

    def test_name_on_next_line(self):
        self.leak("theorem\n  leaked4 : True := trivial")
        self.assertFail("G6", "leaked4")

    def test_macro_outside(self):
        self.leak('macro "leaked5" : term => `(0)')
        self.assertFail("G6", "`macro` command outside StatisticalRL")

    def test_deriving_instance_outside(self):
        self.leak("deriving instance Repr for Nat")
        self.assertFail("G6", "`deriving instance` command outside StatisticalRL")

    def test_mutual_end(self):
        self.leak("namespace StatisticalRL\nmutual\ndef f : Nat → Nat | _ => 0\nend\n"
                  "end StatisticalRL\ntheorem caught : True := trivial")
        self.assertFail("G6", "caught")

    def test_inside_namespace_ok(self):
        self.put("Formalization/Probability/Fine.lean", NS % (
            "open Nat in theorem ok1 : True := trivial\n"
            "@[simp, aesop safe (rule_sets := [X])] theorem ok2 : True := trivial\n"
            "local notation \"T\" => Nat\ntheorem\n  ok3 : True := trivial"))
        self.assertPass("G6")


class TestLexer(unittest.TestCase):
    def test_mask_nested_and_strings(self):
        code, comments = sg.mask_lean('a /- x /- y -/ sorry -/ b "sorry" -- sorry\nc')
        self.assertNotIn("sorry", code)
        self.assertEqual(len(comments), 1)
        self.assertEqual(code.count("\n"), 1)

    def test_universe_suffix(self):
        ds = sg.scan_decls("namespace StatisticalRL\ntheorem foo.{u} : True := trivial\nend StatisticalRL\n")
        self.assertEqual(ds[0]["name"], "StatisticalRL.foo")


if __name__ == "__main__":
    unittest.main()
