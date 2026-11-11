"""Fixture tests for scripts/move_modules.py (temporary trees only, no Lean)."""

import io
import json
import os
import shutil
import subprocess
import sys
import tempfile
import unittest

# MOVE_MODULES_DIR lets a reviewer run these tests against another copy of the
# script (for example the pre-fix version) to confirm the regression tests fail there.
sys.path.insert(0, os.environ.get("MOVE_MODULES_DIR")
                or os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))
import move_modules as mm  # noqa: E402

DEFS = '''import Mathlib.Data.Real.Basic

/-! Definitions.  The text below is a docstring, not an import:
import Formalization.Ch7Rest.Defs
-/

namespace StatisticalRL.Ch7Rest.Marl

def foo : Nat := 1

end StatisticalRL.Ch7Rest.Marl
'''

MAIN = '''/- leading comment -/
import Formalization.Ch7Rest.Defs Formalization.Ch7Rest.DefsExtra -- two modules on one line
import Formalization.MDP.Basic

/-! See `Formalization/Ch7Rest/Defs.lean` for definitions. -/

namespace StatisticalRL.Ch7Rest.Marl
theorem foo_eq : foo = 1 := rfl
end StatisticalRL.Ch7Rest.Marl
'''

EXTRA = "import Mathlib.Data.Real.Basic\nnamespace StatisticalRL.Ch7Rest\ndef bar : Nat := 2\nend StatisticalRL.Ch7Rest\n"
BASIC = "import Mathlib.Data.Real.Basic\nnamespace StatisticalRL\ndef baz : Nat := 3\nend StatisticalRL\n"
CH7 = "import Formalization.Ch7Rest.Defs\nnamespace StatisticalRL.Statements.Ch7\ndef Thm : Prop := True\nend StatisticalRL.Statements.Ch7\n"
ROOT = ("import Formalization.Ch7Rest.Defs\nimport Formalization.Ch7Rest.DefsExtra\n"
        "import Formalization.Ch7Rest.Main\nimport Formalization.MDP.Basic\nimport Formalization.Statements.Ch7\n")
AUDIT = "import Formalization\n"
COVERAGE = ("| Thm 7.6 | [Defs](../Formalization/Ch7Rest/Defs.lean), "
            "[Main](../Formalization/Ch7Rest/Main.lean#L3) | `StatisticalRL.Ch7Rest.Marl.foo_eq` |\n"
            "Extra module `Formalization.Ch7Rest.DefsExtra` and `Formalization.Ch7Rest.Defs`.\n"
            "Glob `Formalization/Ch7Rest/*.lean` stays.\n")
LEDGER = {"certified": [{"label": "thm:x", "lean": "StatisticalRL.Ch7Rest.Marl.foo_eq",
                         "file": "Formalization/Ch7Rest/Main.lean"}]}
GATE = ("# G2 frozen library -> Statements import edges. May only shrink.\n"
        "Formalization/Ch7Rest/Main.lean -> Formalization.Statements.Ch3Definitions\n")

MOVES = {"moves": [
    {"old": "Formalization.Ch7Rest.Defs", "new": "Formalization.MultiAgent.Definitions"},
    {"old": "Formalization.Ch7Rest.Main", "new": "Formalization.MultiAgent.Main"},
]}


class Fixture(unittest.TestCase):
    def setUp(self):
        self.root = tempfile.mkdtemp(prefix="move_modules_test_")
        files = {
            "Formalization/Ch7Rest/Defs.lean": DEFS,
            "Formalization/Ch7Rest/DefsExtra.lean": EXTRA,
            "Formalization/Ch7Rest/Main.lean": MAIN,
            "Formalization/MDP/Basic.lean": BASIC,
            "Formalization/Statements/Ch7.lean": CH7,
            "Formalization.lean": ROOT,
            "Audit.lean": AUDIT,
            "docs/COVERAGE.md": COVERAGE,
            "docs/named-result-status.json": json.dumps(LEDGER, indent=2) + "\n",
            "docs/critic-old.md": "Historical: Formalization/Ch7Rest/Defs.lean\n",
            "scripts/gates/g2_library_to_statements.txt": GATE,
            ".lake/build/lib/lean/Formalization/Ch7Rest/Defs.olean": "stale",
        }
        for rel, text in files.items():
            p = os.path.join(self.root, rel)
            os.makedirs(os.path.dirname(p), exist_ok=True)
            with open(p, "w", encoding="utf-8") as fh:
                fh.write(text)

    def tearDown(self):
        shutil.rmtree(self.root)

    def write_map(self, data):
        p = os.path.join(self.root, "moves.json")
        with open(p, "w", encoding="utf-8") as fh:
            json.dump(data, fh)
        return p

    def write_file(self, rel, text):
        p = os.path.join(self.root, rel)
        os.makedirs(os.path.dirname(p), exist_ok=True)
        with open(p, "w", encoding="utf-8") as fh:
            fh.write(text)

    def read(self, rel):
        with open(os.path.join(self.root, rel), encoding="utf-8") as fh:
            return fh.read()

    def run_mm(self, *args):
        out = io.StringIO()
        err = io.StringIO()
        old_err = sys.stderr
        sys.stderr = err
        try:
            code = mm.main(["--root", self.root, *args], out=out)
        finally:
            sys.stderr = old_err
        return code, out.getvalue(), err.getvalue()

    def snapshot(self):
        snap = {}
        for dp, _, fs in os.walk(self.root):
            for f in fs:
                p = os.path.join(dp, f)
                with open(p, "rb") as fh:
                    snap[os.path.relpath(p, self.root)] = fh.read()
        return snap


class TestDryRun(Fixture):
    def test_dry_run_reports_and_writes_nothing(self):
        path = self.write_map(MOVES)
        before = self.snapshot()
        code, out, _ = self.run_mm("--map", path, "--dry-run")
        self.assertEqual(code, 0)
        self.assertEqual(before, self.snapshot())
        self.assertIn("pending moves: 2", out)
        self.assertIn("- import Formalization.Ch7Rest.Defs Formalization.Ch7Rest.DefsExtra", out)
        self.assertIn("+ import Formalization.MultiAgent.Definitions Formalization.Ch7Rest.DefsExtra", out)
        self.assertIn("Lean import lines rewritten: 4 in 3 files", out)
        self.assertIn(".lake/build/lib/lean/Formalization/Ch7Rest/Defs.olean", out)
        # the docstring mention in Main.lean is reported, not rewritten
        self.assertIn("Formalization/Ch7Rest/Main.lean:5", out)

    def test_requires_mode(self):
        with self.assertRaises(SystemExit):
            mm.main(["--root", self.root, "--map", self.write_map(MOVES)], out=io.StringIO())


class TestApply(Fixture):
    def test_apply_rewrites_imports_and_docs_only(self):
        code, _, err = self.run_mm("--map", self.write_map(MOVES), "--apply", "--delete-stale")
        self.assertEqual(code, 0, err)
        self.assertFalse(os.path.exists(os.path.join(self.root, "Formalization/Ch7Rest/Defs.lean")))
        main = self.read("Formalization/MultiAgent/Main.lean")
        self.assertIn("import Formalization.MultiAgent.Definitions Formalization.Ch7Rest.DefsExtra "
                      "-- two modules on one line", main)
        # non-import content (docstring path, namespace) is untouched
        self.assertIn("See `Formalization/Ch7Rest/Defs.lean`", main)
        self.assertIn("namespace StatisticalRL.Ch7Rest.Marl", main)
        self.assertEqual(self.read("Formalization/MultiAgent/Definitions.lean"), DEFS)
        root = self.read("Formalization.lean")
        self.assertIn("import Formalization.MultiAgent.Definitions\n", root)
        self.assertIn("import Formalization.Ch7Rest.DefsExtra\n", root)  # prefix-similar module kept
        self.assertIn("import Formalization.MultiAgent.Main\n", root)
        self.assertIn("import Formalization.MultiAgent.Definitions\n", self.read("Formalization/Statements/Ch7.lean"))
        cov = self.read("docs/COVERAGE.md")
        self.assertIn("(../Formalization/MultiAgent/Definitions.lean)", cov)
        self.assertIn("(../Formalization/MultiAgent/Main.lean#L3)", cov)
        self.assertIn("`StatisticalRL.Ch7Rest.Marl.foo_eq`", cov)  # declaration name unchanged
        self.assertIn("`Formalization.Ch7Rest.DefsExtra`", cov)
        self.assertIn("`Formalization.MultiAgent.Definitions`", cov)
        self.assertIn("Formalization/Ch7Rest/*.lean", cov)
        ledger = json.loads(self.read("docs/named-result-status.json"))
        self.assertEqual(ledger["certified"][0]["lean"], "StatisticalRL.Ch7Rest.Marl.foo_eq")
        self.assertEqual(ledger["certified"][0]["file"], "Formalization/MultiAgent/Main.lean")
        self.assertIn("Formalization/MultiAgent/Main.lean -> Formalization.Statements.Ch3Definitions",
                      self.read("scripts/gates/g2_library_to_statements.txt"))
        self.assertEqual(self.read("docs/critic-old.md"), "Historical: Formalization/Ch7Rest/Defs.lean\n")
        self.assertFalse(os.path.exists(os.path.join(self.root, ".lake/build/lib/lean/Formalization/Ch7Rest/Defs.olean")))

    def test_rerun_is_idempotent(self):
        path = self.write_map(MOVES)
        self.assertEqual(self.run_mm("--map", path, "--apply")[0], 0)
        before = self.snapshot()
        code, out, _ = self.run_mm("--map", path, "--apply")
        self.assertEqual(code, 0)
        self.assertIn("pending moves: 0; already applied (skipped): 2", out)
        self.assertEqual(before, self.snapshot())

    def test_apply_with_git_uses_git_mv(self):
        if shutil.which("git") is None:
            self.skipTest("git not available")
        env = dict(os.environ, GIT_AUTHOR_NAME="t", GIT_AUTHOR_EMAIL="t@e", GIT_COMMITTER_NAME="t",
                   GIT_COMMITTER_EMAIL="t@e")
        for cmd in (["git", "init", "-q"], ["git", "add", "-A"], ["git", "commit", "-qm", "fixture"]):
            subprocess.run(cmd, cwd=self.root, check=True, env=env, stdout=subprocess.DEVNULL)
        self.assertEqual(self.run_mm("--map", self.write_map(MOVES), "--apply")[0], 0)
        status = subprocess.run(["git", "status", "--porcelain"], cwd=self.root, text=True,
                                capture_output=True, check=True).stdout
        self.assertIn("R  Formalization/Ch7Rest/Defs.lean -> Formalization/MultiAgent/Definitions.lean", status)


class TestRefusals(Fixture):
    def assert_refused(self, data, needle):
        before = self.snapshot()
        code, _, err = self.run_mm("--map", self.write_map(data), "--apply")
        self.assertEqual(code, 2)
        self.assertIn(needle, err)
        snap = self.snapshot()
        snap.pop("moves.json", None)
        before.pop("moves.json", None)
        self.assertEqual(before, snap)

    def test_refuses_statements_source(self):
        self.assert_refused({"Formalization.Statements.Ch7": "Formalization.Other.Ch7"}, "Statements")

    def test_refuses_statements_target(self):
        self.assert_refused({"Formalization.Ch7Rest.Defs": "Formalization.Statements.Defs"}, "Statements")

    def test_refuses_existing_target(self):
        self.assert_refused({"Formalization.Ch7Rest.Defs": "Formalization.MDP.Basic"}, "both source and target exist")

    def test_refuses_case_collision(self):
        self.assert_refused({"Formalization.Ch7Rest.Defs": "Formalization.MDP.basic"}, "case-insensitively")

    def test_refuses_duplicate_target(self):
        self.assert_refused({"moves": [
            {"old": "Formalization.Ch7Rest.Defs", "new": "Formalization.X.A"},
            {"old": "Formalization.Ch7Rest.Main", "new": "Formalization.X.A"}]}, "duplicate target")

    def test_refuses_chain(self):
        self.assert_refused({"moves": [
            {"old": "Formalization.Ch7Rest.Defs", "new": "Formalization.Ch7Rest.Main"},
            {"old": "Formalization.Ch7Rest.Main", "new": "Formalization.X.Main"}]}, "")

    def test_refuses_missing_source(self):
        self.assert_refused({"Formalization.Ch7Rest.Nope": "Formalization.X.Nope"}, "neither source nor target")

    def test_refuses_malformed(self):
        self.assert_refused({"Ch7Rest.Defs": "Formalization.X.Defs"}, "malformed")


class TestHeaderParser(unittest.TestCase):
    def test_header_stops_at_first_command(self):
        text = ("/-! doc\nimport Formalization.A\n-/\nimport Formalization.B\n\n-- c\n"
                "import Formalization.C\nnamespace X\n")
        new, ch = mm.rewrite_imports(text, {"Formalization.A": "Formalization.Z",
                                            "Formalization.B": "Formalization.Y",
                                            "Formalization.C": "Formalization.W"})
        self.assertEqual([c[0] for c in ch], [4, 7])
        self.assertIn("/-! doc\nimport Formalization.A\n-/", new)


def git_init(root):
    env = dict(os.environ, GIT_AUTHOR_NAME="t", GIT_AUTHOR_EMAIL="t@e", GIT_COMMITTER_NAME="t",
               GIT_COMMITTER_EMAIL="t@e")
    for cmd in (["git", "init", "-q"], ["git", "add", "-A"], ["git", "commit", "-qm", "fixture"]):
        subprocess.run(cmd, cwd=root, check=True, env=env, stdout=subprocess.DEVNULL)


class TestReviewFixes(Fixture):
    """Regression tests for review findings R1-R4 and link labels (each failed on the pre-fix script)."""

    # R1: never delete through a symlinked .lake/build
    def test_r1_refuses_symlinked_build_dir(self):
        foreign = tempfile.mkdtemp(prefix="move_modules_foreign_")
        try:
            olean = os.path.join(foreign, "lib/lean/Formalization/Ch7Rest/Defs.olean")
            os.makedirs(os.path.dirname(olean))
            with open(olean, "w") as fh:
                fh.write("foreign")
            shutil.rmtree(os.path.join(self.root, ".lake/build"))
            os.symlink(foreign, os.path.join(self.root, ".lake/build"))
            code, _, err = self.run_mm("--map", self.write_map(MOVES), "--apply", "--delete-stale")
            self.assertEqual(code, 2)
            self.assertTrue(os.path.exists(olean), "foreign artifact was deleted")
            self.assertIn("symlink", err)
            self.assertTrue(os.path.exists(os.path.join(self.root, "Formalization/Ch7Rest/Defs.lean")))
        finally:
            shutil.rmtree(foreign)

    def test_r1_refuses_symlinked_lake_dir(self):
        foreign = tempfile.mkdtemp(prefix="move_modules_foreign_")
        try:
            shutil.move(os.path.join(self.root, ".lake"), os.path.join(foreign, ".lake"))
            os.symlink(os.path.join(foreign, ".lake"), os.path.join(self.root, ".lake"))
            code, _, _ = self.run_mm("--map", self.write_map(MOVES), "--apply", "--delete-stale")
            self.assertEqual(code, 2)
            self.assertTrue(os.path.exists(os.path.join(foreign, ".lake/build/lib/lean/Formalization/Ch7Rest/Defs.olean")))
        finally:
            shutil.rmtree(foreign)

    def test_r1_skips_symlinked_artifact(self):
        target = os.path.join(self.root, "elsewhere.olean")
        with open(target, "w") as fh:
            fh.write("x")
        art = os.path.join(self.root, ".lake/build/lib/lean/Formalization/Ch7Rest/Main.olean")
        os.symlink(target, art)
        code, _, _ = self.run_mm("--map", self.write_map(MOVES), "--apply", "--delete-stale")
        self.assertEqual(code, 2)
        self.assertTrue(os.path.exists(target))

    def test_r1_deletes_regular_artifact(self):
        code, _, err = self.run_mm("--map", self.write_map(MOVES), "--apply", "--delete-stale")
        self.assertEqual(code, 0, err)
        self.assertFalse(os.path.exists(os.path.join(self.root, ".lake/build/lib/lean/Formalization/Ch7Rest/Defs.olean")))

    # R2: already-applied entries are still rewritten and checked
    def test_r2_rerun_repairs_crashed_move(self):
        os.makedirs(os.path.join(self.root, "Formalization/MultiAgent"))
        for a, b in (("Defs", "Definitions"), ("Main", "Main")):
            os.rename(os.path.join(self.root, f"Formalization/Ch7Rest/{a}.lean"),
                      os.path.join(self.root, f"Formalization/MultiAgent/{b}.lean"))
        code, out, err = self.run_mm("--map", self.write_map(MOVES), "--apply")
        self.assertEqual(code, 0, err)
        self.assertIn("already applied (skipped): 2", out)
        self.assertNotIn("Formalization.Ch7Rest.Defs\n", self.read("Formalization.lean"))
        self.assertIn("import Formalization.MultiAgent.Definitions Formalization.Ch7Rest.DefsExtra",
                      self.read("Formalization/MultiAgent/Main.lean"))
        self.assertIn("(../Formalization/MultiAgent/Definitions.lean)", self.read("docs/COVERAGE.md"))

    def test_r2_old_import_added_after_move_is_rewritten(self):
        path = self.write_map(MOVES)
        self.assertEqual(self.run_mm("--map", path, "--apply")[0], 0)
        self.write_file("Formalization/Late.lean", "import Formalization.Ch7Rest.Main\n")
        code, _, err = self.run_mm("--map", path, "--apply")
        self.assertEqual(code, 0, err)
        self.assertEqual(self.read("Formalization/Late.lean"), "import Formalization.MultiAgent.Main\n")

    # R3: case-insensitive guards
    def test_r3_refuses_lowercase_statements_target(self):
        code, _, err = self.run_mm("--map", self.write_map({"Formalization.Ch7Rest.Defs": "Formalization.statements.Defs"}),
                                   "--dry-run")
        self.assertEqual(code, 2)
        self.assertIn("Statements", err)

    def test_r3_refuses_case_only_directory_difference(self):
        code, _, err = self.run_mm("--map", self.write_map({"Formalization.Ch7Rest.Defs": "Formalization.mdp.Defs"}),
                                   "--dry-run")
        self.assertEqual(code, 2)
        self.assertIn("differs only in case", err)

    def test_r3_refuses_case_only_difference_between_targets(self):
        code, _, err = self.run_mm("--map", self.write_map({"moves": [
            {"old": "Formalization.Ch7Rest.Defs", "new": "Formalization.MultiAgent.A"},
            {"old": "Formalization.Ch7Rest.Main", "new": "Formalization.Multiagent.B"}]}), "--dry-run")
        self.assertEqual(code, 2)
        self.assertIn("differs only in case", err)

    # R4: comment-prefixed imports, line endings, dirty tree, rollback
    def test_r4_import_after_block_comment_on_same_line(self):
        self.write_file("Formalization/Other.lean", "/- c -/ import Formalization.Ch7Rest.Defs\nnamespace X\nend X\n")
        code, _, err = self.run_mm("--map", self.write_map(MOVES), "--apply")
        self.assertEqual(code, 0, err)
        self.assertEqual(self.read("Formalization/Other.lean"),
                         "/- c -/ import Formalization.MultiAgent.Definitions\nnamespace X\nend X\n")

    def test_r4_preserves_crlf(self):
        crlf = "import Formalization.Ch7Rest.Defs\r\nnamespace X\r\nend X\r\n"
        with open(os.path.join(self.root, "Formalization/Crlf.lean"), "w", newline="") as fh:
            fh.write(crlf)
        self.assertEqual(self.run_mm("--map", self.write_map(MOVES), "--apply")[0], 0)
        with open(os.path.join(self.root, "Formalization/Crlf.lean"), newline="") as fh:
            self.assertEqual(fh.read(), crlf.replace("Ch7Rest.Defs", "MultiAgent.Definitions"))

    def test_r4_refuses_dirty_touched_path(self):
        if shutil.which("git") is None:
            self.skipTest("git not available")
        path = self.write_map(MOVES)
        git_init(self.root)
        self.write_file("Formalization/Ch7Rest/Main.lean", MAIN + "-- wip\n")
        before = self.snapshot()
        code, _, err = self.run_mm("--map", path, "--apply")
        self.assertEqual(code, 2)
        self.assertIn("uncommitted", err)
        after = self.snapshot()
        self.assertEqual({k: v for k, v in before.items() if not k.startswith(".git")},
                         {k: v for k, v in after.items() if not k.startswith(".git")})
        self.assertEqual(self.run_mm("--map", path, "--apply", "--allow-dirty")[0], 0)

    def test_r4_refuses_import_after_header(self):
        # an import after the header is refused before anything is written
        self.write_file("Formalization/Bad.lean", "namespace X\nend X\nimport Formalization.Ch7Rest.Defs\n")
        path = self.write_map(MOVES)
        before = self.snapshot()
        code, _, err = self.run_mm("--map", path, "--apply")
        self.assertEqual(code, 2)
        self.assertIn("after the file header", err)
        self.assertEqual(before, self.snapshot())

    def test_r4_rollback_restores_tree(self):
        path = self.write_map(MOVES)
        before = self.snapshot()
        real = mm.rewrite_doc
        calls = {"n": 0}

        def boom(text, mapping, regs):
            calls["n"] += 1
            if calls["n"] > 50:
                raise RuntimeError("injected failure")
            return real(text, mapping, regs)
        mm.rewrite_doc = boom
        try:
            plan, mapping = mm.build_plan(self.root, path, [])
            calls["n"] = 50
            with self.assertRaises(mm.MoveError):
                mm.apply(self.root, plan, mapping, False, True, io.StringIO())
        finally:
            mm.rewrite_doc = real
        self.assertEqual(before, self.snapshot())

    # link labels in COVERAGE follow the link target
    def test_link_label_renamed(self):
        self.write_file("docs/COVERAGE.md", "[Main.lean](../Formalization/Ch7Rest/Main.lean), "
                        "[Ch7Rest/Defs.lean](../Formalization/Ch7Rest/Defs.lean#L2), [the proof](../Formalization/Ch7Rest/Main.lean)\n")
        self.assertEqual(self.run_mm("--map", self.write_map(MOVES), "--apply")[0], 0)
        self.assertEqual(self.read("docs/COVERAGE.md"),
                         "[Main.lean](../Formalization/MultiAgent/Main.lean), "
                         "[MultiAgent/Definitions.lean](../Formalization/MultiAgent/Definitions.lean#L2), "
                         "[the proof](../Formalization/MultiAgent/Main.lean)\n")


class TestStatementsDefinitionsMove(Fixture):
    """Only a non-index Statements module, explicitly flagged, may move out of Statements/."""

    def setUp(self):
        super().setUp()
        self.write_file("Formalization/Statements/Ch3Definitions.lean",
                        "import Mathlib.Data.Real.Basic\nnamespace StatisticalRL.X\ndef d : Nat := 0\nend StatisticalRL.X\n")
        self.write_file("Formalization/Generative/Use.lean", "import Formalization.Statements.Ch3Definitions\n")

    def test_flagged_definitions_module_moves(self):
        data = {"moves": [{"old": "Formalization.Statements.Ch3Definitions",
                           "new": "Formalization.Generative.ModelBasedDefinitions",
                           "allow_statements_source": True}]}
        code, _, err = self.run_mm("--map", self.write_map(data), "--apply")
        self.assertEqual(code, 0, err)
        self.assertEqual(self.read("Formalization/Generative/Use.lean"),
                         "import Formalization.Generative.ModelBasedDefinitions\n")
        self.assertIn("Formalization/Ch7Rest/Main.lean -> Formalization.Generative.ModelBasedDefinitions",
                      self.read("scripts/gates/g2_library_to_statements.txt"))

    def test_unflagged_definitions_module_refused(self):
        self.assert_refused_map({"Formalization.Statements.Ch3Definitions": "Formalization.Generative.D"},
                                "allow_statements_source")

    def test_index_module_refused_even_when_flagged(self):
        for old in ("Formalization.Statements.Ch7", "Formalization.Statements.Ch7Proofs",
                    "Formalization.Statements.QLearningProofs"):
            self.assert_refused_map({"moves": [{"old": old, "new": "Formalization.Other.X",
                                                "allow_statements_source": True}]}, "index")

    def assert_refused_map(self, data, needle):
        before = self.snapshot()
        code, _, err = self.run_mm("--map", self.write_map(data), "--apply")
        self.assertEqual(code, 2)
        self.assertIn(needle, err)
        snap = self.snapshot()
        snap.pop("moves.json", None)
        before.pop("moves.json", None)
        self.assertEqual(before, snap)


class TestShortFormsAndScopes(Fixture):
    def setUp(self):
        super().setUp()
        # a second Main.lean elsewhere makes the bare name `Main.lean` ambiguous
        self.write_file("Formalization/Other/Main.lean", "import Mathlib.Data.Real.Basic\n")
        self.write_file("docs/ERRATA-AND-DEVIATIONS.md",
                        "See Ch7Rest/Defs.lean:12, `Defs.lean`, Ch7Rest/Main.lean and Main.lean.\n"
                        "Namespace StatisticalRL.Ch7Rest.Defs.foo and module tail Ch7Rest.Defs stay.\n"
                        "Glob Ch7Rest/De*.lean and stem Defs stay; dir Ch7Rest/ stays.\n")
        self.write_file("docs/critic-old.md", "Historical: Formalization/Ch7Rest/Defs.lean\n")
        self.write_file("docs/validation/run/manifest.json",
                        '{"Formalization/Ch7Rest/Defs.lean": "00"}\n')
        self.write_file("site/reader/x.py", "# see Formalization/Ch7Rest/Main.lean\n")
        self.write_file("site/_build/page.html", "Formalization/Ch7Rest/Main.lean\n")

    def test_tails_and_bare_names(self):
        code, _, err = self.run_mm("--map", self.write_map(MOVES), "--apply", "--doc",
                                   "docs/ERRATA-AND-DEVIATIONS.md")
        self.assertEqual(code, 0, err)
        self.assertEqual(self.read("docs/ERRATA-AND-DEVIATIONS.md"),
                         "See MultiAgent/Definitions.lean:12, `MultiAgent/Definitions.lean`, "
                         "MultiAgent/Main.lean and Main.lean.\n"
                         "Namespace StatisticalRL.Ch7Rest.Defs.foo and module tail Ch7Rest.Defs stay.\n"
                         "Glob Ch7Rest/De*.lean and stem Defs stay; dir Ch7Rest/ stays.\n")
        # default scope leaves review records and site sources alone
        self.assertEqual(self.read("docs/critic-old.md"), "Historical: Formalization/Ch7Rest/Defs.lean\n")
        self.assertEqual(self.read("site/reader/x.py"), "# see Formalization/Ch7Rest/Main.lean\n")

    def test_all_docs_scope(self):
        code, out, err = self.run_mm("--map", self.write_map(MOVES), "--apply", "--all-docs")
        self.assertEqual(code, 0, err)
        self.assertEqual(self.read("docs/critic-old.md"), "Historical: Formalization/MultiAgent/Definitions.lean\n")
        self.assertEqual(self.read("site/reader/x.py"), "# see Formalization/MultiAgent/Main.lean\n")
        self.assertIn("MultiAgent/Definitions.lean:12", self.read("docs/ERRATA-AND-DEVIATIONS.md"))
        # hash-pinned manifests and build output are never edited
        self.assertIn("Formalization/Ch7Rest/Defs.lean", self.read("docs/validation/run/manifest.json"))
        self.assertEqual(self.read("site/_build/page.html"), "Formalization/Ch7Rest/Main.lean\n")
        self.assertIn("docs/ERRATA-AND-DEVIATIONS.md:3", out)  # stem leftover reported

    def test_history_records_get_full_paths_only(self):
        self.write_file("docs/critic-old.md", "Ran <builder folder>/Defs.lean; repo file Formalization/Ch7Rest/Defs.lean, "
                        "tail Ch7Rest/Defs.lean, bare `Defs.lean`\n")
        self.assertEqual(self.run_mm("--map", self.write_map(MOVES), "--apply", "--all-docs")[0], 0)
        self.assertEqual(self.read("docs/critic-old.md"),
                         "Ran <builder folder>/Defs.lean; repo file Formalization/MultiAgent/Definitions.lean, "
                         "tail Ch7Rest/Defs.lean, bare `Defs.lean`\n")

    def test_keep_history(self):
        code, _, err = self.run_mm("--map", self.write_map(MOVES), "--apply", "--all-docs", "--keep-history")
        self.assertEqual(code, 0, err)
        self.assertEqual(self.read("docs/critic-old.md"), "Historical: Formalization/Ch7Rest/Defs.lean\n")
        self.assertEqual(self.read("site/reader/x.py"), "# see Formalization/MultiAgent/Main.lean\n")

    def test_keep_history_requires_all_docs(self):
        with self.assertRaises(SystemExit):
            mm.main(["--root", self.root, "--map", self.write_map(MOVES), "--apply", "--keep-history"],
                    out=io.StringIO())

    def test_same_tail_namespace_untouched(self):
        # a namespace whose tail equals a moved module's tail (RobustRL.Ch7.LowerBound73 case)
        self.write_file("docs/COVERAGE.md", "`StatisticalRL.Ch7Rest.Main.thm` in Formalization.Ch7Rest.Main\n")
        self.assertEqual(self.run_mm("--map", self.write_map(MOVES), "--apply")[0], 0)
        self.assertEqual(self.read("docs/COVERAGE.md"),
                         "`StatisticalRL.Ch7Rest.Main.thm` in Formalization.MultiAgent.Main\n")


class TestLeanComments(Fixture):
    def test_rewrites_comments_only(self):
        code, _, err = self.run_mm("--map", self.write_map(MOVES), "--apply", "--lean-comments")
        self.assertEqual(code, 0, err)
        main = self.read("Formalization/MultiAgent/Main.lean")
        self.assertIn("See `Formalization/MultiAgent/Definitions.lean` for definitions.", main)
        self.assertIn("namespace StatisticalRL.Ch7Rest.Marl", main)
        # the docstring in Defs that looks like an import is a comment: rewritten as a module name
        self.assertIn("import Formalization.MultiAgent.Definitions\n-/",
                      self.read("Formalization/MultiAgent/Definitions.lean"))

    def test_without_flag_comments_untouched(self):
        self.assertEqual(self.run_mm("--map", self.write_map(MOVES), "--apply")[0], 0)
        self.assertIn("See `Formalization/Ch7Rest/Defs.lean`", self.read("Formalization/MultiAgent/Main.lean"))

    def test_code_only_detects_code_change(self):
        a = "import A\n/- c -/\ndef x := 1 -- note\n"
        self.assertEqual(mm.code_only(a), mm.code_only("import B\n/- other -/\ndef x := 1 -- changed\n"))
        self.assertNotEqual(mm.code_only(a), mm.code_only("import A\n/- c -/\ndef x := 2 -- note\n"))

    def test_string_literal_not_a_comment(self):
        text = 'def s := "-- Formalization/Ch7Rest/Defs.lean"\n-- Formalization/Ch7Rest/Defs.lean\n'
        regs = mm.doc_regexes({"Formalization.Ch7Rest.Defs": "Formalization.MultiAgent.Definitions"})
        new, _ = mm.rewrite_lean_comments(text, {"Formalization.Ch7Rest.Defs": "Formalization.MultiAgent.Definitions"}, regs)
        self.assertEqual(new, 'def s := "-- Formalization/Ch7Rest/Defs.lean"\n-- Formalization/MultiAgent/Definitions.lean\n')


if __name__ == "__main__":
    unittest.main()
