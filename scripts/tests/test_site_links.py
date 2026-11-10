"""Tests for site/reader/links.py, the reader's build-time check of links into the repository."""

import sys
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "site"))
from reader.links import heading_slug, md_anchors, repo_link_problems  # noqa: E402

REPO = "https://github.com/o/r"
REV = "0123456789abcdef"
DOC = """# Title

<a id="C1"></a>

## Candidate C1: singleton actions in Theorem 3.7(i)

## Theorem 7.11's covariance `Γ` omits

```
## not a heading
```

## Same
## Same
"""
FILES = {"docs/SOURCE-ISSUES.md": DOC, "Formalization/A.lean": "x\n"}


def page(*hrefs):
    return "".join(f'<a href="{REPO}/blob/{REV}/{h}">x</a>' for h in hrefs)


class Slugs(unittest.TestCase):
    def test_heading_slug(self):
        self.assertEqual(heading_slug("Candidate C1: singleton actions in Theorem 3.7(i)"),
                         "candidate-c1-singleton-actions-in-theorem-37i")
        self.assertEqual(heading_slug("Theorem 7.11's covariance `Γ` omits"), "theorem-711s-covariance-γ-omits")

    def test_anchors(self):
        a = md_anchors(DOC)
        self.assertIn("C1", a)
        self.assertIn("title", a)
        self.assertIn("same", a)
        self.assertIn("same-1", a)
        self.assertNotIn("not-a-heading", a)


class Links(unittest.TestCase):
    def check(self, *hrefs):
        return repo_link_problems({"p": page(*hrefs)}, REPO, REV, set(FILES), FILES.__getitem__)

    def test_good(self):
        self.assertEqual(self.check("docs/SOURCE-ISSUES.md#C1", "docs/SOURCE-ISSUES.md#same-1",
                                    "Formalization/A.lean#L1-L2", "docs/SOURCE-ISSUES.md"), [])

    def test_missing_anchor(self):
        self.assertEqual(len(self.check("docs/SOURCE-ISSUES.md#C2")), 1)

    def test_directory_link(self):
        # A bare "#C44" resolved against the docs/ directory instead of the file it came from.
        self.assertEqual(len(self.check("docs/#C44")), 1)

    def test_missing_file(self):
        self.assertEqual(len(self.check("docs/NOPE.md")), 1)


class RepositoryLedgers(unittest.TestCase):
    """Anchors the reader links into exist in the working tree's ledgers."""

    def test_issue_and_decision_anchors(self):
        issues = md_anchors((ROOT / "docs/SOURCE-ISSUES.md").read_text())
        for c in ("C1", "C2", "C12", "C39", "C44"):
            self.assertIn(c, issues)
        self.assertIn("user-decisions-2026-11-09", md_anchors((ROOT / "docs/PROGRESS.md").read_text()))


if __name__ == "__main__":
    unittest.main()
