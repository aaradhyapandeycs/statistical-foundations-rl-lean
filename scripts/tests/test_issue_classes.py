"""The committed issue-class ledger agrees with docs/ERRATA-AND-DEVIATIONS.md (headings, counts table)."""

import json
import re
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]


class IssueClassesRecord(unittest.TestCase):
    def setUp(self):
        self.led = json.loads((ROOT / "docs/issue-classes.json").read_text())
        self.doc = (ROOT / "docs/ERRATA-AND-DEVIATIONS.md").read_text()
        errata = self.doc.split("### Errata", 1)[1].split("### Deviations", 1)[0]
        self.by_heading, cls = {}, None
        for line in errata.splitlines():
            m = re.match(r"#### Class ([A-D])", line)
            if m:
                cls = m.group(1)
            m = re.match(r"(\d+)\. \*\*", line)
            if m:
                self.by_heading[m.group(1)] = cls

    def test_entry_classes_match_headings(self):
        self.assertEqual(self.led["errata_entries"], self.by_heading)

    def test_counts_table_matches_ledger(self):
        row = re.search(r"\| \*\*Total\*\* \| \*\*(\d+)\*\* \| \*\*(\d+)\*\* \| \*\*(\d+)\*\* \| \*\*(\d+)\*\* \|", self.doc)
        table = dict(zip("ABCD", map(int, row.groups())))
        entries = {c: list(self.led["errata_entries"].values()).count(c) for c in "ABCD"}
        self.assertEqual(entries, table)
        items = {c: sum(i["class"] == c for i in self.led["items"]) for c in "ABCD"}
        m = re.search(r"gives A (\d+), B (\d+), C (\d+), D (\d+) \((\d+) items\)", self.doc)
        self.assertEqual(items, dict(zip("ABCD", map(int, m.groups()[:4]))))
        self.assertEqual(sum(items.values()), int(m.group(5)))

    def test_record_references_exist(self):
        for it in self.led["items"]:
            rec = it["record"]
            if rec and rec.startswith("Erratum "):
                self.assertIn(rec.split()[1], self.led["errata_entries"], it["item"])


if __name__ == "__main__":
    unittest.main()
