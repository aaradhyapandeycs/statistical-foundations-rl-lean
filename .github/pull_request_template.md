## Summary

<!-- What this PR changes. Name the source results it touches (label, number, `.tex:a–b` range), or write "infrastructure only". -->

## Checklist

- [ ] **Printed statement first.** For each source result touched: the printed statement is stated (or quoted) before any variant; source label and exact `.tex` line range cited.
- [ ] Statement entry in `Formalization/Statements/ChN.lean` and exactly one `X_holds` in `ChNProofs.lean` (or N/A).
- [ ] `_corrected` / `_restricted` entries state how they differ from the printed result and link a `docs/SOURCE-ISSUES.md` entry (or N/A).
- [ ] **Critic review.** Builder ≠ critic; critic report path: `docs/critic-…md` (or "infrastructure only").
- [ ] **Axioms.** No `sorry`, `admit`, custom `axiom`, `native_decide`, `implemented_by`, `unsafe`, `opaque`; axiom audit shows only `propext`, `Classical.choice`, `Quot.sound`.
- [ ] No statement or signature change to existing exports (or each is listed and justified below).
- [ ] **Full check.** Command, verification id/timestamp, module count and the axiom audit line:
  ```
  <paste>
  ```
- [ ] **Docs and ledger updated.** `docs/COVERAGE.md` row, `docs/named-result-status.json` record, `docs/PROGRESS.md` ownership (or N/A).
- [ ] `python3 scripts/static_gates.py` passes. Any change to `scripts/gates/*.txt` only removes entries (growth is justified below).
- [ ] New Lean files: module docstring with label and `.tex` range; under `namespace StatisticalRL`; no bare `import Mathlib`.
- [ ] **No private paths** (`/Users/…`, `.local/`, `/private/tmp`, scratch files) in tracked files; `scripts/run_before_push.sh` passes. <!-- release-scan: allow -->
- [ ] No whole-book or whole-chapter completion wording; infrastructure is not described as a completed source result.

## Notes / justifications
