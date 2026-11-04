# Fixed-policy variance verification

Source: arXiv:2610.41903v1, `lem:cum-var-ub-Hsquare-ucbvi-mean`,
`chapters/onlineRL.tex:648–658`.

- Actual source export:
  `StatisticalRL.OnlineRL.finitePolicy_expected_cumulative_variance_le_horizon_sq`.
- Full statement and applying proof:
  `StatisticalRL.Statements.Lemma5_4` and `Lemma5_4_holds`.
- Seven qualified definition/proof modules compiled freshly; a seven-export
  probe passed with standard axioms. The Chapter 5 statement and proof modules
  then compiled; a probe printed five actual statement proofs, including the
  new `Lemma5_4_holds`, with standard axioms.
- The guarded affected check completed with exit 0: 11 modules rebuilt plus
  509 unchanged source/artifact pairs reused from the verified 513-module
  joint-bound snapshot, covering all 520 current project modules.
- The whole-library axiom audit passed for **5,441 declarations**, allowing
  only `propext`, `Classical.choice`, and `Quot.sound`.
- Verification run: `20261104T111021369410Z`.
- Manifest SHA-256:
  `d57460d3948a340d57b67ab1b92e41989a82e3336f181e3dca7852e3b809665c`.
- Affected-check driver SHA-256:
  `e3f66d9590250f5cd7cd17d382bdc43d4e5d6fe97e289e86dd0dc6ca6b7f309c`.
- Chapter 5 statement source SHA-256:
  `41c78abbfd010e8c7a46c7e9eacf3da7f912d925bb4db9eb25456a718ae45ec9`.
- Chapter 5 proof source SHA-256:
  `ef81014bbeaff16437d198ca11c0607b5a4cca571630dacc8ff4f82b3e33ef0a`.

The executed command was the guarded `check_affected.py` integration driver.
It uses this repository's checker/parser and normal pinned Lean wrapper,
rebuilds the complete reverse-import closure, and runs the full Audit. This
is an affected rebuild, not a fresh clean 520-module `scripts/check.py` run.
The public fresh-checkout commands remain `lake build` and
`lake env lean Audit.lean`; local complete checking uses `python3 scripts/check.py`.

Reuse provenance is 520 → 513 → 477 → 453 → 447 → 438 → clean418. All reused
project source/artifact hashes and retained ancestry edges were checked,
along with the same resolved compiler and package locations and unchanged
dependency file metadata before/after. The historical clean418 record did
not pin OLean or package bytes; inherited artifacts are bound by the later
TV438 reuse receipts. No new clean520 claim is made.

The new expected-value lemma has no source correction. This release does
not certify adaptive T5/T6 concentration, the final online regret theorem,
any complete chapter, or the complete monograph. Project size at this
milestone is 59,246 Lean lines including comments and blanks in 520 files.

The pinned source inventory check and all eight existing scanner unit tests
also passed. The live ledger validation finds 18 unique named results with
existing evidence and coverage files.
