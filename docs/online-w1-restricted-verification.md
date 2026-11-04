# Restricted W1 verification

This report records the earlier W1-only milestone. Its coverage is now
superseded by the [complete corrected joint lemma](online-w123-joint-verification.md);
the source and validation evidence below is retained as history.

The verified endpoint is the W1 clause only of
`lem:bound-W1-W2-ucbvi-proof`, `chapters/onlineRL.tex:928–953`.
`StatisticalRL.Statements.Lemma5_7_W1_K2_corrected` states the printed
coefficients and confidence, for K≥2, the corrected zero-count convention,
fixed deterministic greedy tie, and source confidence/bonus domains. The
proof consumes the stronger 6SAHK failure-budget export and derives the
printed 12S²AHK budget using S≥1. No concentration estimate is a hypothesis.
W2, W3, the joint lemma and final regret remain open. See source issues C8/C12.

The production-layout focused check compiled all 24 new modules and probed
four actual exports, allowing only `propext`, `Classical.choice` and
`Quot.sound`. The separate two-module index check and actual statement proof
probe passed. The independent critic checked source correspondence,
qualification, definition extraction, the full statement and proof wrapper.

The affected integration compiled 28 modules and reused 449 unchanged
modules from the verified453 baseline. It checked the complete 477-source
freeze, compiler binary/version, exact package paths, every reused OLean,
the reverse import closure and all-library axiom audit. The audit passed
5,240 declarations with only the three standard axioms. The driver also
rechecked baseline sources/artifacts and unchanged shared-package metadata
afterward. Compiler linter warnings about unused arguments and tactic syntax
remain visible in the raw per-module logs; no compilation error was accepted.

Evidence run: `verification/20261104T075344964449Z/manifest.json`.
Manifest SHA-256: `3e0dc0bc0958019e9fd344cea5dbfbccc6032086feb1ac4590235aebc77e29f5`.
Driver SHA-256: `26729d325bd4984f7c1ccd11f6a979db6d62c6066cf3c632c0ed413a761a5417`.
Focused qualified leaf source SHA-256:
`5f342121ef1d0c3c34c92b2c39915357395f2706f80e167215eef03c69f384a8`.
Statement source SHA-256:
`3dc2d738571ca3b22d49ea5ed01de196620c73241777ada272bb57b59f001fa1`.
Proof-wrapper source SHA-256:
`e5fc45a06dbc677d8a221f30fbe4f2968a065b931e4c86ecf4b2fa9d60555bb8`.

This was **not a fresh 477-module clean build**. Provenance is the retained
453→447→438→clean418 chain. The historical clean418 manifest did not itself
record OLean or dependency byte hashes; later reuse receipts bind its
inherited artifacts. The current 453 and 477 manifests pin every project
source and OLean. All 477 workspace source/artifact hashes were synchronized
with the successful candidate before landing. Shared dependency files were
not modified.

Public reproduction: `lake exe cache get`, `lake build`,
`lake env lean Audit.lean`. The project's local full-check command remains
`python3 scripts/check.py`; the reported run used the guarded affected driver
and retained exact evidence above. Source provenance and dependency pins
are unchanged. No whole-chapter or monograph completion is claimed.
