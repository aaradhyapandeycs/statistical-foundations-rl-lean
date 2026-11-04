# Complete corrected joint W1/W2/W3 verification

The endpoint is the complete corrected/restricted Lemma 5.7,
`lem:bound-W1-W2-ucbvi-proof`, `chapters/onlineRL.tex:925–957`.
`StatisticalRL.Statements.Lemma5_7_K2_corrected` expands all three actual
W sums, T6 quantities, coefficients, iota, confidence allocation and one
joint probability event. Its proof applies the existing joint export.
Scope is K≥2 (C12), the finite zero-count completion (C8), fixed deterministic
greedy tie and source confidence/bonus domains; singleton states are covered.
This does not certify the original K=1 claim or a final regret theorem.

The fresh production-layout check compiled 35 proof modules plus one
definition-only module against the verified477 baseline, checking every
baseline source and OLean before and after. The six-export probe passed
with only `propext`, `Classical.choice` and `Quot.sound`. The extracted W3
definition required restoration of its original Fintype/DecidableEq context;
the immutable failed preview was retained, and corrected preview v2 was
freshly compiled and independently reviewed. Raw copied draft OLeans were
not accepted as qualification evidence. The complete statement and proof
wrapper also compiled and passed their actual-export axiom probe.

The affected integration rebuilt 40 modules and reused 473 unchanged modules
from the verified477 baseline. Its whole-library audit passed 5,423
declarations with only the standard axioms. Every one of the 513 source
files was frozen and checked, all reused OLeans were pinned, and the driver
rechecked the compiler, package paths and shared-package metadata afterward.
No dependency files or pins changed. Linter warnings about unused arguments
and tactic syntax remain in the raw logs; no compilation error was accepted.

Before publication, six stale module comments calling the files uncompiled
were corrected. All bytes outside those module comments and all Lean tokens
were checked unchanged. The initial successful513 snapshot was retained;
the final immutable candidate was then rebuilt and audited as reported here.
No statement, proof or import changed during that cleanup.

Evidence run: `verification/20261104T093654755299Z/manifest.json`.
Manifest SHA-256: `bce1165017a1bbc0f40b621742d0cf6001fdaf97c4469ef2d9faefff56958306`.
Driver SHA-256: `2836d36ffe8345f1db516c2148348db95e6b82221a672b3e47c4198c4f39b6bb`.
Qualified preview manifest SHA-256:
`2aeec5ce04e1dbe370aacb49ae430ced9af7ecb65cd617048c35d4a1a4af3b95`.
Statement source SHA-256:
`ed9852c3a47f7e49515b8cd929207c5c08b3d7d28538c1af807383364345b10c`.
Proof-wrapper source SHA-256:
`785cfdb270e2bf4c111382797219ce65f56de1776448179fb504484bd023d1a2`.

This was **not a fresh 513-module clean build**. The retained provenance
chain is 477→453→447→438→clean418. The historical clean418 manifest did
not record OLean or dependency byte hashes; later reuse receipts bind its
inherited artifacts. Current477 and513 records pin every project source
and OLean, and all513 workspace sources/artifacts were synchronized to the
successful candidate before landing. Shared dependency metadata remained
unchanged. Public reproduction is `lake exe cache get`, `lake build`, and
`lake env lean Audit.lean`; local full reproduction remains
`python3 scripts/check.py`. This reported check used the guarded affected
driver and retained the exact evidence above.

The ledger keeps 17 original named-result entries and three separate
corrected variants, replacing the W1-only variant with this joint result.
The old W1 statement and proof remain available. No chapter or whole-monograph
completion is claimed.
