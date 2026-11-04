# Complete corrected T5/T6 verification

Source: arXiv:2610.41903v1, `lem:bound-T56`,
`chapters/onlineRL.tex:1055–1092`. Chapter SHA-256:
`393a4d26c228d833a27e54a4913489e499d2143f2f9b80ebf3c55d9a9ccb8c53`.

- Actual export: `StatisticalRL.OnlineRL.onlineSourceAllocated_T3_T56_simplified_actual_confidence`.
- Complete statement: `StatisticalRL.Statements.Lemma5_9_K2_corrected`.
- Applying proof: `StatisticalRL.Statements.Lemma5_9_K2_corrected_holds`.
- The first event contains all three printed initial bounds at probability
  at least 1−14 S²AH²K delta-prime. Under the printed large-K premise, the
  second contains both simplified bounds at probability at least 1−30 S²AH²K
  delta-prime. The producer proves strict bounds and a stronger joint event;
  the applying wrapper weakens and projects those conclusions.
- The same reset-vector and causal transition law supplies every quantity.
  The chosen universal c1=4,c2=16 are independent of problem parameters.
  Scope: K≥2 (C12), finite zero-count completion and H charge(C8), and fixed
  deterministic maximizing ties. No intermediate event/variance is assumed.
- Focused qualification passed for 52 T56 components, 30 suffix/T0/algebra
  components, and 11 final source modules, with actual-export axiom probes.
  Full Chapter 5 statements and applying proofs then compiled and were probed.
- Guarded affected integration: **97 rebuilt + 562 verified reused =659**
  project modules. Full audit: **6,382 declarations**, permitting only
  `propext`, `Classical.choice`, `Quot.sound`.
- Run: `20261104T141921097070Z`.
- Manifest SHA-256: `5d9909a2953015e0f29295f77aa0de79c16942103cfd7d6b1bc7c8bc1c6c8ca7`.
- Affected driver SHA-256: `b5f1bae14850be37c9df46a298e81b09171f6b27a3e4b74f34a0de3d394446e5`.
- Chapter 5 statement SHA-256: `080a370fa6284418b2518fc81c539c4305a10d40d49e8628e9c5758572a6d373`.
- Chapter 5 applying proof SHA-256: `4a41357b1d94ca72f59f303bac7cfe04c1eb84b66b8cda1405ff611964a44d82`.

The command executed was the guarded affected-check driver, using the
repository checker/parser and pinned Lean wrapper. It rebuilt every new or
reverse-dependent module and the full Audit. This is not a new clean
`python3 scripts/check.py` run across 659 modules. Public fresh-checkout
commands remain `lake build` and `lake env lean Audit.lean`; local complete
checking uses `python3 scripts/check.py`.

Reuse ancestry is659→566→520→513→477→453→447→438→clean418. Current source/
OLean hashes and ancestry edges were rechecked. Compiler/package paths and
dependency metadata were unchanged. The historical clean418 run did not pin
OLean/package bytes; those inherited artifacts are bound by later reuse
receipts. Separately, public566 GitHub CI run 41829324463 passed its complete
build, inventory and `scripts/check.py` audit.

Size: **72,393 project Lean lines**, including comments/blanks, in 659 files.
Ledger: 18 original named entries with disclosed limits, plus five corrected
variants. This release does not certify final regret, any whole chapter or
the whole monograph. Earlier failed probes remain isolated and uncounted.
