# Independent review: Lemma 5.3 reciprocal-count bound

## Source and statement

I reviewed the pinned source `source/upstream/tex/chapters/onlineRL.tex`,
SHA-256 `393a4d26c228d833a27e54a4913489e499d2143f2f9b80ebf3c55d9a9ccb8c53`,
Lemma 5.3 (`lem:sum-inv-Nhk-ucbvi`), lines 638–646. It bounds the episode-major
sum of `1 / max(N_h^k(s_h^k,a_h^k), 1)` by
`2 S A H log₂ K`, for `K ≥ 2`.

The public statement is `StatisticalRL.Statements.Lemma5_3` in
[`Ch5.lean`](../Formalization/Statements/Ch5.lean). It keeps the source
denominator, K-domain, and episode-major loop order. The formulation quantifies
over any finite causal episode planner and realized path, which is a direct
generalization of the source algorithm-specific deterministic count claim.
Its only typeclass assumptions are finite state/action carriers; it adds no
probability event, bonus condition, positive-count premise, or concentration
estimate. Classical equality deciders are local to the statement section and
do not become theorem hypotheses.

## Proof review

The source proof's first visit is retained: for a row visited `N > 0` times,
the rank-indexed sum is `1 + harmonic(N - 1)`; for `N = 0`, it is zero. The
proof then bounds the harmonic term and explicitly handles the zero- and
one-visit cases before using `2 + log(K - 1) ≤ 2 log₂ K`. The actual-history
wrapper identifies the strict-past observed-row count with the visit rank,
aggregates over rows and stages, and commutes the finite sums only in the
applying wrapper to match the source's `k`-outer, `h`-inner order.

The reviewed exports are `StatisticalRL.OnlineRL.onlineSequential_maxOne_reciprocal_count_budget`
and `StatisticalRL.Statements.Lemma5_3_holds`. The applying proof is in
[`Ch5Proofs.lean`](../Formalization/Statements/Ch5Proofs.lean). The helper
definition module contains only the source reciprocal-count definition; the
statement module imports definition modules, while theorem dependencies stay
in the proof module.

## Build evidence and limits

The focused source/index run `run-lem53-qualified-20261104-08` succeeded for
both provider modules, the provider export probe, `Ch5`, `Ch5Proofs`, and the
actual statement-proof probe. The probe reported only `propext`,
`Classical.choice`, and `Quot.sound`. Earlier failed attempts were retained;
run 07 compiled its Lean targets but failed an obsolete Python postcheck, so
run 08 is the first complete focused receipt.

The guarded integration check then rebuilt 6 modules and verified 662 reused
modules against the public 666-module baseline. The whole-project audit passed
for 6,460 declarations with the standard three axioms. This was an affected
rebuild, not a fresh clean build of all 668 modules. The historical clean 418
baseline did not contain OLean or package byte hashes; later recorded reuse
receipts bind the inherited artifacts. Current sources, compiled artifacts,
reuse ancestry, and compiler/package path and metadata checks were verified.

The full ledger retains other Chapter 5 limitations and does not certify the
chapter or monograph as a whole.
