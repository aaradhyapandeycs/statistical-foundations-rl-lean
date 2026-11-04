# Independent review: corrected joint T2/T3/T4 lemma

Source: arXiv:2610.41903v1, `lem:bound-T234`,
`chapters/onlineRL.tex:988–1005`. The reviewed chapter SHA-256 is
`393a4d26c228d833a27e54a4913489e499d2143f2f9b80ebf3c55d9a9ccb8c53`.

The full statement `StatisticalRL.Statements.Lemma5_8_K2_corrected` spells
out all four displayed inequalities, including the comparison between the
first and expanded T3 radii. All quantities use the same actual reset-vector
and causal sequential-path law, true transition rows, pre-episode empirical
rows, optimistic continuations and selected true-policy continuations. The
printed iota and lower-bound hypothesis are retained.

Independent source review checked the T2 charge/count calculation, the T3
predictable conditional-variance bound and source confidence conversion, and
T4's episode return-minus-policy-value identity, conditional centering and
range. These discharge the analytic and causality prerequisites. No variance
estimate, conditional-law certificate or concentration event is assumed.
The T3 radius comparison is proved deterministically, rather than replaced
by two unrelated alternative bounds on the same sum.

T2 holds deterministically. The T3 event has failure budget at most
2 log₂(KH) delta-prime; T4 has failure strictly below 2 delta-prime. Their
intersection and log₂(KH)≥1 give the printed strict joint confidence greater
than 1−4 log₂(KH) delta-prime, without an independence assumption.

The source differences are explicit: K≥2 addresses the impossible strict
confidence at K=H=1 (SOURCE-ISSUES C12); the finite zero-count implementation
and analysis charge H address C8. One fixed deterministic maximizing tie
rule is used. This certifies a corrected/restricted auxiliary lemma, not the
unrestricted printed endpoint, Lemma 5.9/T5/T6, or the final regret theorem.

Independent review checked the qualified modules, complete statement and
applying proof, then recomputed all 566 source/OLean hashes against terminal
integration evidence. The affected rebuild passed with 50 rebuilt and 516
verified reused modules; the full audit passed for 5,811 declarations with
only `propext`, `Classical.choice` and `Quot.sound`. Added module headers
contain no stale uncompiled or draft status claims. The one nonfatal pinned
Mathlib deprecation warning does not change the result.

The terminal manifest SHA-256 is
`8de596578d0a288d673d2064cd959d42877dca03ca0eacf4ae90d48181ed4170`.
The complete statement and applying proof hashes are respectively
`13de3a0e0c693eee9e658d46e1c551c9799bff2bdd22141967457eb0dfcc8c6b`
and `b82700e1adc91bccb5cfdc2ea66ee5cf70eea5da124a3224a9c1d667dcaa17d2`.
See [verification](online-t234-joint-verification.md) for affected-build scope
and retained artifact-provenance limits. Independent review found no blocker
to this bounded release; no chapter or monograph completion is claimed.
