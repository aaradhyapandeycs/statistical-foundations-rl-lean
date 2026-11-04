# Independent review: corrected UCBVI T5/T6 bounds

I reviewed the source-facing statement and proof for `lem:bound-T56` against
`chapters/onlineRL.tex:1055–1092` and the definitions of T0 and iota at
`onlineRL.tex:1027–1033` and `726–734`. The source chapter SHA-256 is
`393a4d26c228d833a27e54a4913489e499d2143f2f9b80ebf3c55d9a9ccb8c53`.

The indexed statement is
`StatisticalRL.Statements.Lemma5_9_K2_corrected`; its applying theorem is
`StatisticalRL.Statements.Lemma5_9_K2_corrected_holds`. The producer is
`StatisticalRL.OnlineRL.onlineSourceAllocated_T3_T56_simplified_actual_confidence`.
The statement keeps the source reset-vector and sequential transition law,
the episode/state/action quantifiers, the three initial inequalities with
probability at least `1 − 14 S² A H² K δ′`, and both simplified inequalities
with probability at least `1 − 30 S² A H² K δ′` under the printed large-K
condition. It retains the printed T0 and iota expressions. The chosen
universal bonus constants are `c₁ = 4` and `c₂ = 16`; these do not depend on
the MDP parameters. The wrapper applies the stronger strict-confidence export,
weakens strict probability to the indexed non-strict bounds, and projects the
joint event to the simplified event.

The corrected variant has explicit limits. It assumes `K ≥ 2` (C12), uses
the finite zero-count completion and H analysis charge described in C8, and
uses one fixed deterministic maximizing tie rule. It proves the listed
auxiliary bounds, not the final UCBVI regret theorem. The proof does not take
T3 concentration, a variance estimate, or an optimism event as an external
premise: the actual suffix-family concentration is discharged and consumed
inside the same-law probability chain.

## Source and build evidence

The indexed statement SHA-256 is
`080a370fa6284418b2518fc81c539c4305a10d40d49e8628e9c5758572a6d373`; the
applying proof SHA-256 is
`4a41357b1d94ca72f59f303bac7cfe04c1eb84b66b8cda1405ff611964a44d82`. The
complete 659-source freeze and final affected-build manifest are recorded in
`online-t56-joint-verification.md`. I independently checked every frozen
source hash and every corresponding OLean hash in both the candidate and the
workspace against the frozen state and terminal manifest: 659 of 659 matched.
The run records 97 rebuilt modules and 562 verified reused modules; all 97
module exits and the `Formalization` and `Audit` exits are zero. The full
namespace audit covers 6,382 declarations and reports only `propext`,
`Classical.choice`, and `Quot.sound`.

This was a guarded affected rebuild against the verified 566-module baseline,
with ancestry through the previously checked 520, 513, 477, 453, 447, 438, and
418-module states. It is not a fresh clean 659-module build. The historical
418-module clean run did not pin OLean or package byte hashes; later reuse
receipts bind the inherited artifacts to subsequent checked states. The
compiler and dependency paths and recorded before/after dependency metadata
matched the pinned verification environment.

Focused component, statement-index and actual-export probes passed before the
affected build. The final integrated full-library audit also checks the
integrated exports transitively. One non-fatal deprecation warning remains
for `Set.setOf_app_iff` in the applying proof; it is disclosed and did not
affect compilation or the axiom audit.

This review supports only the corrected/restricted Lemma 5.9 entry and its
stated evidence. It does not certify the unrestricted K=1 endpoint, the
printed undefined zero-count algorithm, a complete chapter, or the final
regret theorem.
