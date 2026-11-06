# Online Q-learning verification and scope

Status: **fresh full project compilation and axiom audit passed**.
The source proof and canonical integration have independent source reviews;
the entire monograph remains **incomplete**. The full check compiled all 1,052
project modules and audited 8,873 project declarations.

The release adds the complete `Lemma5_18_restricted` and
`Thm5_16_corrected` Props to `Formalization/Statements/Ch5.lean` and applies
their existing providers in `Ch5Proofs.lean`. The algorithm's actual trajectory
law, Q/count updates, previsit episode list, optimal Q/V, deployed policy return
and regret are represented by proved definitions and bridges. No confidence
event or correctness certificate is assumed in either source-facing theorem.

The source-facing theorem is
`StatisticalRL.OnlineRL.qLearning_actualRegret_rate_confidence`.
The explicit bound is
`max(1,19 exp(1)) sqrt(S A H⁵ K (1+log(4SAT/delta)))`, with strict success
probability greater than 1−delta. The original bonus uses cb=2 and
`log(SAT/delta)`; the rate logarithm is separate. H=K=1 and singleton carriers
are included. The two-clause optimism/error result also applies to the same
completed actual algorithm. Fixed ties, initial V=H and proof repairs are
disclosed in [C20](SOURCE-ISSUES.md#C20).

## Retained bounded evidence

The final private consolidation checked 665 modules: 88 were freshly compiled
in its last run and 577 used recursively compatible, hash-verified predecessor
artifacts. Across the retained stage runs, 376 distinct modules were freshly
compiled from their final exact sources. These counts must not be presented as
665 fresh compilations. All 20 previous public wrappers and both new wrappers
remain in the physical `Ch5Proofs.lean`; the compatibility QLearningProofs
module only imports it. The definition-only Ch5 closure contains 44 modules.

The closed probe checks 22 ordered actual exports and definition identities;
all transitive axiom records use only `propext`, `Classical.choice` and
`Quot.sound`. Nine legacy semantic identities are checked separately.
Sources, compiler and eight pinned package-artifact metadata maps were equal
before and after. Metadata preservation is not a package-content byte seal.

The final bounded status SHA-256 is
`328bb1d5169e615e621388b99f67ccb22e977b9d22eb756d89aabea322afb8ad`;
the source/artifact index is
`0da6f6056e0b8a6abac753d83e89b4a6930b99a974a1767e74b93544a78e52db`;
the physical consolidation handoff is
`505471d5cfa612e13c62831995babd652cfbc7a5f52954768a528e1765ebf674`.
The [independent review record](critic-online-qlearning-source.md) states its
scope and trust boundary. Historical failed checks remain preserved and do not
become passing evidence through this release.

## Fresh full public-tree check

The unmodified `python3 scripts/check.py` completed successfully at
`2026-11-06T00:47:51.844073+00:00` with initially empty project build artifacts.
All 1,052 project modules were compiled from their exact sources, including
consumers outside the earlier 665-module scope. No project OLeans were reused.
The actual Audit import closure covered all modules and checked 8,873
project declarations, allowing only `propext`, `Classical.choice` and `Quot.sound`.

The [full manifest](validation/online-qlearning-20261105/manifest.json) records
source hashes, actual commands, per-module exit codes and timings. The
[Audit output](validation/online-qlearning-20261105/Audit.log) and
[guard summary](validation/online-qlearning-20261105/guards.json) accompany it.
All project sources, frozen public inputs, compiler, runner and configuration
hashes matched before and after. All eight pinned dependency artifact metadata
maps matched across 85,038 paths; dependency artifacts
were not rebuilt. This is metadata preservation, not a dependency byte seal.

The checked library contains 101,188 physical Lean lines including comments
and blank lines, 6,065 more than the preceding published main. Line counts do
not measure source coverage. The named-result ledger has 41 covered entries
out of 90 inventoried environments: 23 original-result entries including
disclosed restrictions, and 18 corrected or restricted variants. The inventory
does not cover every substantive prose claim. No whole chapter or book is certified.

A separate independent source-only release review checked the proposed tree,
including statement scope, C20, imports and comment-only preservation.
Its review SHA-256 is
`0f7921ebd7ed899025fc648716214c41ecd683cd86b59a173b514efedd0e19a1`.
Historical failures remain preserved; the successful full run does not turn
an earlier failed or partial run into passing evidence.

Reproduce after the pinned dependency setup in the README:

```sh
python3 scripts/check.py
```
