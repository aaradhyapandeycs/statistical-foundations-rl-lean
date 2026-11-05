# Independent review: corrected MVP T6 variance bound

## Status and scope

This review concerns the corrected source-facing statement for Lemma 5.15,
`lem:bound-T6-ucb-mvp` (onlineRL.tex:1822–1833), and its focused proof/index
build. The 794-module affected integration has now passed. Its manifest and
complete source/OLean synchronization into the public workspace are being
handled as a separate release step. Lemma 5.14 and the MVP regret theorem
remain open.

## Source and correction boundary

The source conclusion is

\[
T_6^{\mathrm{ucb}} \le 4H T_2 + 4H W_4 + K H^2\,\iota_b
\]

with probability at least `1 − 4 S A H K δ′`, where the source definitions of
`T₂`, `T₆ᵘᶜᵇ`, and `W₄` use the same episode paths and continuation values.
The proof at lines 4487–4554 decomposes `T₆ᵘᶜᵇ` into the centered-square
martingale term `T₈` and a Bellman remainder, then controls the remainder by
the bonus charge `T₂`, the positive empirical-row error `W₄`, and `K H²`.
The AM–GM step and the stated `K H² ι_b` absorption give the displayed
coefficients.

The Lean entry deliberately records the corrected implementation conditions:

- **C8:** use the source bonus for positive visit counts and the finite analysis
  charge `H` when a row has zero observations, where the printed bonus formula
  divides by zero.
- **C13:** use the power-of-two trigger interpretation supported by the
  manuscript's doubling prose. The literal consecutive-integer trigger is not
  certified by this entry.
- **C16:** use the reciprocal allocation
  `δ′ = δ / (100 S² A² H² K²)`; this differs from the printed allocation and is
  explicitly disclosed as a corrected variant.
- Fix one deterministic maximizing tie rule.

The statement quantifies over finite state/action spaces, positive `H` and
`K`, an initial distribution, fallback state, `0 < δ ≤ 1`, and bonus constants
`c₁ ≥ 4`, `c₁² ≤ c₂`. It uses the actual sequential reset and transition law.
It covers `K = 1` by a direct deterministic branch; for `K ≥ 2`, the proof
uses the actual T8 concentration event and scalar closure. The event has no
concentration, variance-budget, or T8 premise.

## Canonicalization and focused evidence

The 30-module canonical provider mapping is
`mapping.json` in a private production-preview directory (not shipped) (SHA
`8e574a5b2d07374de5f699cdfd422837c2fe18ebfa524bef64d11af0a66bd459`). It
records the selected raw source snapshots and their canonical qualified
modules; imports and instance names are adapted to the public namespace, while
the mathematical declaration bodies are retained. Its run-1 status is SHA
`26665c0d930e72504bbcaeacca00b17aea7c0ddc55ff938dda71f2dcaa1cea14`: all 30
targets and the 45-export probe passed. Probe log SHA is
`f8c7e825a36c776bdc26eeb10710b33899d3df6b8ebcb6cc038057f839cf9812`; inspected
exports report only `propext`, `Classical.choice`, and `Quot.sound`.

The merged Ch5 index preserves the existing index and adds
`Lemma5_15_corrected` and `Lemma5_15_corrected_holds`. Exact focused pins:

- mapping: `fe02d998b4b7daef8bf7b34236933fbd53a845d216a408a45124dc9dd0a7689f`;
- runner: `85d555f0dd31a7d2aecd57d8b86ad7560bb23aa277804840370f458fdd49423a`;
- `Ch5.lean`: `b4485b97c94f22c679ae7f1d8f2b6fe3557b672066c4cf82688268f430e3df64`;
- `Ch5Proofs.lean`: `5d0ebdb67970bb05b715b8ef479c96828153cd411274a49a8b88cc0826e86ae5`;
- run-1 status: `b98aff7ad1c612720fe38d14888d7b823a888dda8ce46640ed5165fc1cab6cd4`;
- 15-export probe log: `20309e6097ed3854bb1e7db00a6731be91498fbe481da7f0bf102f5dfc84ba79`.

Both index modules and all 15 requested exports compiled; the axiom probe
reports only the standard three axioms. The focused runner pins the published
764-module baseline, the 30-provider receipt, the compiler and package
metadata, stages in a fresh overlay, and checks the output/probe records. This
is focused evidence only, not the 794-module affected integration.

## Independent assessment

The source label and displayed T6 inequality match the proposition. The
quantifiers retain the actual experiment, bonus-domain conditions and
confidence parameter, with the stated C8/C13/C16 and fixed-tie corrections
visible. The applying proof consumes `mvpActualT6_source_confidence`; its
large-count branch consumes the actual T8 confidence result, and its singleton
branch proves the event directly. The actual variance, bonus charge and
positive empirical-row error use the same retained planner, history and path.

The focused statement/proof gate and the separate 794-module affected
integration pass. The integration rebuilt 34 modules and verified reuse of
760, with 7,417 declarations in the whole-project axiom audit; the manifest
permits only `propext`, `Classical.choice`, and `Quot.sound`. Manifest SHA-256:
`1502da30b6298f37dabf028f04d7c43a6e7e0f5f5259f4d3d97254ce69b3f4c1`.
Run: `20261104T211708111013Z`; driver SHA-256:
`a5a3c9b55547b29cd66ff470f35cc795b15c955756ddeee6919b5dd936d4948a`.

This was an affected integration with retained reuse evidence, not a clean
full-project check. Final release synchronization and frozen-path review are
still pending. Nothing here certifies the uncorrected printed allocation, the
literal trigger reading, Lemma 5.14, or the full MVP regret theorem.
