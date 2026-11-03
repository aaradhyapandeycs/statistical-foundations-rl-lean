# Independent second review: supported finite Pinsker

**Verdict:** source-semantic and fresh compiler/axiom review pass for the exact supported finite probability-vector inequality `2 TVhalfL1²≤KLfinite(p||q)`. This is not an actual-measure or countable/geometric Pinsker theorem, nor source model stability or final Q-learning closure. The author/build note `docs/critic-q-learning-finite-pinsker-independent.md` is evidence only; this review independently read the exact sources and rebuilt them in a new isolated directory.

## Exact identity

All five source/probe hashes in the earlier note recompute exactly:

| Original source under `.local/` | SHA-256 |
|---|---|
| `QLearningPinskerBinaryDraft.lean` | `e63f8df09441e70a9798b96e1e92695dbea9aa4ed0f72a3d9e754b538ffa1015` |
| `QLearningPinskerBinaryCurvatureDraft.lean` | `c63b9e764fea6447fb27ed21605b9b8724601970a95795d0bd2e71fb88f046d5` |
| `QLearningFiniteLogSumPinskerDraft.lean` | `6636fbb227eb153725e8d282a3a571487cda2cfd6995c550b3e239f2b4fa519f` |
| `QLearningFinitePinskerCoarseningDraft.lean` | `6ad7a8a679ca68d9fc9213334d76059c9a5988ce50aab7c19f4a419b561bfc80` |
| `QLearningFinitePinskerAxiomProbe.lean` | `f842414366e8923df33f6a2b3682e3a7464c16802734e2df2da236a2565df2ff` |

Author files were not modified. The first four were copied byte-identically to `.local/finite-pinsker-source-second-audit`; their copied hashes also match. The pinned source is `intro.tex:217–246` (SHA `6bfa41c0bcb9df3aa613ebe2bce9a966caaa9942e6629d52dabee5e518d0c92a`), which defines TV by supremum over events and KL(P||Q) under P≪Q, then states coefficient 2. The application is `generative_model_model_free.tex:2676–2695`, SHA `7f4eb058e00480bc0694cac93ac41e22f4cfe48aa58a00c4ccf909f805e60b22`.

## Exact final binder audit

For `qFinitePinsker`, every logical premise matches a probability-vector/support convention. Counts: TYPING 3, SOURCE 3, STANDING 4, RULED 0, EXCESS 0.

| Binder | Classification | Role |
|---|---|---|
| implicit `Omega : Type*` | TYPING | Common finite carrier |
| `[Fintype Omega]` | TYPING | Finite source probability vectors |
| `[DecidableEq Omega]` | TYPING | Finite cells/complements; classical choice suffices |
| `p : Omega→Real` | SOURCE | First/numerator law |
| `q : Omega→Real` | SOURCE | Second/reference law |
| `hp : ∀i,0≤p(i)` | STANDING | Probability nonnegativity |
| `hq : ∀i,0≤q(i)` | STANDING | Probability nonnegativity |
| `hp1 : sum p=1` | STANDING | First-law normalization |
| `hq1 : sum q=1` | STANDING | Reference-law normalization |
| `hsupport : ∀i,p(i)≠0→q(i)≠0` | SOURCE | Finite AC, in the correct direction p≪q |

For `qBinaryPinsker_source_complete`, p,q are SOURCE probability parameters, its four interval endpoints are STANDING, and its two support implications are SOURCE finite AC. There is no convexity/derivative premise in this final binary export. The earlier `*_of_convex` and interior lemmas are bounded analytic helpers whose curvature/derivative inputs are fully discharged by `qBinaryStrongPotential_convex` and its actual derivative proof in `source_complete`; they are not smuggled into the final finite theorem.

## Constant, orientation and proof substance

The finite TV definition is exactly `(1/2) sum |p−q|`. Its positive-difference cell contains q(i)≤p(i), including equality atoms which contribute zero. Normalization makes the positive and negative masses cancel, so TV equals the first-law excess on that cell. No factor two is lost in this identity.

The binary potential is `x log x+(1−x)log(1−x)`. Subtracting `2x²` yields Bregman remainder `binaryKL−2(p−q)²`; the interior second derivative is `1/x+1/(1−x)−4=(2x−1)²/[x(1−x)]≥0`. Continuity of x log x handles the closed endpoints. This supplies the correct coefficient 2, rather than merely assuming binary Pinsker.

Finite log-sum is genuinely proved for nonnegative unnormalized cell masses, using support inclusion, normalization of a positive-mass cell, the Gibbs/nonnegative-KL argument and an exact scale decomposition. Empty and all-zero-numerator cells are handled separately. Two-cell coarsening plus binary Pinsker and the TV identity proves the final finite result. No target Pinsker inequality, actual KL bound, integrability, full-support or nonzero-variance estimate is assumed.

Orientation is first law relative to second throughout. To compose with the existing row helper `qChi_rowKL_le pNominal qAlternative`, instantiate the finite Pinsker arguments as p=qAlternative.prob and q=pNominal.prob. The variable names differ across these APIs; blindly preserving their argument order would reverse AC and KL. The reviewed finite code itself has the correct direction.

## Zero support and auxiliary definition limits

`qFiniteKLTerm a b` assigns zero at a=0, including a=b=0. For positive numerator, support plus nonnegativity proves positive denominator before log-ratio algebra. The finite theorem allows numerator support to be a strict subset of reference support; no reverse support condition occurs. Coarsened reference mass zero forces numerator mass zero by atomwise support. Reference cell mass one similarly forces numerator cell mass one using the complement. Thus binary reference endpoints reduce to identical laws and KL zero, while p=0 or p=1 with interior reference retains the correct nonzero binary KL.

The auxiliary `qBinaryKL` assigns zero whenever its reference is 0 or 1, even for unsupported p. Likewise a positive `qFiniteKLTerm a 0` is totalized through real log/division. These bodies are **not global definitions of source extended KL on arbitrary real inputs**. They are valid auxiliary expressions on the explicit supported probability domain of the consuming theorems. The exported two-finite-term characterization proves this domain-limited binary representation. They must not be certified or reused as unconditional KL definitions outside that domain. This does not invalidate the final supported inequality.

Identical laws, singleton carriers, common zero atoms and zero-TV cases are included; no division by TV, KL, p−q or a coarsened zero mass is made. Empty finite carrier makes the normalization premises impossible, not a hidden missing nonempty case.

## Independent fresh build, axioms and endpoint checks

The four exact copied sources were compiled bottom-up into new `.local/finite-pinsker-source-second-audit` oleans. Its import path includes only this isolated directory, actual built project libraries and pinned package libraries; it does **not** include the author's output or general `.local` artifact path. No author olean was reused. Each matching `<stem>.log` exits zero. Existing warnings are only unused binders/simp arguments and unnecessary tactic syntax; no proof error or source mutation occurred.

Fresh `ImportAudit.lean` imports the new final artifact, repeats all sixteen author result probes and adds all seven exported definitions (23 probes total). `axioms.log` reports only propext, Classical.choice and Quot.sound throughout. Textual checks of the four original files find no sorry, admit or project axiom. The definitions and final theorem are transitively covered, not merely selected easy helpers.

`EndpointProbe.lean` compiles cleanly (`endpoints.log` empty) with six concrete uses: p=q=0, p=q=1, p=0/q=1/2, p=1/q=1/2, a sparse Bool alternative against a full-support reference, and identical degenerate Bool laws with a shared zero atom. These verify the intended API accepts genuine zero/support endpoints without a full-support premise. Unsupported binary baseline cases are intentionally excluded by the source AC domain.

The compiler slot was released immediately after the existing probes finished; no further Lean process was started for this note.

## Remaining source/production scope

Source TV is the actual event-supremum measure distance, whereas this chain exports the finite half-L1 expression. An actual measure-TV characterization and actual measure-KL/atomic-expression bridge are still required before declaring the source general Pinsker theorem or using a measure-level API. Existing finite AC-to-KL and finiteness bridges can supply the KL half, but are not consumed by this final export. Do not treat `.toReal` as an unconditional replacement for extended KL without finiteness.

No countable Sigma-prefix/geometric mixture, truncation convergence, countable KL passage, bounded-payoff TV inequality, model stability or final Q-learning theorem is established here. Actual production import/build/axiom evidence and separate countable/measure consumption review remain necessary. Stale uncompiled comments in the author files are documentation cleanup, not proof gaps; the exact staged supported finite theorem is independently verified within the stated scope.

## Production integration

The reviewed supported finite-vector Pinsker proof chain is integrated as the corresponding `Formalization/ModelFree/QLearning*Pinsker*.lean` modules. Countable and actual-measure stability applications remain separate. Declaration and proof bodies match the reviewed staged sources; imports and status comments were updated where needed. The full project check compiled 283 modules and audited 3,694 project declarations, allowing only `propext`, `Classical.choice`, and `Quot.sound`.
