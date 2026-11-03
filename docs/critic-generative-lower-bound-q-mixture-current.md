# Independent review: current one-row Q-mixture sources

This note reviews the exact source revisions below. The review is source-level; it is not a new Lean compile or axiom probe.

| Module | SHA-256 | Status |
|---|---|---|
| `.local/GenerativeLowerBoundQMixtureFamily.lean` | `ee3a2c7c954a4766095c8e61d036dd379ffd9dc3cb909ee6a935b5305a857b9c` | Source reviewed |
| `.local/GenerativeLowerBoundQMixtureOptimal.lean` | `7c6850bede8602249710bd29b726fdb39bb196ea96e0135a35a8f2ec35ad0cc1` | Repaired revision source reviewed |
| `.local/GenerativeLowerBoundQMixtureObservation.lean` | `47066c717bdf107546c95a8728c3793a03ead7f3b95c064ef7c3856afd3d7e48` | Draft source reviewed; uncompiled per handoff |

## Family and actual optimal Q

The family has exactly `m+1` states (`Option (Fin m)`) and `A` actions (`Fin A`). The baseline index `none` uses probability `p` in every active row; index `some (j,a)` changes only that row to `q`. The absorber has reward zero and deterministic self-loop, while active states have reward one and transition only to themselves or the absorber. All models share the same state/action types and satisfy the actual finite-MDP row construction. The hypotheses `0 ≤ p ≤ q < 1` and `0 ≤ γ < 1` suffice for the staged MDP.

The candidate Q formula correctly uses `qMixtureBestStay` in the continuation value: at the affected state in an alternative, the maximum row probability is `q`; at other active states, and throughout the baseline, it is `p`. The repaired `qMixtureStay_best_attained` proof explicitly witnesses a maximizing action in both cases, including when no changed row exists at that state. The action-maximum and Bellman fixed-point arguments match the actual row expectation. The bridge theorem then identifies the candidate with the actual optimal-greedy forced-first-action trajectory Q.

At the changed coordinate `(some j, a)`, the baseline forced-action Q is `1/(1−γp)` and the alternative Q is `1/(1−γq)`. The source-separation theorem applies the existing scalar parameter separation to these actual optimal trajectory Q values and claims strict difference `>2ε`, under `γ∈[2/3,1)` and `0<ε<1/(32(1−γ))`. This is baseline-to-one-alternative separation at its designated coordinate; it does not assert pairwise separation among alternatives. The repaired file is the only revision covered here: the earlier optimal-Q review hash `924c71f297b4233f50d21d21f095fd6f58334bfa3a4acd18fba126735f541b67` is stale and conveys no verdict on the current source.

The current builder handoff `docs/builder-generative-lower-bound-q-mixture-optimal.md` reports successful compilation of both exports and axiom inspection of the optimal trajectory-Q and strict-separation theorems with only `propext`, `Classical.choice`, and `Quot.sound`; it also reports three nonfatal linter warnings. Those are builder-reported results, not independently reproduced in this review. The family handoff `docs/builder-generative-lower-bound-q-mixture-family.md` still describes the candidate as unproved/unidentified and is stale relative to the optimal-Q handoff and current source.

## Actual observation law draft

The draft uses the production sample type `((Option (Fin m) × Fin n) × Fin N) → Option (Fin m)`. Its encoded coordinates are exactly active state/action/sample triples `((Fin m × Fin n) × Fin N)`. Each bit records whether that active row sample is a self-loop. The index-dependent parameter is `q` at the single selected row and `p` elsewhere, repeated over its `N` samples. This agrees with the family MDP transition definition and the production sampling law's independent coordinate/marginal interface.

The reconstruction fills absorber rows with `none` and active rows from their encoded bit. The draft separately proves the encoder/reconstruction left inverse, active-coordinate product law, full-array row support (including absorber coordinates), and the almost-everywhere equality needed to identify the full sample law as the encoded product pushed through the common reconstruction. Thus its intended law identity includes the deterministic absorber rows; it is not merely an active-coordinate marginal statement. The construction needs no `N>0` assumption and handles the empty product at `N=0`. It uses `[NeZero n]` for the true action set and no positive lower bound on `m`; these are consistent with the stated spaces.

The observation handoff `docs/builder-generative-lower-bound-q-mixture-observation.md` marks the draft uncompiled. No likelihood ratio, second-moment/χ² bound, testing inequality, estimator risk, measurability of a Q-estimator, or final lower-bound conclusion is proved by this observation module. Those remain separate proof obligations.

## Verdict and scope

The family and repaired actual-optimal-Q arguments are semantically consistent with the stated one-row family and source parameter separation. The observation draft's encoding, support, and common reconstruction match the actual sampling space and row laws on inspection. The Q-mixture packing plan still requires the statistical mixture argument and a common estimator/risk reduction; none should be inferred from the current source-law identity alone. This note makes no independent compilation claim.

Production integration: the corresponding production module bodies match the independently reviewed staged sources, with qualified imports. The full project export compiled and audited 2,522 declarations, permitting only `propext`, `Classical.choice`, and `Quot.sound`.
