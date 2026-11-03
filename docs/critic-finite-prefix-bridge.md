# Independent source review: finite/infinite trajectory prefix bridge

## Source-first reconstruction

`prelim.tex` lines 66–73 and 89–102 describes a trajectory with fixed `s₀`,
stationary randomized action sampling `a_t ∼ π(·|s_t)` followed by
`s_{t+1} ∼ P(·|s_t,a_t)` for every time `t ≥ 0`. For any finite `n`, its first
`n` action/next-state pairs must have joint mass
`∏_{k<n} π(a_k|s_k)P(s_{k+1}|s_k,a_k)` with `s₀` the supplied state. The
zero-length path is the unique empty path with mass one. A valid bridge to the
existing `FinitePath State Action n` law must show equality of the **actual
mapped infinite probability measure** to the finite path probability law for
all `n`, with a demonstrably index-preserving path map, rather than assuming
one law is the other. It must preserve ordering, not reverse or omit a time
step. It must not require a positive probability of the realized path, a
Bellman equation or a fixed point.

An equality of all prefix laws is significant input for transferring finite
path payoffs, but the statement must be inspected to see which particular
expectation bridge or infinite-return consequence is actually proved; neither
source Q semantics nor a Bellman equation follows merely by naming this
bridge.

Source SHA-256: `2d27bb720d49020ce1d3ea362b1678a90c6208882accca90fef21c25e42031a5`.

## Findings

**Verdict: PASS for the all-length measure bridge from the actual fixed-state,
stationary infinite trajectory law to the project's independently defined
finite path law.** This is scoped to stationary stage lists and does not itself
prove a Bellman or Q result.

1. The imported `InfinitePrefix.lean` establishes the actual probability mass
   of any singleton history as the product of the correct action/transition
   factors. `historyMass_first_step` re-expresses that product by peeling the
   initial pair and starting its tail product at the state actually reached.
   `historyMass_eq_finitePathWeight` matches it to
   `DecisionStage.pathWeight` for a first stationary stage followed by a list
   whose stages all equal the same stationary model and policy. This is a
   proved mass identity, not an assumed coupling or a division by path mass.
2. `historyTail` shifts the history indices down by one. `historyToFinitePath`
   takes index zero as the path's first `(action,next-state)` and recursively
   applies that tail; `finitePathToHistory` supplies its inverse.
   `historyFinitePathEquiv` proves both compositions are identity. For
   `stages.length = n`, this history conversion handles **n+1** pairs because
   it represents a path for `stationaryStage :: stages`; this offset is
   explicit in its type and correctly removed in the outer `finitePrefix`.
3. `infiniteTrajectoryLaw_map_historyFinitePath` uses finite-space measure
   extensionality on singleton paths, the proved bijection, the actual cylinder
   probability identity and the project PMF bridge to establish equality of
   measures. `infiniteTrajectoryLaw_map_finitePrefix` then handles arbitrary
   stationary stage lists, with a separate empty-list case proving that the
   constant empty-path pushforward equals the normalized empty `trajectoryLaw`.
   Its nonempty branch maps the actual infinite law through the restriction
   and history/path encoding. `infiniteTrajectoryLaw_map_replicatePrefix`
   instantiates it for **every** `n : ℕ` with exactly `n` repeated copies of
   the model and policy; no `n>0`, path-support or extra equality hypothesis is
   needed.
4. `finitePrefix_cons_head` and `finitePrefix_cons_tail` show the first encoded
   pair equals coordinate zero and the encoded remainder is the finite prefix
   of the trajectory shifted by one. Together, recursively, they preserve
   every position and rule out a reversed history. Independent compiled
   examples confirm the empty prefix is `PUnit.unit` and the two-step prefix
   stores `(path 0).1`, `(path 0).2`, `(path 1).1`, `(path 1).2` in that order.
5. `hstage` on the more general list theorem is a structural requirement that
   every stage uses the same stationary model and policy represented by the
   infinite law; it is discharged in the source-facing `List.replicate n`
   theorem. State/action finiteness and the model/policy structures provide
   actual normalized probabilities. No desired prefix equality, conditional
   probability, Bellman equation, or positive-mass condition is assumed.
6. The proved equality is a **measure** pushforward identity, strong enough to
   be used in a future integral transport proof. This file does not itself
   identify the discounted finite payoff integral with an infinite partial
   return, exchange a limit, establish the conditional shifted-tail law, or
   prove the V/Q Bellman equations. Those are separate consumers of this
   bridge, not claims established by it.

## Checks and identity

A copy of the exact stable staged source with the independent length-zero and
length-two probes and seven `#print axioms` commands compiled via
`bash scripts/lean-local.sh <temporary-probe>`.
Checked were `historyMass_first_step`, `historyMass_eq_finitePathWeight`,
`historyFinitePathEquiv`, `finitePrefix_cons_head`, `finitePrefix_cons_tail`,
`infiniteTrajectoryLaw_map_finitePrefix`, and
`infiniteTrajectoryLaw_map_replicatePrefix`; each used only `propext`,
`Classical.choice`, and `Quot.sound`. The temporary file was removed. This
checks the staged source and imported artifacts, not integrated facade/build
closure.

SHA-256:

- `.local/FinitePrefixBridge.lean`: `3ca9d38a8b1014054e83a318476b9fc4316573be5da3624cc20f70ccea87b6d7`
- `Formalization/MDP/InfinitePrefix.lean`: `c93faa5934f9ea745e44a2e3a175b3519ce3fa827b47ec60e8cf8311bce43c71`
- `Formalization/MDP/InfiniteTrajectory.lean`: `60c4f2c0279014ba54f6d0165e01d86ba407f2f72f93f4e9c493a6b8b86e33e9`
- `Formalization/MDP/FiniteTrajectory.lean`: `5b6f53bc1822729beb715ad385b74951dedf7c0596ca654cf246945593ca3130`
