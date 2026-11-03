# Full-episode occupancy bridge builder handoff

Source: `source/upstream/tex/chapters/prelim.tex`, lines 749–774,
`eq:dh-pi-defn` and `eq:dhstar-finite`; source SHA-256
`2d27bb720d49020ce1d3ea362b1678a90c6208882accca90fef21c25e42031a5`.
Implementation: `Formalization/MDP/OccupancyBridge.lean`, SHA-256
`e7c5519936dc6209640ab82da2aff2991bf71f2ee54f5f29d275ba11cd5a9ab5`.

`pathState` and `pathAction` project the state before the action and the action
at index `i : Fin H` directly from one complete `trajectoryLaw stages` path.
`fullPath_state_expectation` and `fullPath_joint_expectation` prove, for
arbitrary real test functions, that full-path expectations agree with the
normalized recursively propagated state law and its current policy, thereby
marginalizing every later stage. `stateOccupancy_eq_fullPath` and
`stateActionOccupancy_eq_fullPath` apply those statements to state and joint
event indicators. The initial distribution is genuinely mixed in as an outer
expectation. These results cover first and last stages and impose no positivity
of individual event probabilities. `Fin 0` is empty, so no decision is invented
when the horizon is zero.

`greedyIndex` preserves the source index through the length-preserving greedy
stage construction. `greedyActionAt` is the existing finite-horizon optimal
action, selected from the environment's current action backup and its optimal
continuation. `greedyStages_policy_at` identifies the policy of the constructed
stage list with its point mass, and `greedy_stateActionOccupancy` derives the
source's deterministic indicator formula for the same optimal stage sequence.
Optimality of that sequence against all randomized policies is established in
`FiniteOptimal.lean` (`greedy_suffix_dominates`), rather than assumed here.

A focused `bash scripts/lean-local.sh Formalization/MDP/OccupancyBridge.lean`
compile passed before a final warning-only proof cleanup. A temporary copy of
the final exact file, with axiom commands appended, then compiled using the
same wrapper. The six checked declarations `fullPath_state_expectation`,
`fullPath_joint_expectation`, `stateOccupancy_eq_fullPath`,
`stateActionOccupancy_eq_fullPath`, `greedyStages_policy_at`, and
`greedy_stateActionOccupancy` used only `propext`, `Classical.choice`, and
`Quot.sound`. The temporary probe was removed. Independent source review,
export/facade integration, and an integration build remain for the lead.

Dependency hashes: `FiniteOccupancy.lean`
`ad542b90fe2daeeaa93696f00fe763c7ca1e428042f769be7fd728c5657ab8d0`;
`FiniteOptimal.lean`
`abd23ed8206032df152160f50d838d91bf99a169a09bbf2612bc5e9608494e85`.
