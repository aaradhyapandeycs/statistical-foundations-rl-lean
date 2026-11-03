# Infinite optimal trajectory values: builder handoff

Source: `source/upstream/tex/chapters/prelim.tex` lines 114–140 and 233–245,
`eq:optimal-Vstar-Q-star-defn` and `eq:bellman_fix_point`; SHA-256
`2d27bb720d49020ce1d3ea362b1678a90c6208882accca90fef21c25e42031a5`.
Staged implementation: `.local/OptimalTrajectoryValue.lean`, SHA-256
`d3fbac88b1bec5e29ad93e9432d6a491f72fb3d9ada243f3a954950b47af21d7`.

`optimalGreedyAction` chooses an attained maximizer of the already constructed
optimality Bellman fixed point at every state, and `optimalGreedyPolicy`
encodes this deterministic stationary action rule by point masses. It does not
assume an optimal policy exists. `qBellman_optimalGreedy` proves that the
optimality solution is a fixed point of this concrete policy's Bellman
operator; uniqueness then gives `policyFixedPoint_optimalGreedy`.

For an arbitrary stationary randomized policy, `qBellman_monotone` proves
order preservation and `qBellman_optimal_le` proves the optimality solution
is an upper bound on its policy backup. Iterating the policy backup from that
upper bound, then using the already-proved contraction limit, yields
`policyFixedPoint_le_optimal` at **every** state/action. The reviewed
`ForcedPrefixBridge` identifies each actual forced-action infinite-trajectory
Q with its policy fixed point, including actions with zero policy mass.
Consequently `optimalGreedy_trajectoryQ` proves the greedy policy's actual
trajectory Q equals the optimality Bellman fixed point and
`trajectoryQ_le_optimalGreedy` proves it dominates every represented
stationary randomized policy at every state and forced first action.

`trajectoryValue_le_optimalGreedy` applies the independently established
trajectory V–Q policy-average identity and the actual greedy maximizer to
prove simultaneous state-value domination. The final theorem
`exists_stationary_trajectory_optimal` packages a **single** deterministic
stationary action rule whose point-mass policy dominates every stationary
randomized competitor in both actual V and Q at all states/actions; the
existential witness precedes all competitor and query quantifiers.

Policy scope is exactly the project's `StationaryPolicy State Action`:
state-dependent randomized stationary Markov rules. This file does not compare
history-dependent or nonstationary infinite-horizon policies, introduce a
statistical estimation experiment, or establish Theorem 3.7's minimax lower
bound. The source's discounted-policy section explicitly uses stationary
policies. No source policy, maximizer, Bellman equation or trajectory
identification is added as an assumption.

Validation: `bash scripts/lean-local.sh .local/OptimalTrajectoryValue.lean`
passed. A temporary copy of the exact staged source with eight `#print axioms`
commands compiled with the same wrapper. `optimalGreedyAction_max`,
`qBellman_optimalGreedy`, `policyFixedPoint_optimalGreedy`,
`policyFixedPoint_le_optimal`, `optimalGreedy_trajectoryQ`,
`trajectoryQ_le_optimalGreedy`, `trajectoryValue_le_optimalGreedy`, and
`exists_stationary_trajectory_optimal` used only `propext`,
`Classical.choice`, and `Quot.sound`. The temporary probe was removed.
`Formalization/MDP/ForcedPrefixBridge.lean` was compiled to its project-owned
olean using the repository wrapper at the lead's explicit request. Independent
review, export/facade integration and a whole-project build remain.

Dependency hashes:

- `Formalization/MDP/ForcedPrefixBridge.lean`: `f8b1e459e311c7dfc914f13bd70f9129931bf7b6e3d79b7d2b6d69fe2bc50e3a`
- `Formalization/MDP/FiniteOptimal.lean`: `abd23ed8206032df152160f50d838d91bf99a169a09bbf2612bc5e9608494e85`
- `Formalization/MDP/FixedPoint.lean`: `b7c7b6338d1ec5005942e3b0f80676ed8e0e2dfb650a2cb01638642fe65f642e`
