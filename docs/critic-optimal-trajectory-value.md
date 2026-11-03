# Independent review: optimal stationary trajectory Q and V

**Verdict: PASS for existence and simultaneous optimality over the represented class of stationary randomized policies, including forced first actions with zero policy probability.** The actual greedy trajectory Q equals the already constructed optimality Bellman fixed point. This is a scoped source/semantic review of the staged implementation and its cited bridges, not an author-approved frozen-declaration audit or a whole-paper certification.

The reviewer did not author `.local/OptimalTrajectoryValue.lean`. I authored part of its imported `PrefixValueBridge.lean`; that bridge has a separate independent source/axiom review in `docs/critic-prefix-value-bridge.md`. Its forced-action dependency has its own separate independent review in `docs/critic-forced-prefix-bridge.md`. The present review checks that the staged result actually consumes their trajectory-to-fixed-point conclusions.

## Source-first reconstruction and policy scope

`source/upstream/tex/chapters/prelim.tex:31–52` supplies the finite stationary MDP, nonempty carriers, normalized transition laws, reward in `[0,1]`, and `0 ≤ γ < 1`. Lines 63–74 define a **stationary randomized policy** as an action distribution at each state; line 76 says time-invariant policies are typically sufficient in the stationary infinite-horizon model. Lines 89–102 define `V^π(s)` as expectation of the actual infinite discounted trajectory return. Lines 114–123 define `Q^π(s,a)` with a fixed first action and π thereafter, for all state/action pairs; lines 123–128 state the policy average identity. Lines 136–140 state one deterministic optimal policy simultaneously maximizing both V and Q, and lines 233–245 state the optimal Q is the unique fixed point of `T Q = r + γ E_P max Q`.

The staged conclusion quantifies competitors as `StationaryPolicy State Action`, i.e. precisely the state-dependent stationary randomized Markov policies explicitly defined in that source subsection. It does **not** quantify over nonstationary or history-dependent infinite-horizon policies. If a broader policy class is later adopted for the phrase “optimal policy,” proving its equivalence or domination is a separate source obligation; this review does not silently enlarge the current result. The source writes a conditional expectation at the initial action; for a zero-probability action, the project's forced-action intervention is the well-defined continuation matching its prose, and is not claimed to equal every version of a conditional distribution on a null event.

## Model, construction, and quantifier audit

- `DiscountedMDP` expands to finite nonempty State/Action carriers, each genuine normalized nonnegative transition distribution, stationary reward and its `[0,1]` endpoints, and discount `0 ≤ γ < 1`. `StationaryPolicy` expands to a normalized action probability distribution for every state. No assumed existence of an optimal policy, maximizer, Bellman solution, comparison, support positivity, or trajectory identification is a theorem input.
- `optimalGreedyAction` (staged lines 20–30) chooses a maximizer of the *already proved unique* Bellman optimality fixed point over the actual finite nonempty action carrier. `optimalGreedyAction_max` proves this maximum is attained; `optimalGreedyPolicy` (32–34) is a point-mass stationary policy derived from that single action function.
- `qBellman_optimalGreedy` (36–52) proves that the constructed policy backup, evaluated at the optimality fixed point, equals the optimality backup there, because the greedy policy's expectation is the actual finite maximum. The existing Q-Bellman uniqueness theorem then gives `policyFixedPoint_optimalGreedy`. No source trajectory value is defined as a fixed point in this construction.
- For every stationary randomized π, `qBellman_monotone` uses nonnegative γ and normalized transition/policy expectations, and `qBellman_optimal_le` uses the bound of a policy average by the finite maximum. `policyFixedPoint_le_optimal` iterates the actual policy Bellman map from the optimality fixed point, preserving the upper bound, and takes its already proved contraction limit. This yields the inequality at every s and a with no policy-support or positive-transition assumption and no hypothesis that π is deterministic.
- `optimalGreedy_trajectoryQ` consumes the imported actual forced-trajectory-Q/fixed-point identification and the just-proved greedy fixed-point equality; `trajectoryQ_le_optimalGreedy` consumes the same identification for an arbitrary competitor and obtains actual-trajectory Q domination. The forced law takes the initial action as an intervention and then follows π, so the statement remains meaningful and valid when `π(a|s)=0`.
- `trajectoryValue_le_optimalGreedy` consumes the imported actual trajectory V–Q policy-average identity. It bounds the competitor's policy average by the optimal fixed-point maximum and identifies that maximum with the greedy policy's actual trajectory state value. It uses the **same** greedy policy for V and Q.
- The final `exists_stationary_trajectory_optimal` has quantifiers `∃ f : State → Action, ∀ π, ∀ s, ∀ a, Q^π(s,a) ≤ Q^{pointMass f}(s,a) ∧ V^π(s) ≤ V^{pointMass f}(s)`. The witness `f = M.optimalGreedyAction` is selected before π, s, and a, and depends only on the common MDP. It is a single deterministic stationary rule, not a different rule per queried state/action or rival policy. Both actual trajectory comparisons refer to the same MDP.

`optimalGreedy_trajectoryQ` identifies the genuine greedy trajectory Q with `optimalityFixedPoint`. Together with the latter's existing fixed-point equation and uniqueness this yields the source Bellman-optimality equation for the represented trajectory optimum. The file does not add a separately named project `Q*` abstraction; source naming/semantic export decisions remain a separate integration task.

## Independent checks and identity

A temporary copy of the exact staged source, with two additional examples, compiled using `bash scripts/lean-local.sh <temporary-file>` without diagnostics. The first example takes a competitor concentrated on action b with `a ≠ b`, proves its probability of a is zero, and still applies actual trajectory-Q domination at forced action a. The second independently composes greedy trajectory-Q attainment with `optimalityFixedPoint_spec` to obtain the optimal Bellman fixed-point equation for the actual greedy trajectory Q.

The same probe ran `#print axioms` for `optimalGreedyAction_max`, `qBellman_optimalGreedy`, `policyFixedPoint_optimalGreedy`, `policyFixedPoint_le_optimal`, `optimalGreedy_trajectoryQ`, `trajectoryQ_le_optimalGreedy`, `trajectoryValue_le_optimalGreedy`, and `exists_stationary_trajectory_optimal`; each reported only `propext`, `Classical.choice`, and `Quot.sound`. The temporary source was removed. This checks the staged declarations and imported project artifacts, not a future integrated export or full build.

Reviewed SHA-256 values:

| File | SHA-256 |
| --- | --- |
| `.local/OptimalTrajectoryValue.lean` | `d3fbac88b1bec5e29ad93e9432d6a491f72fb3d9ada243f3a954950b47af21d7` |
| `Formalization/MDP/ForcedPrefixBridge.lean` | `f8b1e459e311c7dfc914f13bd70f9129931bf7b6e3d79b7d2b6d69fe2bc50e3a` |
| `Formalization/MDP/ForcedActionReturn.lean` | `87f447460f55da6d49a7311a73d69537f934395d3fbadf9c7a88b0c0c4bca0c2` |
| `Formalization/MDP/ForcedActionTrajectory.lean` | `77fe3fbe10217a1e8a6476a3ed1ea978c698c1972dec82b769f427491a9d9346` |
| `Formalization/MDP/PrefixValueBridge.lean` | `bd286567aa059c3e5fb293f1943eb06bd2e3d79c8dc9484d8a73195a2db16e89` |
| `Formalization/MDP/FiniteOptimal.lean` | `abd23ed8206032df152160f50d838d91bf99a169a09bbf2612bc5e9608494e85` |
| `Formalization/MDP/FixedPoint.lean` | `b7c7b6338d1ec5005942e3b0f80676ed8e0e2dfb650a2cb01638642fe65f642e` |
| `Formalization/MDP/Basic.lean` | `ecf28ee04a78405be352f5453d957f34a7883d33304b21255a9f7f444e0bc088` |
| `source/upstream/tex/chapters/prelim.tex` | `2d27bb720d49020ce1d3ea362b1678a90c6208882accca90fef21c25e42031a5` |
