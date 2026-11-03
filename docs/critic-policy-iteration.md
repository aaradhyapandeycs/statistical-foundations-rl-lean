# Independent policy-iteration review

Reviewed 2026-11-02, independently of the builder. Verdict: **PASS for the policy-iteration part of the source linear-convergence lemma, including arbitrary maximizing ties and actual trajectory Q-values.** Finite optimal-value attainment and eventual stabilization for the fixed tie rule are sound additional results. This is an ordinary source/semantic review, not author approval or a frozen-manifest certification. Integration and validation of production exports remain the lead’s responsibility.

## Stable identities and reconstructed source

- `.local/PolicyIteration.lean`: SHA-256 `4114f17b1942d8a355fd11d3ed118603e37902ab3c10e4670514e2feb4883228`.
- `Formalization/MDP/OptimalTrajectoryValue.lean`: SHA-256 `d3fbac88b1bec5e29ad93e9432d6a491f72fb3d9ada243f3a954950b47af21d7`.
- `source/upstream/tex/chapters/prelim.tex`: SHA-256 `2d27bb720d49020ce1d3ea362b1678a90c6208882accca90fef21c25e42031a5`.

Source lines 324–331, `eq:policy_iteration`, update `π_k(s)` to any maximizer of `Q^{π_{k−1}}(s,·)`. Lines 339–343 state `‖Q_k−Q*‖∞ ≤ γ^k ‖Q_0−Q*‖∞` for every `k ≥ 1`, with `Q_k = Q^{π_k}`. The PI proof is omitted in the source (line 354), so substantive proof construction is required. The present statement additionally permits index zero, where the bound is equality. Source lines 66–76 define the stationary randomized policy carrier; lines 136–141 define `Q*` via a simultaneously optimal deterministic stationary policy. This module uses precisely that policy class and identifies an actual optimal greedy policy.

## Binder audit

Primary source-facing target: `StatisticalRL.DiscountedMDP.arbitraryGreedyTrajectoryPolicyIteration_error`. The finite-attainment target has the same inputs except the iteration index. Expanded meaning-carrying model and policy fields are listed explicitly; no desired rate, improvement, convergence, or tail result is an input.

| Binder or expanded field | Bin | Source correspondence |
|---|---|---|
| `State : Type*` | TYPING | state carrier |
| `Action : Type*` | TYPING | action carrier |
| `[Fintype State]` | STANDING | finite source state space |
| `[Fintype Action]` | STANDING | finite source action space |
| `M : DiscountedMDP State Action` | TYPING | model record |
| `M.state_nonempty` | STANDING | nonempty source state set |
| `M.action_nonempty` | STANDING | nonempty source action set |
| `M.transition` underlying mass functions | STANDING | source transition kernel |
| transition `prob_nonneg` fields | STANDING | nonnegative transition probabilities |
| transition `sum_prob` fields | STANDING | normalized transition probabilities |
| `M.reward` | STANDING | source reward function |
| `M.reward_nonneg` | STANDING | source rewards in `[0,1]` |
| `M.reward_le_one` | STANDING | source rewards in `[0,1]` |
| `M.discount` | STANDING | source `γ` |
| `M.discount_nonneg` | STANDING | source `0 ≤ γ` |
| `M.discount_lt_one` | STANDING | source `γ < 1` |
| `π : ℕ → StationaryPolicy State Action`, underlying action masses | SOURCE | iteration sequence with arbitrary initial randomized stationary policy |
| each policy’s `prob_nonneg` fields | TYPING | probability-valued policy carrier |
| each policy’s `sum_prob` fields | TYPING | probability-valued policy carrier |
| `f : ℕ → State → Action` | SOURCE | chosen maximizing action at every update |
| `hupdate` | SOURCE | exact deterministic greedy policy update, source line 329 |
| `hmax` | SOURCE | selected action attains the current actual Q maximum, source line 329 |
| `n : ℕ` | SOURCE | source iteration index, extended validly to zero |

Counts (expanded table rows): SOURCE 5, STANDING 13, TYPING 5, RULED 0, EXCESS 0. The `Nonempty Action` instance introduced inside `hmax` comes from the model’s recorded nonemptiness; it is not an additional maximization hypothesis. In auxiliary `policy_error_of_greedy_backup`, the backup-equality premise is conditional infrastructure. The final source theorem proves and supplies that equality from the actual update and maximizing-selector hypotheses, so the condition is not smuggled into the result.

## Mathematical and semantic checks

`policyIteration` evaluates each policy through its genuine Q Bellman fixed point and selects a maximizer for the next policy. `greedyActionFor` uses a proved finite maximum existence result, not a placeholder selector. `greedyImprove` returns point-mass action distributions. Its body is the stated source algorithm. The chosen tie rule is fixed as a function of Q. Separate arbitrary-selector theorems quantify over an unrestricted `f n s`, so tie choices can vary by state and iteration without a common tie-breaking order.

Policy improvement is proved by monotone policy-evaluation iteration and passage to the proved limit. The improved policy’s fixed point dominates one optimality backup of the old Q, while every policy value is bounded above by the optimality fixed point. These componentwise inequalities bound the new sup-norm error by the optimality-backup error. The proved `γ` contraction then yields the one-step rate; induction gives exactly `γ^n`, with no extra prefactor or shifted exponent. Sup norms on finite function spaces coincide with the source entrywise maximum norm. `γ = 0` is included: after one update Q is already optimal, and the index-zero `0^0` convention yields the identity bound.

The trajectory conclusion is substantive. `trajectoryExpectedQ` is the integral of the actual infinite discounted reward series under `forcedActionTrajectoryLaw`. That law forces only the first action and uses the original policy thereafter. It is meaningful for actions with zero probability under the policy, so no conditional-on-null-event gap remains. The imported `ForcedPrefixBridge.trajectoryExpectedQ_eq_policyFixedPoint` proves the equality via finite-prefix laws, actual partial-return expectations, and convergence of dominated integrals. `OptimalTrajectoryValue.policyFixedPoint_optimalGreedy` proves that the explicitly constructed optimal policy has the optimality fixed point, and the same module proves its domination over all stationary randomized policies. Thus both sides of the exported rate are actual source Q-values, not arbitrary fixed-point surrogates.

Finite optimal attainment is correctly separated from policy identity. After the first iteration, every policy is deterministic, so the set of evaluated Q-functions is finite. The exact rate implies convergence to Q*. The finite image is closed, hence contains its limit, giving an actual finite index with Q = Q*. This argument admits arbitrary varying maximizing ties and does not assert that the policy sequence itself stabilizes. Arbitrary ties can cycle among distinct optimal policies. The separate concrete sequence uses the same fixed maximum chooser as `optimalGreedyPolicy`; once optimal Q is attained, the next greedy improvement is that policy, and all later policies equal it. The proof establishes this by exact equality of the choice expressions after rewriting Q = Q*, rather than by assuming uniqueness of the maximizing action.

The limit step uses actual convergent policy evaluation and finite-image closure. No unsupported interchange of maxima and limits occurs. Finite termination here means finite attainment of optimal value, or eventual policy identity for the concrete fixed tie implementation. There is no quantitative iteration-count bound and no proof of a separate executable stopping test. Those are not claimed by the builder or by the source linear-rate statement.

## Independent validation

- `bash scripts/lean-local.sh .local/PolicyIteration.lean`: exit 0, no diagnostics.
- `bash scripts/lean-local.sh .local/PolicyCriticAxioms.lean`: exit 0, using an exact copied source with appended audit commands; temporary file deleted afterwards.

Thirteen transitive axiom checks passed: `greedyImprove_policyFixedPoint_ge`, `policy_error_of_greedy_backup`, `arbitraryGreedyPolicyIteration_error`, `arbitraryGreedyPolicyIteration_finite_optimal`, `arbitraryGreedyTrajectoryPolicyIteration_error`, `arbitraryGreedyTrajectoryPolicyIteration_finite_optimal`, `policyIteration_error`, `trajectoryPolicyIteration_error`, `policyIteration_monotone`, `tendsto_policyIteration`, `policyIteration_finite_optimal`, `policyIteration_optimal_persists`, and `policyIteration_eventually_optimalGreedy`. Every list contains exactly `propext`, `Classical.choice`, and `Quot.sound`; no custom axiom or placeholder was found. Validation used one compiler sequentially, coordinated with the other workers within the two-compiler cap. The staged source and imported trajectory bridge hashes were rechecked unchanged.

## Remaining limits

The staged file is not yet a production export. Its integration must preserve this reviewed content, compile the actual export, extend the production axiom audit, and record the source coverage accurately. This review covers the PI portion, not the separate VI portion or whole-monograph completion. No mathematical source gap was found for the reviewed PI rate. Definitions and standing infrastructure were inspected for the semantic path used here, but this review does not independently recertify every theorem in their modules or every source claim about MDPs.
