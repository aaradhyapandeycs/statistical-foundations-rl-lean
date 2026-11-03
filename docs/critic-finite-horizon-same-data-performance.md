# Independent source review: same-data evaluation and all-stage performance

Reviewed staged sources:

- `.local/FiniteHorizonPolicyEvaluationConsumption.lean`, SHA-256 `4c120da0a7d740cf246a93b9fb83b79be99ea4a4bf0dd8b721ea4a8fe0521db0`.
- `.local/FiniteHorizonPolicyPerformanceConsumption.lean`, SHA-256 `5bd1ee322f9bd8e4fee1df4e5751ef8aada73f7c5f7b64aa477e5935b5d7288c`.

This review is source-only; no compiler slot was allocated and no builder handoff for these files was present in `docs/` at review time.

## Same-data evaluation consumption

`policyTrajectorySuffix` and `policyTrajectoryQSuffix` are actual trajectory expectations for the controlled suffix environment, with the policy time-indexed by the original stage offset. The true auxiliary level-zero identity rewrites `controlled (drop h)` to the same suffix semantics. The empirical level-zero identity uses the paired empirical/true stages from the same `data`, proves reward equality for each pair by construction, and invokes the comparison auxiliary level-zero trajectory identity. No independent empirical sample or changed reward model is inserted.

`allLevelBernsteinEvent_policyEvaluation` consumes the recursive residual conclusion from the all-level bridge for the same `data`, branch `b`, and stage offset `h`; it then rewrites paired list projections to the actual empirical stages and `List.ofFn E`. The event's all-state norm therefore gives a pointwise same-data trajectory evaluation bound. The probability wrapper is under `samplingLaw E N` and merely maps the already-proved common event into this evaluation predicate; it does not spend confidence a second time.

The evaluation theorem retains the explicit safe radius `6 H sqrt(3 β H/N)` and sample condition `12 H β < N`, with `β = allLevelBeta`. It claims both Bool-indexed event branches simultaneously. In the performance application, the fixed branch is instantiated with the data-independent true backward-greedy policy, and the fitted branch with the concrete empirical backward-greedy policy computed from that exact data.

## True benchmark, suffix indices, and forced-action Q

`policyTrajectorySuffix_le_optimal` is the ordinary finite-horizon optimal-control domination for any deterministic nonstationary policy on the same suffix. `backwardGreedyActions_policyTrajectorySuffix` identifies the canonical backward-greedy policy's value with `EnvironmentStage.optimalValue` on every suffix, including empty suffixes. Its proof aligns the policy time offset after dropping `h` stages.

The V comparison uses the true optimal policy `fixed` and the empirical backward-greedy policy `f`. On a single data outcome, the empirical value of `fixed` is no greater than the empirical optimum, while the two true-versus-empirical evaluation errors are each at most `r`. This yields the true benchmark gap at most `2r`; nonnegativity comes from optimality of the true benchmark over `f`. No event uniform over arbitrary policies is needed: the common event was built for the fixed true-optimal policy and the selected fitted policy branch, and the fitted continuation theorem establishes its future-data measurability.

For Q, `policyTrajectoryQSuffix` uses `DecisionStage.trajectoryQ` in the controlled suffix MDP, so its first action is forced and subsequent actions follow `f`. The helper `policyTrajectoryQSuffix_loss_le_of_values` expands both optimal and policy Q backups, cancels their common immediate reward, and writes the Q gap as the true transition expectation of the next-suffix V gap. Its all-`h` V premise supplies that next-suffix bound at `h+1`; transition expectation preserves it. The empty-suffix case is handled separately with both Q values zero. The helper also establishes nonnegative Q loss by optimal Q dominance.

The final event states both V and forced-first-action Q inequalities for every natural `h`, every state, and every action. For `h ≥ H`, suffixes are empty and the bounds are trivial; this is a valid strengthening of the usual finite stage range. The probability result uses the same common all-level event under the actual sampling law, preserving strict `1−δ < probability` and the radius `12 H sqrt(3 β H/N)`.

## Scope

The source gives a conditional explicit sample-size/radius guarantee for the concrete causal backward-greedy planner. It does not yet convert `β` and the strict sample-size premise into the monograph's stated ε/sample-count form or absorb the safe logarithm into the printed universal constant. The note does not claim compilation or axiom closure.

**Verdict:** source semantics align across common event, same-data evaluation, suffix indexing, true optimal benchmark, empirical fitted selector, and forced-first-action Q. No policy/sample independence assertion is used. No substantive source mismatch found in these two staged files.

## Re-review of compiler-repaired sources

Re-reviewed exact current sources:

- `.local/FiniteHorizonPolicyEvaluationConsumption.lean`, SHA-256 `29b807936570572f45a3f602e6d5162aba7cbf64108c445a0705b4bc900e5524`.
- `.local/FiniteHorizonPolicyPerformanceConsumption.lean`, SHA-256 `47b69c27754f119d410a7d20cd8c5742343d1596f1dfa178ab3bac48f5569536`.

Compared with the previously reviewed hashes in this note, the evaluation file only changes the proof closing the paired-list length bound: it now explicitly finishes the `simp` result with `le_rfl`. In the performance file, `rw [hd] at he` makes the current cons-stage equation explicit before rewriting the Q identity, and `dsimp only` unfolds the local `let f` before introducing the suffix-stage quantifier. These are proof/elaboration repairs; theorem statements, definitions, event/data quantifiers, constants, policy choices, and suffix/Q meanings are unchanged. The semantic review above applies to these changes as well.

Both exact files compiled independently, in order, into `.local/finite-horizon-policy-consumption-fresh-audit/`, using the already-built staged Bernstein bridge and existing pinned project/Mathlib artifacts. The 12-export `#print axioms` probe completed without errors; every export reports only `[propext, Classical.choice, Quot.sound]`. No `sorryAx` was present. This verifies these two staged modules against the previously reviewed staged bridge; it is not a production integration or source-theorem sample-complexity claim.

Production integration: production bodies match the independently reviewed sources, with qualified imports. The full project export compiled and audited 2,565 declarations, allowing only `propext`, `Classical.choice`, and `Quot.sound`.
