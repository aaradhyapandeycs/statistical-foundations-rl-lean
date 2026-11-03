# Staged one-state policy-learning experiment

`.local/OneStatePolicyExperiment.lean` gives a single deterministic, jointly measurable reward-greedy policy estimator for the existing actual one-sample-per-row one-state generative experiment. For every admissible model and every data value it has exactly zero full-array Q loss against the actual trajectory-optimal greedy policy. It composes this with the positive-constant parameter feasibility statement, obtaining the explicit estimator/model quantifier order for the one-state candidate obstruction to Theorem 3.7(i). This is staged proof evidence pending independent source/statement review and integration, not an author-approved correction or a claim of a reviewed full theorem refutation.

## Source and experiment

The source assumes a known reward function on a common finite action set and independent generative transition samples (`prelim.tex:31–45`, `generative_model_model_based.tex:15–31`), defines trajectory Q with the first action forced (`prelim.tex:114–123`), and states Theorem `theorem:azar` at model-based lines 1438–1464. The earlier policy-learning section assumes at least two actions; the staged construction fixes `S=1`, `A=16`, `γ=2/3`, `N=1`, so it satisfies that condition and `SA≥16`.

The imported `.local/OneStateExperiment.lean` constructs `oneStateGenerativeLaw` as the actual finite product of the MDP transition row laws indexed by `(state, action, sample-index)`, with a singleton sample-index carrier. Its checked declarations establish the probability law, each true row marginal and mutual independence across all sample coordinates. `oneStateExampleMDP` witnesses an inhabited admissible model class. This policy module reuses that same law; it does not assume a zero failure event or substitute an arbitrary sample measure.

## Selector, actual Q, and quantifiers

`rewardMaximizers` is the actual finite set of maximizing actions; `rewardMaximizers_nonempty` proves it is nonempty. `measurableRewardGreedy` chooses its smallest action index, making ties deterministic. `measurableRewardGreedy_max` proves it attains the maximum, while `measurableRewardGreedy_eq_iff` describes its exact selection event as “this action is maximal and no smaller action is maximal.” `measurableRewardGreedy_measurable` uses that characterization, finite intersections and Borel measurable comparisons. Thus no measurability of an opaque arbitrary maximizer is assumed.

`oneStatePolicyEstimator` takes the known reward table, discount and data and returns a deterministic stationary action map. It uses only the reward table and ignores the other inputs. `oneStatePolicyEstimator_joint_measurable` proves joint measurability in all three observable inputs. For actual evaluation, each chosen action is encoded as the corresponding point-mass stationary policy; the first Q action remains forced separately by the trajectory law.

`oneStatePolicyEstimator_actualQ` proves this output policy's actual infinite-trajectory Q equals that of `M.optimalGreedyPolicy` for every admissible model, data value, state and first action. It uses the already proved one-state Bellman formula, its own maximal-reward proof, the policy fixed-point uniqueness characterization, and the forced-action trajectory bridge; it does not assume the desired equality. The imported optimal-trajectory result establishes the target policy's simultaneous dominance over every stationary randomized policy. `oneStatePolicyEstimator_loss` proves the sup norm of the full Q-array difference is zero for **every** sample outcome; `oneStatePolicyEstimator_failure` proves the actual product law assigns zero probability to the source's strict-loss event for every `ε≥0`.

The final `oneState_theorem37_i_obstruction` formalizes this order:

```text
∀ c > 0, ∃ ε > 0,
  [strict source accuracy, discount bounds, SA≥16, and N=1 sample bound] ∧
  [∃ an admissible MDP with discount 2/3] ∧
  ∃ one jointly measurable deterministic stationary policy estimator,
    ∀ admissible MDPs M with discount 2/3,
      [∀ data, ‖Q^(estimated policy)−Q*‖∞ = 0] ∧
      [P_M(‖Q^(estimated policy)−Q*‖∞ > ε) < 1/4].
```

The estimator is chosen once, before the universal model quantifier; it receives each model's known reward table as allowed input. The same fixed estimator covers ties and varying rewards. The feasibility conjunct uses the previously reviewed `oneState_theorem37_hypotheses_feasible`, and the model witness is explicit. The Lean output policy class is deterministic stationary; the comparison target is optimal over the project's stationary randomized policies. No nonstationary-policy-class assertion is made here.

## Verification and integration boundary

The exact staged source was copied to a temporary probe and compiled with nine appended `#print axioms` commands, using `.local/lean` and the project/package search path plus `.local` at the front. The imported `OneStateExperiment.olean` was compiled from its exact staged source, itself importing the exact staged `OneStateTrajectory.olean`. All nine checked declarations (`rewardMaximizers_nonempty`, `measurableRewardGreedy_max`, `measurableRewardGreedy_eq_iff`, `measurableRewardGreedy_measurable`, `oneStatePolicyEstimator_joint_measurable`, `oneStatePolicyEstimator_actualQ`, `oneStatePolicyEstimator_loss`, `oneStatePolicyEstimator_failure`, and `oneState_theorem37_i_obstruction`) depend only on `propext`, `Classical.choice`, and `Quot.sound`. The source compile was clean.

The local import currently reads `import OneStateExperiment`; after independent review and integration of the dependency, it must be changed to its actual project module path, then the integration diff reviewed and the affected project built and axioms rechecked. This staged result does not settle the author's intent, the full paper scope, or completion of the published theorem formalization.

SHA-256:

- `.local/OneStatePolicyExperiment.lean`: `ac9fd551a5fb69f537745ec4b89874e52fa26649deed2e8e583f556146046fd3`.
- `.local/OneStateExperiment.lean`: `e7b4220fab2b6495905667e1530e1f32d2e8ce564ac7bdc31f0299cf088ecc8f`.
- `.local/OneStateTrajectory.lean`: `091d881d496d1709115cb088a749d708633513c45bf84154ac534c93a02133d1`.
- `Formalization/Obstructions/OneStateParameters.lean`: `2be78dda039c300ebcc4455658994b8b0495c7f5da6ef31c1db20fb27b1586ba`.
- Source `prelim.tex`: `2d27bb720d49020ce1d3ea362b1678a90c6208882accca90fef21c25e42031a5`.
- Source `generative_model_model_based.tex`: `b7e7abfb2c2cb2c0dd82470db5ecac3a67d7163682246d499935d9130214ac4d`.
