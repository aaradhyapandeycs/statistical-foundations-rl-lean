# One-state optimal Q on actual trajectories: staged handoff

The staged module `.local/OneStateTrajectory.lean` composes the earlier one-state Bellman identity with the actual infinite forced-first-action trajectory and optimal-policy bridges. It defines one estimator solely from the known reward table and discount, ignoring an arbitrary data value. It proves pointwise exactness, zero sup-norm error, and zero mass for the strict-error event under any data measure, uniformly for every admissible one-state MDP sharing those known inputs. This is a substantive uniform obstruction, not a formalized complete generative-sampling minimax refutation or author-approved correction.

The source requires known rewards and discount and defines Q by forced first action followed by the policy (`source/upstream/tex/chapters/prelim.tex:31–45,114–123`; generative samples in `generative_model_model_based.tex:15–31`; theorem `theorem:azar`, 1438–1464). The construction works for finite State and Action, `[Subsingleton State]`, and `[Nonempty Action]`; State may technically be empty, where statements are vacuous. The original S=1 case is included. The estimator is

```text
Qhat(r, γ, data)(s,a) = r(s,a) + γ max_b r(s,b)/(1−γ).
```

It contains no transition kernel and does not inspect `data`. The proof does not supply a guessed Bellman identity as an assumption.

## Exports and scope

All are in `StatisticalRL.Obstructions`:

- `oneState_trajectoryOptimalQ`: the actual infinite forced-action Q of the explicitly constructed optimal greedy stationary policy is the previously proved one-state formula.
- `oneState_trajectoryQ_le`: every stationary randomized policy's actual infinite Q is bounded pointwise by that same formula. Together with attainment, this identifies the trajectory optimum over the formalized stationary policy class.
- `oneState_rewardGreedy_trajectoryQ`: the reward-maximizing one-state policy itself attains that Q on actual trajectories, using `trajectoryExpectedQ_eq_policyFixedPoint` and `greedy_policyFixedPoint_eq_optimalityFixedPoint`.
- `oneStateKnownRewardEstimator_exact`: for arbitrary known `(reward,discount)`, every MDP with matching inputs, every data value and all state-action inputs, the **same** known-reward estimator equals actual optimal-greedy trajectory Q.
- `oneStateKnownRewardEstimator_norm_error`: the finite sup-norm of the full Q-array error is identically zero on each data value.
- `oneStateKnownRewardEstimator_error_measure`: for any measurable data carrier, any measure (not even necessarily a probability measure) and `ε≥0`, the strict-error event is empty and has mass zero. This avoids adding any assumptions about the data-generating law and is stronger than a fixed-law event calculation.

The MDP appearing in the optimum is used to state the target trajectory law, not as an input to the estimator. Transition-dependent greedy policy selection in the characterization likewise is not an estimator input; reward greedy attainment is proved separately. Arbitrary data carriers cover all finite sample vectors once a concrete experiment is supplied.

## Remaining boundary

The current exports quantify the MDP and data value (or data measure) but do not define the original theorem's full joint statistical experiment, the full parameter/carrier-size quantifiers, or a minimax theorem/refutation in Lean. No nonstationary/history-dependent policy optimality claim is made. The original theorem, its assumptions, and the proposed correction remain source/audit matters. An independent source/statement/code/axiom review and integration build are required before landing.

## Focused verification and identity

The exact staged source, copied unchanged to a temporary probe with six appended `#print axioms` commands, compiled cleanly with `bash scripts/lean-local.sh` against the built project imports. Each of the six exports listed above reported only `propext`, `Classical.choice`, and `Quot.sound`. This checks the exact staged source, not an integrated project build.

SHA-256 identities:

- `.local/OneStateTrajectory.lean`: `091d881d496d1709115cb088a749d708633513c45bf84154ac534c93a02133d1`.
- `Formalization/Obstructions/OneState.lean`: `87db477c4dbcb5badbdbbdbbe438cfea4ff3a64b513ea332da33a62b325f072e`.
- `Formalization/MDP/OptimalTrajectoryValue.lean`: `d3fbac88b1bec5e29ad93e9432d6a491f72fb3d9ada243f3a954950b47af21d7`.
- `Formalization/MDP/ForcedPrefixBridge.lean`: `f8b1e459e311c7dfc914f13bd70f9129931bf7b6e3d79b7d2b6d69fe2bc50e3a`.
