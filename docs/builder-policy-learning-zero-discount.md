# Model-based policy learning at zero discount

`.local/PolicyLearningZeroDiscount.lean` proves an exact boundary-case guarantee for the reviewed generative-model policy-learning estimator. For every admissible finite MDP with `γ=0`, every positive sample size, and every sample outcome, its empirically optimal greedy policy has exactly the true optimal trajectory V and Q at every state and state-action pair. The joint zero-loss event has probability one under the actual product law of the model's independent state-action transition samples. This is staged proof evidence pending independent review and integration; it is **not** the general source sample-complexity theorem.

The source permits `γ∈[0,1)` (prelim lines 31–45), defines trajectory Q using the forced initial action and V as actual expected discounted return (prelim lines 90–123), and constructs the empirical-model deterministic optimal policy from N samples per state-action pair (model-based chapter lines 814–865). The general policy-learning theorem is at lines 898–922. In particular, no lower bound on γ excludes zero.

The proof does not assume near optimality or sample accuracy. `trajectoryQ_zero_discount` uses the true trajectory/Bellman bridge to show every policy's actual forced-action Q equals the immediate reward. `optimalQ_zero_discount` derives the same reward table for the optimality fixed point, and `greedy_reward_zero_discount` shows each optimal greedy action maximizes immediate reward. The empirical model copies the true known reward and discount, so its greedy action also maximizes the true reward regardless of samples. The actual true-trajectory value of the resulting deterministic point-mass policy equals that of the true optimal greedy policy; all first-action Q values equal those of the true optimal policy, including actions outside policy support. `policyEstimator_loss_zero_discount` proves both full finite sup-norm losses equal zero for every outcome. `policyEstimator_success_zero_discount` identifies the joint zero-loss event with the entire sample space and establishes probability exactly one using the true product `samplingLaw`.

The result covers the explicit greedy selector provided by the reviewed algorithm construction and compares it with the existing true optimal greedy policy, which dominates stationary randomized policies. It neither asserts performance for positive γ nor certifies the source's universal sample-complexity theorem, its N-dependent logarithm, or all empirical optimizer selectors. Independent review and integrated-export compilation/axiom inspection remain pending.

Validation: `bash scripts/lean-local.sh .local/PolicyLearningZeroDiscount.lean` compiled cleanly against the integrated policy-learning dependency. An exact temporary source copy with seven appended axiom inspections compiled and was deleted. The two trajectory Q identities, reward maximality, true Q and V equalities, zero-loss and probability-one results depend only on `propext`, `Classical.choice`, and `Quot.sound`. Compiler use was coordinated within the two-compiler limit.

SHA-256:

- `.local/PolicyLearningZeroDiscount.lean`: `b75ba66b5c4d4c2be3cb8b2978f1ea9b74afa4f10b4b078b7d51a209f7c6be3e`.
- `Formalization/Generative/ModelBasedPolicyLearning.lean`: `6f568330fd0744f11c0e965e5e3fd884dac5fd579965bbe4d7918f571e8c4f8c`.
- `source/upstream/tex/chapters/generative_model_model_based.tex`: `b7e7abfb2c2cb2c0dd82470db5ecac3a67d7163682246d499935d9130214ac4d`.
- `source/upstream/tex/chapters/prelim.tex`: `2d27bb720d49020ce1d3ea362b1678a90c6208882accca90fef21c25e42031a5`.
