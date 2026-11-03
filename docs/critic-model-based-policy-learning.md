# Independent review of staged model-based policy learning

Review date: 2026-11-02. Reviewed ordinary staged infrastructure, not a frozen declaration or completed source theorem. Only this report is owned by the reviewer.

## Identity and source reconstruction

The exact reviewed `.local/ModelBasedPolicyLearning.lean` SHA-256 is `6f568330fd0744f11c0e965e5e3fd884dac5fd579965bbe4d7918f571e8c4f8c`. Source `source/upstream/tex/chapters/generative_model_model_based.tex` SHA-256 is `b7e7abfb2c2cb2c0dd82470db5ecac3a67d7163682246d499935d9130214ac4d`. Relevant dependency hashes match the builder report: `EmpiricalRow.lean` is `6e87c90ff1150f7053845acff92d60a5c35035c7a78adcd394e0da5f3d9dc154`; `OptimalTrajectoryValue.lean` is `d3fbac88b1bec5e29ad93e9432d6a491f72fb3d9ada243f3a954950b47af21d7`.

I independently read the raw source algorithm at lines 814–865 and theorem at lines 898–922. The algorithm samples N next states per state-action pair from the true row, constructs relative frequencies, retains the known r and γ, and selects an optimal deterministic policy of that empirical MDP. The source does not prescribe a tie rule or require a particular planning implementation.

The separate theorem requires a universal positive c₀, all δ in (0,1), all ε in (0,1/(1−γ)], and the exact implicit sample bound N ≥ c₀ log(SAN/((1−γ)²εδ))/((1−γ)³ε²). Its conclusion is a single event of probability at least 1−δ on which all true-model state values lose at most ε and all true-model Q values lose at most γε, for any empirical optimal deterministic policy.

## Semantic findings

**The staged algorithm construction passes the reviewed scope. The sample-complexity theorem remains open.** No claimed statistical bound is hidden in the construction.

- `samplingLaw` is literally the finite product of the actual transition-row probability measures, with one coordinate for each `((s,a),i)`. The marginal theorem and full indexed independence theorem concern those coordinates under that law. This is a real experiment, not an arbitrary probability measure with assumed concentration.
- `empiricalRow` expands to `(N : ℝ)⁻¹ * ∑ i, if data ((s,a),i) = s' then 1 else 0`. Its positivity and normalization are proved in the dependency. The empirical-row expectation theorem is a deterministic frequency/sample-average identity, not a statistical deviation claim.
- `empiricalModel` replaces the transition field with these frequencies and copies reward, discount, and their standing bounds. It does not read the true transition in its body. Passing the ambient MDP is a convenient input package and does not supply an oracle transition to planning.
- `qEstimator` selects the optimal Bellman fixed point only after proved unique existence. Its equation is the real empirical reward-plus-discounted-expected-action-maximum equation; `qEstimator_unique` supplies uniqueness. There is no fallback or assumed Bellman certificate.
- `policyEstimator` chooses a maximizing action of that fixed point at each state. Classical choice specifies one deterministic mathematical function, including ties. Noncomputability is compatible with this mathematical algorithm specification; no executable planning complexity is claimed.
- All three data-output maps are measurable for each fixed M, N, hN. The sample domain is finite and carries the discrete product measurable structure. Consequently arbitrary tie selections on this domain are measurable; the proof is not illicitly asserting that arbitrary selections on a continuous parameter space are measurable.
- The value object is an integral of the actual summable infinite discounted reward under the Ionescu–Tulcea controlled path law. The Q object uses an actual forced-first-action path law, including actions of zero policy support. `qEstimator_eq_trajectory` consumes the proved trajectory/Bellman bridge, and empirical optimality compares actual trajectory values against every stationary randomized policy simultaneously, rather than comparing nominal fixed-point labels.

The comparator policy class is stationary randomized, matching the project's discounted stationary policy framework. This report does not extend that result to arbitrary history-dependent policies. The source algorithm's deterministic stationary optimizer is represented by the point-mass policy embedding.

## Binder and carrier check

The following expands all logical inputs used across the staged exports; repeated occurrences of the same binder in different exports have the same classification. None is a source-theorem sample-complexity premise smuggled into a theorem of that scope.

| Expanded input | Bin | Basis |
|---|---|---|
| State type | TYPING | Finite state carrier |
| Action type | TYPING | Finite action carrier |
| Fintype State | STANDING | Finite MDP setting |
| Fintype Action | STANDING | Finite MDP setting |
| M.state_nonempty | STANDING | Nonempty state set |
| M.action_nonempty | STANDING | Nonempty action set and genuine maximum |
| M.transition | STANDING | True probability transition rows |
| Each transition mass nonnegative | STANDING | Probability row definition |
| Each transition row sums to one | STANDING | Probability row definition |
| M.reward | STANDING | Known reward input |
| M.reward_nonneg | STANDING | Source reward normalization |
| M.reward_le_one | STANDING | Source reward normalization |
| M.discount | STANDING | Known discount input |
| M.discount_nonneg | STANDING | Discounted MDP convention |
| M.discount_lt_one | STANDING | Discounted MDP convention |
| N : ℕ | SOURCE | Algorithm sample count |
| hN : 0 < N | SOURCE | Positive sample count needed by source 1/N frequencies |
| data | TYPING | Observed sample coordinate function |
| coordinate i | TYPING | Coordinate marginal query |
| s | TYPING | State query |
| a | TYPING | Action query |
| V | TYPING | Test function in deterministic sample-average identity |
| Q | TYPING | Candidate in fixed-point uniqueness characterization |
| hQ : empirical qOptimality Q = Q | SOURCE | Antecedent of the uniqueness characterization, not an assumption for estimator existence |
| π | TYPING | Stationary randomized comparator |
| Each π-row nonnegative | TYPING | Comparator probability distribution |
| Each π-row sums to one | TYPING | Comparator probability distribution |

Counts in this expanded input inventory: SOURCE 3, STANDING 13, TYPING 11, RULED 0, EXCESS 0. There are no ε, δ, concentration certificates, near-optimality assumptions, or arbitrary error-event inputs in these exports. The positive-N restriction is explicit; no N=0 empirical model is invented.

For the empirical row/model: BODY_MATCH OK; PUBLIC_CARRIER OK; WELL_DEFINEDNESS N/A_LITERAL; CHARACTERIZATION N/A_LITERAL; CHOICE_INDEPENDENCE N/A; DEFINITION_VERDICT PASS.

For the Q estimator: BODY_MATCH OK; PUBLIC_CARRIER OK; WELL_DEFINEDNESS OK (unique optimal Bellman solution); CHARACTERIZATION OK (`qEstimator_bellman`, `qEstimator_unique`); CHOICE_INDEPENDENCE OK (uniqueness); DEFINITION_VERDICT PASS.

For the policy estimator: BODY_MATCH OK; PUBLIC_CARRIER OK; WELL_DEFINEDNESS OK (proved finite maximizer existence); CHARACTERIZATION OK (greedy maximizing property and empirical trajectory optimality); CHOICE_INDEPENDENCE N/A (source allows different optimal policies, and no equality of tied policies is claimed); DEFINITION_VERDICT PASS within the source's set-valued optimizer specification.

## Remaining obligations and limits

Joint measurability while varying real reward/discount inputs is not established. The finite-data measurability proofs do not establish it. This is not needed to define the fixed-M experiment or its measurable data-dependent output. A future randomized reward perturbation construction or varying-model parameterization would require a separate argument and an appropriate tie selection.

No true-model near-optimality event or probability bound is defined or proved here. In particular, the empirical optimizer uses the same samples as the estimated rows, so ordinary concentration for a fixed independent policy cannot be substituted. A complete theorem still needs control of that data dependence, the needed empirical/true perturbation and variance estimates across the full ε range, and the universal-constant/sample-logarithm statement above. The current selected optimizer also does not prove the source theorem's claim for every empirical optimal deterministic choice.

## Independent compiler and axiom evidence

After coordinating a compiler slot with the other workers, I generated `.local/PolicyLearningIndependentAudit.lean` as an exact byte copy of the reviewed file plus eleven `#print axioms` commands and ran:

`bash scripts/lean-local.sh .local/PolicyLearningIndependentAudit.lean`

It exited 0 without warnings or errors. Each of the following had exactly the allowed axiom closure `propext`, `Classical.choice`, `Quot.sound`: `samplingLaw_probability`, `samplingLaw_marginal`, `samplingLaw_independent`, `empiricalRow_expectation`, `qEstimator_measurable`, `policyEstimator_measurable`, `valueEstimator_measurable`, `qEstimator_bellman`, `qEstimator_unique`, `qEstimator_eq_trajectory`, `policyEstimator_empirical_optimal`. The temporary audit source was deleted. The reviewed file contains no `sorry`, `admit`, or custom axiom declaration.

This validates the exact staged source and its imported axiom closure. Integration into a production module/export and its corresponding full project check remain lead responsibilities; the ignored staged file is not itself a public library export or evidence of whole-chapter completion.
