# Independent review: deterministic policy-learning performance transfer

**Verdict: PASS for the exact deterministic implications stated, for the project's selected empirical greedy policy.** These lemmas do not establish either probabilistic evaluation budget or the full policy-learning theorem, and do not yet quantify over every possible empirical-optimal tie-breaking policy.

Reviewed `.local/PolicyLearningPerformanceTransfer.lean` SHA-256 `a0bd5f59289707d9a4a0739914e960c76a4b04335b14acfdfc1f55806ccb825d`, against `source/upstream/tex/chapters/generative_model_model_based.tex:900–923, 976–985, 1016–1029`, SHA-256 `b7e7abfb2c2cb2c0dd82470db5ecac3a67d7163682246d499935d9130214ac4d`.

## Actual Q and the discount factor

`trajectoryQ_eq_reward_add_trajectoryValue` uses the actual forced-first-action infinite-trajectory Q, not a conditional expectation that requires the policy to put positive mass on the queried action. Its imported `trajectoryExpectedQ_eq_policyFixedPoint` explicitly bridges the intervention law for **every** action, including zero-support actions; the policy-Q/value bridge and true trajectory-value fixed point then give `Qπ(s,a)=r(s,a)+γ P_{s,a}Vπ`. Thus the result applies to every action even when π is the deterministic fitted policy.

Subtracting this formula for the true optimal greedy policy and any stationary randomized policy gives exactly `Q*−Qπ=γ P(V*−Vπ)`. Source-optimal domination is supplied by the proved actual-trajectory greedy optimum. The exported pointwise implication `0≤Q*−Qπ≤γε` uses the true normalized transition row, the uniform state-value loss input, and `γ≥0`. Nested finite sup norms then give the corresponding state/action Q norm bound, with the source's single γ factor and no hidden factor 2. At γ=0 this forces Q loss to exactly zero; no division by γ is used. The generic implication imposes no positive-γ or policy-support hypothesis.

## Two evaluation budgets and tie scope

`policyEstimator_performance_of_evaluation_errors` takes the **true-optimal policy's** actual empirical-versus-true trajectory-value norm bound ε₀ and the **same data-dependent fitted policy's** actual empirical-versus-true trajectory-value norm bound ε₁, both computed in the same sample-built empirical MDP. The imported `policyEstimator_loss_le_evaluation_errors` derives the value gap from those two norms using the actual empirical greedy policy's optimality; empirical optimality and the desired performance gap are not supplied as hypotheses. Thus `0≤V*−Vπ̂≤ε₀+ε₁`, and the forced-action implication yields `0≤Q*−Qπ̂≤γ(ε₀+ε₁)` for all states/actions. If both proved budgets are ≤ε/2 the exact source ε and γε follow, with no extra factor.

The selected fitted action is the concrete `policyEstimator`, whose tie choice is fixed by the empirical model's greedy construction. The original comparator is the constructed actual optimal greedy policy; its actual trajectory Q/V equal the optimal Bellman values and dominate all stationary randomized competitors. The source main theorem says **any** optimal deterministic policy returned by the algorithm. This file's specialized performance theorem covers the implemented selector, not an arbitrary separately supplied empirical-optimal deterministic policy. A later full-source closure must either generalize the deterministic transfer to every such policy, or establish an equivalent verified algorithm specification. The file and builder handoff correctly avoid claiming the universal tie-policy result.

No independence is assumed for the fitted policy. The two budgets are explicit intermediate premises of a deterministic helper, not a claimed source probability theorem. Combining them at confidence `1−δ` requires a valid common event or a justified δ/2 allocation; in particular, the fixed-policy policy-evaluation theorem cannot be applied directly to the data-dependent fitted policy.

## Independent verification

An unchanged exact-source copy with its original production import and five appended axiom probes compiled using `bash scripts/lean-local.sh <temporary-probe>/policy_learning_performance_second_audit.lean`, exit 0 and no diagnostics. All five exports reported only `propext`, `Classical.choice`, and `Quot.sound`. The integrated `Formalization/Generative/PolicyLearningHoeffding.lean` dependency has SHA-256 `b30bd558ad8f2e7d708b89b8541509e4616c508d0d77d0b8f9539e7a59b9912a`. No source-file admissions or custom axioms were found. Independent production-copy comparison, actual export build and imported-axiom checks remain separate.

## Integrated export verification

Production `Formalization/Generative/PolicyLearningPerformanceTransfer.lean` is byte-identical to reviewed staged SHA-256 `a0bd5f59289707d9a4a0739914e960c76a4b04335b14acfdfc1f55806ccb825d`. The actual integrated module compiled, and an import-only audit of all five theorem exports used only `propext`, `Classical.choice`, and `Quot.sound`.
