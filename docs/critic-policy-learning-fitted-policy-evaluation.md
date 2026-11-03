# Independent review: actual-law fitted-policy evaluation event

**Verdict: pass for the concrete empirical greedy selector's evaluation event.** This is the fitted-policy component of `generative_model_model_based.tex:1334–1415,2637–2715`, not the complete policy-learning theorem.

For each finite admissible MDP M, natural N>0 and `0<δ<1`, the proposed theorem uses the actual state-action product `samplingLaw M N` and asserts a single event of probability strictly greater than `1−δ/2`. On that event the actual empirical optimal value `valueEstimator` differs in sup norm from the true infinite-trajectory value of the implemented empirical greedy policy by at most

    2√(2β₁/(N(1−γ)³)) + 6β₁/(N(1−γ)²),
    β₁=2log(16SAN/((1−γ)δ)).

The source's all-action residual and self-bounding steps yield this precise intermediate radius before any high-sample simplification. There is no additional sample-threshold assumption beyond N>0 in this intermediate bound. The statement concerns the particular deterministic greedy `policyEstimator`; it does not universally quantify over all possible tie-breaking policies, so that broader claim is not licensed by this export alone.

The imported `empiricalOptimalValue_allRows_residual` supplies one genuine good event for **all** states and actions, with the actual sample-dependent empirical optimal vector. Only after fixing data on that event does the proof select `policyEstimator ... s` for each state. It makes no claim that the fitted policy, selected row, chosen net index or empirical value is independent of the data. The event inclusion preserves the original strict `1−δ/2` bound without intersecting two separate failure events.

`deterministicPolicyTransition_expectation` rewrites a point-mass stationary policy's actual induced transition expectation to the selected state-action transition row. Applying it to the first and second moments gives the true selected-policy variance identity; applying it to both true and actual empirical models gives exactly the selected-row empirical-minus-true residual. Thus the all-action event discharges the conditional deterministic bridge's pointwise premise for the **same** sample and fitted policy. Nonnegativity of β₁ comes from the separately proved β₁≥4 theorem; source γ=0 and N=1 are allowed. The finite-sample norm is over all states.

The deterministic bridge compares the actual sample-built empirical model's fitted-policy trajectory value with the true model's actual value for that same policy, and derives the bound without requiring nonnegative forcing under the true kernel. It relies on its independently reviewed true-inverse/value identity and scalar self-bound. This event does not yet control the true-optimal-policy evaluation error, perform the union with that second event, prove a universal tie-policy statement, simplify sample complexity, or close the source policy-learning theorem.

Staged source SHA-256 `012f5481e9da86b91a354ed54a808c6f3fd1b2a60d63c5ab7660b65b9452fa8c`; staged empirical residual dependency `c1ac0b61d3af7c76c05d2a56f14f2dd49e1c1f6225988e35130bc128b35fe8fb`; staged variance bridge dependency `ddc7b3c954362ffad70c249d9ac37c2aa5b726be402a0d733f5471bbb800741b`. An exact unchanged source copy with original imports and four appended axiom checks compiled independently, exit 0, after nine staged dependencies were freshly rebuilt in an isolated project-owned directory. All four theorem exports use only `propext`, `Classical.choice`, and `Quot.sound`. Production export verification remains separate.

## Integrated export verification

Production `Formalization/Generative/PolicyLearningFittedPolicyEvaluation.lean` SHA-256 `e51719ce7192202999f24025cbc98dcd9bf880ed25c27cbff8cc507ee3c7f5ef` differs from the reviewed staged source only by qualification of its two imports. The actual production module compiled, and import-only axiom checks of all four theorem exports succeeded using only `propext`, `Classical.choice`, and `Quot.sound`.
