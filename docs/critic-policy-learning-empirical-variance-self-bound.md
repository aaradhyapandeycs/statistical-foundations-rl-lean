# Independent review: empirical-value variance self-bound ingredient

**Verdict: pass for the pointwise empirical-variance identity, its upper bound, and the conditional scalar closure.** The file does not prove the true-resolvent/Jensen bridge or the source's completed self-bounding residual lemma.

The source `generative_model_model_based.tex:2637–2715`, especially `eq:empirical-value-variance-identity`, sets W to the empirical model's actual policy value, r to the true/empirical common policy-averaged reward, and `z=(P̂π−Pπ)W`. The staged module generalizes H to any valid comparison MDP with the same reward and discount as true M and π to any stationary randomized policy. These equalities are explicit source-semantic premises for its general comparison, rather than assumptions about the desired variance estimate. Its empirical policy-learning specialization supplies them by reflexivity for the actual sample-built empirical model and uses the actual data-dependent greedy point-mass policy and `valueEstimator` for the same sample.

The empirical actual Bellman equation proves `γPW=W−r−γz`, with the source residual sign. Squaring and the actual finite population variance definition give exactly

    γ² Var_P(W) = γ²P(W²)−W²+2Wr−r²+2γ(W−r)z−γ²z².

The code's coefficients, γ powers, and negative squared-residual sign agree. Actual empirical trajectory/reward bounds and the Bellman equation give `0≤W−r≤γ/(1−γ)`; actual true rows give `P(W²)≥0`. Using `γ²≤γ`, `W≥0`, `r≤1`, `W≤1/(1−γ)` and dropping the two explicitly nonnegative squares yields precisely

    γ² Var_P(W) ≤ γP(W²)−W² + 2/(1−γ) + 2γ²|z|/(1−γ).

This is pointwise for each state and data array; it does not invoke fixed-policy concentration on the data-dependent fitted policy. Its true variance row and empirical value are the source objects. It includes γ=0 and zero variance; no division by γ is used. The scalar `√(2BS)≤B+S/2` and `S≤A+2B+√(2BS) ⇒ S≤2A+6B` are correct under explicit B,S≥0, with A unrestricted. They are conditional arithmetic results and do not establish that the source's model-specific S satisfies the antecedent.

## Essential forcing-sign boundary

The earlier true-policy resolvent bound for **nonnegative forcing** cannot automatically be applied to W: as a solution under the true P, W has forcing `r+γz`, which can be negative. This is not merely a hypothetical artifact of arbitrary H. Take one action and states s, low, high, with rewards 0, 0, 1; low and high absorb, while true P from s goes to low and high with probability 1/2 each. For any positive γ and N, the actual sample outcome in which all N successors drawn at s are low has probability `2^(-N)`. Its empirical model has `W(s)=0`, `W(low)=0`, and `W(high)=1/(1−γ)`; therefore `z(s)=−1/[2(1−γ)]` and `r(s)+γz(s)<0`. The required self-bounding correction is essential even on a positive-probability empirical sample.

Remaining work must separately establish true-resolvent positivity/order and cancellation for the displayed pointwise inequality, a Jensen bound for an arbitrary nonnegative variance vector, the actual selected-policy all-row residual event, and the resulting model-specific scalar antecedent. The earlier source true-value variance-resolvent theorem does not by itself provide those claims for this empirical W. The staged file and its numerical closure do not establish the complete source `lem:empirical-value-residual`, its probability claim, or a learning sample theorem.

Staged source SHA-256 `55c8045d77c988c70228066f28f485e134de5ca1a78ebf8ce6a760bd7e24c95c`; source chapter SHA-256 `b7e7abfb2c2cb2c0dd82470db5ecac3a67d7163682246d499935d9130214ac4d`. An exact unchanged source copy with original imports and eight appended axiom checks compiled independently, exit 0. The residual definition and all seven theorem exports use only `propext`, `Classical.choice`, and `Quot.sound`. Production export validation remains separate.

## Integrated export verification

Production `Formalization/Generative/PolicyLearningEmpiricalVarianceSelfBound.lean` is byte-identical to reviewed staged SHA-256 `55c8045d77c988c70228066f28f485e134de5ca1a78ebf8ce6a760bd7e24c95c`. The actual integrated module compiled; an import-only audit of its eight declarations succeeded with only `propext`, `Classical.choice`, and `Quot.sound`.
