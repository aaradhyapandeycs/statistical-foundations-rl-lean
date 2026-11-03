# Source-first bottleneck: two-state generative lower-bound testing

This is a source/API discovery note, not a formal proof or author-approved correction. Source is `generative_model_model_based.tex:1532–1555,1685–1719,1728–1795,1798–1835` and `prelim.tex:1115–1170,1313–1349` (labels `eq:KL-P1-P0-lower-generative-Q`, `eq:lb-fano-pe-simple-Q-generative`, `lem:properties-M01-lower-generative`, `eq:N-UB-test-lower-Q-generative`, `eq:P-Mi-Q-inaccurate-lower-generative`, `lem:fano`, `lem:KL-tensorize`). Search used the locally pinned Mathlib source; declarations below were inspected, not compiler-probed in this note.

## Exact experiment and source quantitative chain

For fixed `2/3≤γ<1`, `0<ε<1/[32(1−γ)]`, and N satisfying `N≤0.003/((1−γ)³ε²)`, the source compares two finite MDPs with states s₁,s₂ and one action. Both have reward 1 at s₁ and 0 at absorbing s₂; the s₁ self-loop has probability p in M₀ and p+α in M₁. Their reward, discount, size, s₂ transition, N and known inputs agree. The actual observation law contains N independent state-action draws from **both** rows. The s₂ row is deterministic and identical under both models; the s₁ row supplies iid Bernoulli self-loop indicators. A same-data Q estimator is fixed before the model is chosen; it cannot receive the hidden model index or unknown true transition. `lem:properties-M01-lower-generative` supplies interior probabilities, actual optimal-Q separation `Q₁*(s₁,a)−Q₀*(s₁,a)>2ε`, and `α²/(1−p)≤128(1−γ)³ε²`.

The source's intended chain is

    KL(P₁||P₀) = N KL(Bern(p+α)||Bern(p))
      ≤ 2Nα²/(1−p) =: β ≤ 256N(1−γ)³ε² ≤ 0.768 < 0.9.

The reviewed scalar modules establish the parameter arithmetic and Bernoulli **expression** bound, not yet the actual-MDP Q identity or the full hard-MDP experiment KL identity. Separate staged Bernoulli-measure and product KL results have since been developed and independently reviewed; their production integration remains separate. The full joint sample-space supports coincide because both Bernoulli parameters are interior and the common deterministic row has the same support; an actual measure proof must account for those zero-probability off-support tables rather than assume all tables positive.

Source binary `lem:fano` (prelim `:1140–1160`) bounds worst-case testing error by at least both `exp(−β)/4` and `(1−√(β/2))/2`. A direct per-test average-error result suffices and avoids needing to construct an infimum: for every measurable test ψ, prove `(P₀(ψ=1)+P₁(ψ=0))/2≥(1−√(KL(P₁||P₀)/2))/2`, hence the maximum is at least that quantity. The direction `P₁||P₀` must match the KL calculation. This is the binary Pinsker/Le Cam route; the source's other exponential branch is not needed for the concrete 0.1 target, but the full source Fano lemma is a separate stronger obligation.

## Candidate omitted strictness step

At `:1790–1795`, the source states only `p_e≥0.1`; at `:1798–1835` it assumes both estimation success probabilities are **strictly** greater than 0.9 and derives a contradiction, then refers to `eq:P-Mi-Q-inaccurate-lower-generative` at `:1551–1555`, which states that some estimation error probability is **strictly** greater than 0.1. As written, contraposing the strictly-greater-than-0.9 assumption yields only some failure probability `≥0.1`. This is a candidate omitted strictness step in the displayed proof, not a counterexample to the conclusion.

There is numerical slack that repairs it without changing the statement: under β≤0.9, the source's Pinsker branch is

    (1−√(β/2))/2 ≥ (1−√0.45)/2 > (1−0.8)/2 = 0.1,

because `0.45<0.8²`. Thus *every* test has maximum error strictly greater than 0.1. If both estimation failures were ≤0.1, the source threshold test `ψ=0` when `Q̂(s₁,a)≤Q₀*(s₁,a)+ε`, else 1, would have each testing error ≤0.1: correctness on each `≤ε` event uses the strict Q gap `>2ε`. This contradicts the strict test lower bound, proving some estimation failure `>0.1`. The proven `β≤0.768` gives even more slack. Keep this observation visible for independent review rather than silently claiming the source's displayed ≥0.1 contradiction alone gives >0.1.

## What pinned Mathlib provides and gaps

- `Mathlib/InformationTheory/KullbackLeibler/Basic.lean` provides `InformationTheory.klDiv : Measure α→Measure α→ℝ≥0∞`, `klDiv_of_ac_of_integrable`, `klDiv_ne_top_iff`, `toReal_klDiv`, `toReal_klDiv_of_measure_eq`, and self-divergence. `Mathlib/MeasureTheory/Measure/LogLikelihoodRatio.lean` defines `llr` using the Radon–Nikodym derivative and proves measurability and basic identities. For finite probability measures, one still needs actual absolute continuity, integrability, the finite sum/log-likelihood calculation, and the `ENNReal`-to-real comparison. In particular, `ENNReal.toReal ∞=0`; do not infer a finite upper KL bound merely from a `toReal` equality without proving non-top.
- `Mathlib/MeasureTheory/Constructions/Pi.lean` provides `Measure.pi`, `Measure.pi_pi` and `Measure.pi_singleton`, and the project has actual product `ModelBasedPolicyLearning.samplingLaw`, marginal/independence theorems and finite-distribution probability rows. These support an explicit finite-atom calculation. In targeted and whole-tree name searches I did **not find** a matching KL product/tensorization theorem, binary Pinsker/Fano theorem, or a ready-made testing-error lower bound. This is a search result, not proof that no equivalent library theorem exists. Directly proving this finite joint-law KL identity may be shorter than a general measure-theoretic tensorization theorem.
- `Real.log_le_sub_one_of_pos` and the independently reviewed staged `GenerativeLowerBoundBernoulli.lean` give the scalar Bernoulli quadratic bound. The staged `GenerativeLowerBoundParameters.lean` gives the exact probability range, scalar reciprocal gap and α² ratio. These modules do not identify the actual hard-model laws or values.
- The source binary testing inequality remains a substantive obligation. One possible finite route is: prove the needed eventwise Pinsker/total-variation estimate for finite probability mass functions from their KL, then derive the average testing error. Alternatively establish the source exponential testing branch directly and prove its strict numerical bound. Neither route is supplied merely by the definition `klDiv`, Gibbs nonnegativity or scalar Bernoulli KL upper bound. If a different route is used, verify its exact constants, KL direction, finite-support zeros, measurable events and strict endpoints.

## Minimal next declarations and quantifiers

1. Actual valid two-state/one-action MDPs M₀,M₁ with identical known rewards, source transition rows and discounts; actual trajectory-optimal Q formula and strict 2ε gap, connecting the reviewed scalar separation to the source's semantics.
2. Their actual N-sample product laws, explicit common support, absolute continuity/integrability or a finite mass formula, and `KL(P₁||P₀)≤2Nα²/(1−p)` with the exact orientation. State whether N=0 is covered by the product construction or assumed positive.
3. A proved finite binary testing inequality for **every** measurable ψ under those laws, strong enough to give a strict `>0.1` worst-case testing lower bound under the source numeric sample condition. Avoid assuming the testing conclusion as a helper premise in the source theorem.
4. For every single measurable estimator using the common data and known inputs, construct the source threshold test and show each test-error event is contained in its corresponding strict `|Q̂−Q_i*|>ε` event. The resulting quantifier order is `∀ estimator, ∃ i∈{0,1}, P_i(error>ε)>0.1`. If randomized estimators are intended, model an independent common random seed and justify the same average-error bound after mixing; finite deterministic-data estimators alone do not automatically cover arbitrary randomization.

The two-state result is a source illustration, not a repair or certification of the separate disputed fixed-size Theorem 3.7. No code, new axioms, author communications or source modifications are part of this note.

## Independent strictness check

A separate worker independently checked the source implication and numerical repair: the displayed contradiction with both successes `>0.9` yields only some failure `≥0.1`, while the source Pinsker branch under β≤0.9 is strictly above 0.1; assuming both failures `≤0.1` then gives the desired contradiction. This is evidence for an omitted proof step, not a finding that the printed theorem is false.

## Subsequent formal progress

The production modules now prove the finite full-support KL-to-overlap bound,
strict Bernoulli-product testing and estimation bounds, the source two-state
trajectory Q separation, and the strict Q-risk conclusion for one deterministic
estimator on the actual complete two-state observation law. See
[the observation-law review](critic-generative-lower-bound-observation-law.md).
Randomized estimators, the full fixed-size lower bound, and the source's full
Fano lemma remain separate obligations.
