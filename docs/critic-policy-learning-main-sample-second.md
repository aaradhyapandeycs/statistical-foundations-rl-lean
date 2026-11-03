# Second independent source review: main policy-learning sample theorem

Verdict: PASS for source/semantic fidelity of the staged candidate on the source's positive-sample domain. This is a source-only second review; no new compiler or axiom certification is claimed here. Actual integrated exports, transitive axiom checks and project integration remain separate closure gates.

Exact reviewed source: `.local/PolicyLearningMainSample.lean`, SHA-256 `1ee82404036e709de10d9b60cc3a02558137b3e4ad286681b2f7472f677ddaf6`. Reviewed handoff: `docs/builder-policy-learning-main-sample.md`. Authoritative source: `source/upstream/tex/chapters/generative_model_model_based.tex`, SHA-256 `b7e7abfb2c2cb2c0dd82470db5ecac3a67d7163682246d499935d9130214ac4d`, entire `Thm:sample-compl-main` (around lines 899–927), together with algorithm, known-reward convention, and preceding MDP definitions.

## Quantifiers, source model and algorithm

The existential wrapper chooses one positive real universal constant 10240 before all finite State/Action carriers, their Fintype instances, MDP, sample count, confidence and accuracy. It cannot depend on S,A,γ,N,ε,δ, model or tie selection. The MDP structure supplies finite nonempty state/action carriers, actual stochastic transition distributions, known [0,1] rewards and 0≤γ<1. There is no unintended γ lower bound, action gap, unique optimizer, lower cardinality restriction or hypothesis involving a desired concentration/performance estimate. Arbitrary finite carrier types cover the source finite tabular environment; enumerations or standard Fin carriers are not required.

`Samples` contains exactly N observations per state-action pair, and `samplingLaw` is their complete independent product with true-row marginals. The empirical model has actual count/N transition rows and exactly the original reward and discount. The empirical-optimal predicate refers to actual trajectory value domination at every state against all stationary randomized policies. The concrete selector is proved to satisfy it on every sample. Every f admitted by the predicate is therefore a legitimate exact deterministic empirical optimizer; existence does not depend on the target event. The algorithm's unspecified tie choice is covered by universal quantification over all such f inside one event after data is realized. This is stronger than one theorem for each fixed tie rule and does not require a policy-count union or independence of the fitted policy.

The source says “any optimal deterministic policy” and the candidate preserves this scope; it does not narrow the assertion to the canonical `policyEstimator`. It makes no statement about arbitrary randomized output policies, approximate planners, reward perturbations or reward estimation. These are not required by the printed main theorem. The later computational approximate-planning remark remains outside scope.

## Exact probability, sample condition and outputs

The confidence domain is exactly 0<δ<1. Accuracy is exactly 0<ε≤1/(1−γ), including its upper endpoint. With h=1−γ and casts of the finite cardinalities and N into real, the budget is precisely

`N ≥ 10240 log(S A N/(h² ε δ))/(h³ ε²)`.

This is per-row N; SAN is total count only inside the printed logarithm. The N-dependent source condition has not been replaced by a stronger logarithm without proof or an epsilon-independent assumption. No asymptotic interpretation is used.

The single final event contains both source conclusions at every state and every state-action pair, for every empirical-optimal deterministic f:

`Vᶠ(s) ≥ V*(s)−ε`, and `Qᶠ(s,a) ≥ Q*(s,a)−γ ε`.

Both functions are actual expected discounted trajectory returns in the true model. Q means forced first action followed by the policy, including actions with zero policy support; it is not an estimator Q or an on-policy-support-only substitute. The optimal reference is the constructed true optimal greedy policy, proved to realize the true optimal value/Q among stationary randomized policies. Thus its choice of tie does not alter V*/Q*. No norm-only substitute replaces the source pointwise claims. Strict probability greater than 1−δ is stronger than the source at-least assertion and applies to their conjunction, without an additional failure allowance for Q.

## Positive N and boundary analysis

The explicit hN:0<N encodes the source sampling/frequency/log domain. Ordinary empirical frequency estimation divides by N, and the printed log contains N, so N=0 is outside the source algorithm's domain. Lean's totalized log instead assigns log0=0, making the unguarded threshold true at N=0; the Pointwise dependency formally proves that pathology. Consequently hN must not be advertised as derived from this totalized threshold. Its visible inclusion is a faithful domain guard. It introduces no large-sample restriction beyond positivity.

For at least two states, the proof derives SAN≥2 internally from S≥2,A≥1,N≥1 and then invokes the scalar logarithm comparison. It does not assume S≥2 in the final theorem. The entire one-state case is proved exactly: the policy-evaluation projection and singleton exactness identify every empirical deterministic-policy value with its true value, then empirical optimality and the proved performance comparison give zero V and Q losses. This covers S=A=N=1 as well as any larger action/sample count; there is no attempt to force an invalid uniform β≤constant·source-log comparison when its right side approaches zero in this corner.

γ=0 is included: the Q bridge multiplies by γ and never divides by it. Empirical and true known rewards coincide, so exact empirical optimizers are valid true optimizers at this endpoint. All distributions and denominators remain valid since h>0; ε's upper endpoint and δ approaching either allowed boundary require no omitted side condition.

## Proof dependencies and constants

The transitive source path is the sharp leave-one-out analysis, not the deliberately approximate first attempt. Preserved absorbing values, a fixed finite grid, row independence at fixed grid parameters, Bernstein over rows/grid, variance perturbation, and the generic empirical-value true-resolvent self-bound establish one all-row event. Postselection and equality of empirical optimal values yield the fitted evaluation event simultaneously for all exact empirical optimizers. Separately, the fixed true-optimal policy is selected before data; injective coordinate projection proves its full policy-evaluation product law, and Bellman uniqueness proves the same-data estimator identity. Those two events use failure δ/2 each and are joined by the proved complement/union bound on the same experiment, without event independence.

The source evaluation lemma uses concrete constants 720 and16: under N≥720β/h its common event gives true V loss≤32sqrt(β/(Nh³)). The main arithmetic file explicitly proves β≤10L for K=SAN≥2, where L is the printed log; it uses hε≤1 and K≥2 to absorb log16 via logK. From budget 10240L/(h³ε²)≤N it derives both N≥720β/h and 32sqrt(β/(Nh³))≤ε. Numerically, 10240=10·32² and exceeds 720·10; the algebraic proof uses the accuracy upper bound to obtain the threshold. Thus the evaluation threshold and accuracy conclusion are internal consequences, not additional theorem assumptions. The final V implication is algebraic; the final Q implication is the exact γ times true-row expectation of V loss.

The previously reviewed Pointwise declaration includes both source evaluation inequalities with common constants, including the correct pointwise sign. Its exact staged source and full staged dependency closure were independently rebuilt and axiom-audited in `docs/critic-policy-learning-source-pointwise.md`. This second review read the main arithmetic proof and its direct use, but does not replace the separate first critic's fresh compilation/axiom audit of this new main candidate.

## Remaining closure gates

No mathematical/source mismatch was found in the entire printed main theorem. The final claim should still be limited to a reviewed staged candidate until its exact direct/dependency compilation, transitive axiom inspection, qualified production-import diff, actual integrated export audit and shared project build are complete. Those checks must use this exact source version or trigger a new review. No theorem at zero samples, approximate planning extension, randomized estimator generalization or full monograph closure follows from this verdict.

## Integrated export verification

Production `Formalization/Generative/PolicyLearningMainSample.lean` SHA-256 `1ec3eb82445ad77b3402be0e5ad33a30c90af2160044625f011f28a520b2be22` differs from reviewed staged SHA `1ee82404036e709de10d9b60cc3a02558137b3e4ad286681b2f7472f677ddaf6` solely by qualification of its two imports. The actual module and its byte-identical staged arithmetic dependency compiled. Import-only checks of all four main exports and two arithmetic exports use only `propext`, `Classical.choice`, and `Quot.sound`; an actual-import `#print` confirms the universal 10240 binder and source-shaped positive-N any-tie V/Q event. The build reports only the two known tactic-style warnings.
