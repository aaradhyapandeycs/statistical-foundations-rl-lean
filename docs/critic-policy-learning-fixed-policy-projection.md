# Independent review: fixed deterministic policy projection

Verdict: PASS for the staged fixed-policy projection/event scope. Exact reviewed staged source `.local/PolicyLearningFixedPolicyProjection.lean`, SHA-256 `fffc379f35f554862fb3b0f8cca7538f3cd1bef30a8bbd3cba9a91ea754f7517`; handoff `docs/builder-policy-learning-fixed-policy-projection.md`.

## Full product law

`projectPolicySamples` selects precisely data((s,f(s)),i), for a deterministic f fixed outside the probability experiment. The embedding of State×Fin N into (State×Action)×Fin N is proved injective using equality of state and sample index. This does not require f itself to be injective. Precomposition of the existing independence theorem gives independence of every projected coordinate simultaneously, and the map-to-product characterization combines that independence with the actual coordinate marginals. The deterministic policy transition is proved equal as a distribution to M.transition(s,f(s)), so the resulting pushforward is exactly the fixed-policy evaluation experiment, not an auxiliary or newly sampled law. No assertion is made for data-dependent f or arbitrary randomized policies.

## Same-data estimator and actual semantics

The full empirical MDP and the evaluation surrogate are not identified: their action rows and rewards differ off-policy. `projectedPolicy_value_eq` instead uses the full model's actual trajectory/value-fixed-point bridge, its Bellman equation, point-mass simplification and the projected empirical row definition. The candidate satisfies the exact policy-evaluation estimator Bellman equation, and uniqueness proves equality. Both estimators use the same selected original observations, original reward and discount; no expected surrogate data are substituted.

## True-optimal event

`trueOptimalPolicy_evaluation_event` fixes f=M.optimalGreedyAction and its point-mass stationary policy before applying the proved source policy-evaluation theorem. The confidence is exactly δ/2. It reuses the positive target ε, ε≤1/(1−γ), and the precise budget `720log(S/((δ/2)(1−γ)))/((1−γ)³ε²)≤N`. This is an intermediate theorem about the actual product law and the actual true-optimal policy, not a target-shaped concentration assumption. Finite discrete data makes the target and projection measurable. The proof explicitly transports the event through the full law equality and estimator identity; positive-N witnesses are equated by proof irrelevance.

The same full-data sample law is available for a later intersection with the fitted-policy event; neither event independence nor a separately drawn evaluation dataset is required. The statement includes one-state/action carriers and γ=0 through its production dependency. No fixed-policy result is applied to a fitted policy.

## Remaining scope

This file does not prove the source β-radius specialization, universal high-sample constant, δ/2 event intersection, arbitrary-tie fitted-policy guarantee, or final sample-log conversion. In particular, its ε budget must still be discharged when choosing ε=sqrt(720β/(Nh³)); β≥log(2S/(δh)) and N≥720β/h are sufficient as detailed in the separate plan. Its exact budget is compatible with the source fixed-optimal estimate but is not itself the complete `lem:policy-learning-evaluation`.

Production integration and actual imported-export verification remain separate from staged source validation.

## Independent compiler and axiom evidence

Compiled an exact copy of the reviewed source with all five declaration axiom probes appended, using `bash scripts/lean-local.sh .local/PolicyLearningFixedPolicyProjectionIndependentAudit.lean` against the actual production dependencies. Exit 0 with no warnings/errors. `projectPolicySamples` has no axioms; the four theorem exports each report only `propext`, `Classical.choice`, and `Quot.sound`. This exact-source check elaborates every proof and inspects its transitive axioms; the original source hash was independently verified. No staged imports or dependency artifacts were modified. Compiler slot released.

## Integrated export verification

Production `Formalization/Generative/PolicyLearningFixedPolicyProjection.lean` is byte-identical to the named-instance staging copy SHA-256 `e9008844f6960a6489c51249fb9ee703f597f88205af42d5e4ec296d43e9d088`, which differs from the independently reviewed original solely by naming its local measurable-space instance. The actual integrated module compiled; its import-only audit reports no axioms for `projectPolicySamples` and only `propext`, `Classical.choice`, `Quot.sound` for the other four exports.
