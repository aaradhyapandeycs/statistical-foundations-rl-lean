# Independent review: arbitrary empirical-optimal tie policies

Verdict: PASS for the stated intermediate event and deterministic comparison; not the complete named learning-evaluation lemma or final source sample theorem.

Reviewed exact staged `.local/PolicyLearningAnyOptimalPolicy.lean`, SHA-256 `e60fb346a093414e4b1f1b7cd0299196552a36e407fc2d5ec2189fe0562fecdc`, and `docs/builder-policy-learning-any-optimal-policy.md`.

## Source and binder audit

The source algorithm outputs an optimal deterministic empirical policy, and the main theorem explicitly covers any such policy. `EmpiricallyOptimal` quantifies all stationary randomized comparison policies and every state in the actual empirical MDP, then requires that the deterministic point-mass policy dominates their actual trajectory values. This is the source algorithmic optimality condition, not an assumed evaluation/performance bound. It is inhabited for every data outcome by the implemented selector. No uniqueness, action-gap, positive-discount, independent fitted-policy, or empirical transition restriction is imposed.

`empiricallyOptimal_value_eq` proves both directions of equality between any such policy's actual empirical value and the canonical empirical optimal value. The inequality from the arbitrary optimizer uses the canonical comparison policy, and the converse uses proved empirical greedy optimality. Equality is proved, not assumed. The condition is universal over states, so optimality at an initial distribution alone is not accidentally substituted.

The probability theorem quantifies f inside the event, after the realized data: one event controls every empirically optimal deterministic tie policy simultaneously. This is stronger than quantifying one deterministic tie rule before probability, and closes the canonical-selector scope limitation for this fitted-evaluation intermediate. The finite discrete data carrier makes this event measurable, including its implication and universal finite-policy quantifier. No additional planner seed or randomized action policy is claimed.

## Proof consumption and postselection

The event first holds for all state-action rows evaluated on the same empirical optimal-value vector. Only then does the proof introduce data, f, and its empirical optimality evidence. It replaces that vector by the proved empirical trajectory value of f; the generic deterministic empirical variance/resolvent result applies to this actual policy, true model M, and the same empirical model. Known reward and discount equalities are discharged by reflexivity. The selected true/empirical row expectations and true variance reduce exactly to action f(s), so the all-action event supplies the needed row bound. Neither independence of f from data nor a union over policies is used.

Probability is strictly above 1−δ/2 under `samplingLaw M N`, with exact `leaveOneOutBeta=2log(16SAN/((1−γ)δ))`. The target radius is the unsimplified source self-bound `2sqrt(2β/(Nh³))+6β/(Nh²)`. There is no hidden N threshold: this intermediate bound is valid for every N>0. β nonnegativity is derived from proved β≥4. The source high-sample requirement is needed later when simplifying this radius, not assumed here.

`empiricallyOptimal_performance` explicitly consumes two actual evaluation norm budgets, proves pointwise V loss between zero and ε₀+ε₁ from empirical optimality and true optimality, and derives Q loss between zero and γ(ε₀+ε₁) using the actual forced-first-action bridge. All data and models are identical throughout; γ=0 is included and involves no division by γ. These conditional deterministic budgets are appropriate in this helper, but must be discharged by the final joint event. No probability claim is attached to them directly.

## Independent compiler/axiom evidence

Freshly compiled the exact staged PerformanceTransfer, FittedPolicyEvaluation, and AnyOptimalPolicy sources serially into an isolated project-local audit artifact directory, using the existing staged lower dependencies and production dependencies. All exited 0 without diagnostics. Then compiled an exact copy of the reviewed AnyOptimalPolicy source with `#print axioms` appended for all five declarations, including `EmpiricallyOptimal`; every result reported only `propext`, `Classical.choice`, and `Quot.sound`. The reviewed source hash matches the handoff. Lower staged dependencies were consumed from their existing reviewed artifacts, not rebuilt transitively in this audit; the axiom probes are transitive. No dependency artifacts were deleted or modified.

This evidence establishes staged compilation and source semantics. Qualification of staged imports, actual production export compilation and integrated axiom checks remain separate landing requirements.

## Remaining source theorem scope

The fixed true-optimal evaluation event on the same product law, the δ/2 union, universal high-sample coefficient choices (including √2 accounting), and final sample-log conversion are not in this file. The named `lem:policy-learning-evaluation` has both fitted evaluation and optimal-policy performance conclusions; this file alone proves its unsimplified fitted-evaluation ingredient. The Q comparison is correct but does not replace either named V conclusion. Approximate planning is outside this exact optimizer predicate and requires a separate tolerance analysis.

## Integrated export verification

Production `Formalization/Generative/PolicyLearningAnyOptimalPolicy.lean` SHA-256 `8337f9ce0d26439fbb7f02afd8d64e98b8806acf8ec5cd8dd253403e1a09a46e` differs from the independently reviewed staged SHA-256 `e60fb346a093414e4b1f1b7cd0299196552a36e407fc2d5ec2189fe0562fecdc` only by qualification of its two imports. The actual production module compiled, and import-only axiom checks of its definition and four theorem exports succeeded using only `propext`, `Classical.choice`, and `Quot.sound`.
