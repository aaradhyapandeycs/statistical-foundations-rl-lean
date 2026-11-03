# Independent review: absorbing-model optimal-value preservation

Reviewed 2026-11-03. Exact staged `.local/PolicyLearningAbsorbingPreservation.lean` SHA-256 `f30ea6939c2f18a913321da758575a13d023241ec8ff19c174e899bcb3cc034b`, independently recomputed. Builder handoff: `docs/builder-policy-learning-absorbing-preservation.md`. Reviewer owns only this report.

## Verdict and exact source

**PASS for the staged deterministic source preservation lemma and its actual empirical-estimator corollary. No statistical independence or policy-learning sample theorem is established.**

I independently read the absorbing model definition at `generative_model_model_based.tex:1231–1252`, `LemAbsToNormalV` / `eqn:relation` at `:1256–1263`, its empirical application at `:1267–1275`, and the source proof at `:2596–2616`. The source changes state x to absorption under every action and sets each reward there to (1−γ)u; it retains all other rewards/transitions, carriers and discount. At u=V*(x), its claim is equality of **optimal state-value functions everywhere**. It does not claim equality of the whole original Q table or of optimal action choices.

The staged general theorem has exactly M,x,s as its substantive inputs and proves `V*_(x,V*(x))(s)=V*(s)`, with both sides actual infinite-trajectory values of their respective proven optimal greedy policies. Its empirical corollary applies that universal theorem to the actual sampled empirical MDP, with u equal to that empirical model's own optimal value at x. Equality is derived, not assumed.

## Refutation checks: what is and is not preserved

A potentially invalid stronger proof would reuse the original Q unchanged at x. The implementation avoids that error. Its candidate `preservedOptimalQ` equals the old optimal Q at s≠x and equals the common scalar V*(x) **for all actions at x**. Original suboptimal actions at x can have smaller Q, so equality of original and absorbing Q tables is neither true in general nor asserted here. At x, the new reward is action-independent, making all new Q actions equal to V*(x), as required.

The candidate's action maximum is proved equal to original V* at every state: constant V*(x) at x, and the old optimal-Q maximum elsewhere. At x, absorbing transition and reward give `(1−γ)V*(x)+γV*(x)=V*(x)`. Away from x, unchanged rewards/transitions and the same candidate continuation maximum give exactly the original Q Bellman equation. The candidate therefore satisfies the **actual absorbing model's** optimality equation. Proved uniqueness identifies it with that model's optimal fixed point; the actual greedy-trajectory bridge then turns its maximum into the absorbing optimal trajectory value. No preservation equation is a binder or an unexplained definition.

Nor does the proof assume the two greedy policies have identical actions, share a tie rule or agree along trajectories. Each model has its own chosen greedy optimizer; the unique optimal value comparison is sufficient. The result compares actual optimal values, not the value of the old optimal policy evaluated in the new model.

## Actual model and trajectory semantics

The dependency `.local/PolicyLearningAbsorbing.lean` was inspected and its hash recomputed as `dfdedc125e606f88241c2c491df64306ee3b0b2f83b6361f5f9dcaa6b2bd0a92`. It uses literal source-prescribed piecewise rows: point mass at x at the absorbing state, original row elsewhere; reward (1−γ)u at x and original reward elsewhere. The u interval proves the modified rewards remain in [0,1]. Discount and finite nonempty carriers are copied. These if-branches are the source's actual definition, not invented off-domain fallbacks.

`optimalTrajectoryValue M` is literally M's actual infinite controlled-trajectory expectation under `M.optimalGreedyPolicy`. The upstream reviewed result proves that policy simultaneously maximizes trajectory V/Q against every stationary randomized policy; the new `optimalTrajectoryValue_eq_actionMaximum` consumes the actual policy-average-Q, forced-action-Q and greedy maximum theorems. This supplies genuine optimal-state-value semantics under the source's stationary policy convention. No new claim about arbitrary history-dependent policies is needed or made.

`optimalValueAbsorbingModel M x` sets u to that actual optimal value and supplies both required interval proofs using actual trajectory bounds. There is no externally assumed admissibility or preservation condition. Its definition and characterization are source-faithful on the whole declared finite-MDP carrier.

For `optimalTrajectoryValue`, BODY_MATCH OK; PUBLIC_CARRIER OK; WELL_DEFINEDNESS OK via the upstream optimal greedy trajectory construction; CHARACTERIZATION OK via the proved maximum theorem and upstream optimality; CHOICE_INDEPENDENCE OK at the value level via the unique fixed point; DEFINITION_VERDICT PASS. For `optimalValueAbsorbingModel`, BODY_MATCH OK; PUBLIC_CARRIER OK; WELL_DEFINEDNESS N/A_LITERAL; CHARACTERIZATION N/A_LITERAL; CHOICE_INDEPENDENCE N/A; DEFINITION_VERDICT PASS. `preservedOptimalQ` is an explicit internal candidate whose defining Bellman property is proved, not a replacement definition of the source optimal value.

## Original and empirical models are kept distinct

The general theorem is valid for every admissible M, so it may be instantiated with either the true MDP or an actual empirical MDP. The empirical corollaries do exactly the latter. Their absorbing parameter is

`optimalTrajectoryValue (empiricalModel M N hN data) x`,

not the original true model's V*(x). The new absorbing model is built from that same empirical MDP and data. The source's claimed pointwise `Vhat*_(x,Vhat*(x))=Vhat*` is therefore represented with the correct model on both sides.

The theorem `empirical_optimalTrajectoryValue_eq_valueEstimator` is definitional equality of the actual empirical optimal-policy trajectory value and the algorithm's actual trajectory value estimator. The same empirical greedy selector is used by both definitions. This is not a circular assumption that the estimator is optimal; its upstream empirical optimality theorem supplies that independent meaning. Composing this equality with the general preservation theorem gives the final estimator corollary at every state and every sample outcome.

The only sampling-domain restriction is N>0 inherited from frequency rows. No typical-data, concentration, transition-accuracy, positive-probability-support or random-event premise occurs. Thus pointwise preservation holds even on observation arrays of zero probability under the true sample law.

## Expanded premise inventory and endpoints

| Expanded input family | Bin / basis |
|---|---|
| State, Action | TYPING finite carriers |
| Fintype State, Fintype Action | STANDING finite source MDP |
| M nonempty state/action fields | STANDING nonempty source spaces |
| M.transition and nonnegative/unit-sum row fields | STANDING true probability kernel |
| M.reward and [0,1] fields | STANDING source reward convention |
| M.discount and 0≤γ<1 fields | STANDING source discount range |
| x | SOURCE absorbing state |
| s, a in pointwise/helper statements | TYPING state/action queries |
| N and hN:0<N in empirical corollaries | SOURCE positive empirical sample count |
| data | TYPING arbitrary actual sample array |
| Local DecidableEq State | TYPING constructed internally by classical equality |

There are no additional supplied optimality, equality, value-bound, uniqueness, independence or concentration premises. The model's nonempty action instance is obtained from its source field inside the proof. EXCESS=0 for the stated preservation lemma.

All results cover γ=0 without division by γ. Then the new reward at x is V*(x), so the new state value remains the original maximum immediate reward even if original suboptimal action rewards differ. At γ approaching one, 1−γ remains strictly positive and all values/normalizations are finite. Singleton states/actions and ties are covered by genuine finite maxima. The admissibility proof does not require a strict interior value u; both 0 and the horizon upper endpoint are included.

## Dependence limitation and source coverage

The empirical parameter Vhat*(x) depends on the same data, including possibly the omitted state's rows. The source explicitly warns about this at line 1275. The preservation theorem proves equality **pointwise** with that random parameter; it does not prove the resulting absorbing optimal value is independent of the removed empirical row. Fixed-u deterministic invariance in the dependency cannot be applied with two differing data-dependent u values to infer independence. No such step occurs in the implementation.

A fixed finite parameter net, stability/covering estimates, a measurable dependence-on-retained-coordinates argument, actual product-law independence, and subsequent concentration remain separate. This lemma alone does not establish policy-learning sample complexity or the claim for arbitrary data-dependent parameter selection. The staged source covers the deterministic source lemma and stated empirical identity; production import integration/export checks remain separate.

## Independent compiler and axioms

After source review and the lead's explicit compiler-slot allocation, I independently rebuilt the exact staged absorbing source in a fresh project-owned temporary artifact directory. Using it plus the ordinary integrated project/dependency paths in `LEAN_PATH`, I compiled `.local/PreservationIndependentAudit.lean`, an exact unchanged copy of the reviewed preservation source with `#print axioms` for all ten definitions/theorems.

Both dependency compilation and the exact-source probe exited 0 without warnings or errors. Every inspected export reported exactly `propext`, `Classical.choice`, `Quot.sound`, including the general preservation result and actual empirical estimator corollary. No `sorry`, `admit` or custom axiom occurs. The probe and fresh staged artifact directory were deleted, and the compiler slot released immediately. This confirms the exact staged implementation/transitive axiom closure without trusting a preexisting staged object. Future production import changes and imported-export checks remain separate.

Source chapter SHA-256 is `b7e7abfb2c2cb2c0dd82470db5ecac3a67d7163682246d499935d9130214ac4d`.

## Integrated export and named-environment coverage (2026-11-03)

Independently recomputed production `Formalization/Generative/PolicyLearningAbsorbingPreservation.lean` SHA-256 as `883eb9411a0f9aadad8631346a3d5149d256a6fa610d1c769b4d66070c06bb71`. Exact byte comparison against the reviewed staged source proved the sole change is `import PolicyLearningAbsorbing` becoming `import Formalization.Generative.PolicyLearningAbsorbing`. All definitions, statements, proofs and instance names are unchanged.

Using the lead's explicit compiler allocation, I built the actual production module to its own project `.olean` with `bash scripts/lean-local.sh -o .lake/build/lib/lean/Formalization/Generative/PolicyLearningAbsorbingPreservation.olean Formalization/Generative/PolicyLearningAbsorbingPreservation.lean`; exit 0 without diagnostics. I then compiled `.local/IntegratedPreservationAudit.lean`, whose only import was the production preservation module. It inspected **all ten actual imported definitions/theorems** and additionally reconstructed the source's full vector equality as an exact-type example:

`optimalTrajectoryValue (optimalValueAbsorbingModel M x) = optimalTrajectoryValue M`.

That equality was proved by function extensionality and exact applications of the actual production preservation export, with only arbitrary valid M and x. The import audit/example exited 0 without diagnostics, and every one of the ten declarations reported exactly `propext`, `Classical.choice`, `Quot.sound`. The temporary probe was deleted and the compiler slot released.

**Named-environment coverage: FULL.** The actual production export `optimalValueAbsorbingModel_preserves_optimalTrajectoryValue` fully covers the entire mathematical assertion of source Lemma 3.3, label `LemAbsToNormalV`, at lines 1256–1263. The source's u*=V*(x) is instantiated inside the actual model definition with proved admissibility, both V* functions are genuine optimal trajectory values, every source state is covered, and the pointwise theorem yields precisely the source's vector equality by the compiled example. No extra premise, specialization to the empirical model, chosen policy coincidence, preservation hypothesis or deferred Bellman obligation weakens it. The auxiliary empirical corollaries are additional source-related coverage, not a substitute for the generic lemma.

This classifies that deterministic named lemma only. It does not cover the later net lemma, fixed-u statistical independence, concentration or the general policy-learning theorem. No source inventory status was changed by this reviewer. The lead's shared project build and the recorded independent production dependency checks remain the surrounding integration evidence.
