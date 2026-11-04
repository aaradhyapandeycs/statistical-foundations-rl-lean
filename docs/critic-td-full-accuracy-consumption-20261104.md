# TD terminal-accuracy proof-consumption review (2026-11-04)

Verdict: no unconsumed conclusion-shaped hypothesis or confidence-event mismatch found in the examined production chain. This is a source-level review of the exact declarations and uses below, not an independent compiler or transitive-axiom check. The separate focused rebuild passed according to the coordinator; the current actual-export axiom audit and integration checks remain separate. This review does not independently certify every proof term in the older concentration library.

Source checked: `source/upstream/tex/chapters/generative_model_model_free.tex`, source rate schedule lines 179–185, theorem `thm:policy-evaluation-TD` lines 203–224, and fixed-terminal error/Freedman/variance steps lines 464–785. The printed theorem is terminal accuracy under the stated schedule, bounded initialization, γ ≥ 1/2, δ, ε, and sample budget. Its proof invokes an eligible late terminal and a budget consequence for the rate weights; those are derived in this chain rather than introduced into the outer statement.

## Actual outer export and premise consumption

`StatisticalRL.TemporalDifference.tdSource_policyEvaluation_accuracy_exists_universal_constants` (`TDSourceFullAccuracyUniversal.lean`, SHA-256 `1bcc96d2b7dd6af07196a404e30ba9169df2227ae754c317b9ff4880bce4f6d5`) first chooses c₁=c₂=1/4 and c₃=max(4096, exp(4)/log(2)^4), before State, Action, model, policy, schedule and accuracy/confidence parameters. Its body derives terminal eligibility from the source budget using `tdSource_final_terminal_eligible_of_budget`; derives the constant relations including 4≤c₁c₃, c₁c₂≤1/8, c₃≥384 and c₃≥3168; and obtains state-cardinality positivity from `M.state_nonempty`. It converts the source finite positive-index schedule to `TDStepSizeSchedule` by unfolding the two definitions. It then calls the all-state first-Freedman producer, the common-event variance producer, and `tdInitialError_contraction_of_source_budget` at the same M, π, η, T, V₀ and t=T. The variance infinity-norm event is enlarged to its coordinatewise version by `norm_le_pi_norm` and probability monotonicity. All three resulting facts are passed to `tdSource_final_accuracy_of_events`. The final signature does not assume an accuracy event, variance cap, martingale property, desired conclusion, or numerical late-time premise.

## First concentration event and its hypotheses

`tdSource_firstFreedman_allStates_of_budget` (`TDSourceFirstFreedmanAssembly.lean`, SHA `15dd0b646592e456c8337f3f318cf8e1b721d3bdd9f55270f008f6debdb962c5`) obtains the large-schedule condition from `tdSourceBudget_implies_schedule_large` and calls `tdSource_firstFreedman_comparisons` (`TDSourceFirstFreedmanComparisons.lean`, SHA `a29ae10bee6e96d4f98f3dec3a64a01373e6b68e7808ea7ab269d1a656b81995`). The latter produces the weight envelope, used-rate bounds, increment and variance scales, positive dyadic level, and logarithm comparison from the schedule and budget, using `tdSource_freedman_schedule_weight_caps` in `TDSourceFreedmanScheduleCaps.lean`. It passes those facts to `tdSource_firstFreedman_allStates_of_caps` (`TDSourceFirstFreedmanUnion.lean`, SHA `223457e58b420df3a2822125ab1097044211e39bdeb683ef60c184f4a8f54eeb`). The union uses δ/(2ST) for each coordinate and obtains failure at most δ/(2T); no independence between state events is assumed. The cap-union helper has a redundant shadowed δ binder in its written signature, supplied twice with the same value at this call; it does not add a mathematical restriction.

`tdTerminal_freedman_weightEnvelope` supplies Freedman with the actual `tdSamplingLaw`, used-sample filtration `tdSampleFiltration`, adapted fixed-terminal increment, zero conditional expectation, and derived bounded-increment and conditional-variance caps. `tdTerminalIncrement_strong_nextPast` and `tdTerminalIncrement_condExp_past_zero` in `TDTerminalHistory.lean` (SHA `368cd60124697e1ffdc7c008e88ba5197720f5877dcbb91d8c8888db1006bc38`) handle real increments before the terminal and zero-padding afterward. `tdSampleFiltration` and `tdTerminalVarianceSum` (`TDVarianceSum.lean`, SHA `95b9fb946b306f81eefd07df33d877d7b5346f6e3a01902eb156d144ec813488`) use the actual observed prefix; the exact conditional-square identity is only asserted almost everywhere and combines the true policy-row variances. The separately provided smaller natural-history square identity retains the outer conditional expectation rather than treating a raw-prefix variance as measurable in the smaller sigma algebra.

`TDSynchronousSampling.lean` defines the probability law as a finite product of `(M.policyTransition π s).rowMeasure`, with independently sampled state/time coordinates. `tdPast_indep_fresh`, `tdFresh_marginal`, and `tdRowIncrement_condExp_zero` connect the past, fresh row and centering under that same law. The extra time-zero coordinate is excluded from used prefixes; the TD recursion reads samples 1 through T and the extension outside the finite array is irrelevant through T. The local state measurable space is top on a finite state type; the law and event are elaborated under that instance. The exact-T bridge now proves the projection law and pathwise iterate equality, as described below. The independent source critic reviewed the projection semantics; the author of this consumption review also built the bridge and therefore does not independently certify its source correspondence.

## Variance, initial term and final intersection

`tdSource_varianceProxy_both_of_budget` (`TDSourceVarianceProxyLemma.lean`, SHA `58e5a56a635759aeb1d37071bb4d4a6eaad16f47658e77bac2ebb99452893670`) derives its source-budget early/late split and fixed-terminal proxy event, then combines them on the same law using `tdOriginalVariance_commonEvent_of_split`. The split and nonnegativity are almost-everywhere facts; finite-state `ae_all_iff` and `measure_mono_ae` correctly retain this qualifier. The infinity-norm 33-scale bound is not assumed by the outer theorem.

`tdInitialError_contraction_of_source_budget` (`TDInitialErrorContraction.lean`, SHA `2a95be0921d9262d45f0dc0e8a24de3ed7d18c8a53c2d42f08a450f884a1eb30`) derives the used-rate interval and source-budget weight estimate, bounds the initial trajectory-value residual by the effective horizon, and applies the actual error propagator. The k=0 weight is the product over rates 1,…,t; it does not require an η₀ bound. `tdSourceRateExtend` (`TDSourceRateFiniteExtension.lean`, SHA `0092f57ccff71de878c6c16231d1cd7ec33a319d9dfbd604afa2c5b500fde23e`) preserves indices through T and sets only the tail to zero; its global unit bound is explicitly only for positive indices. The separate standalone step-size issue C5 is not used as an unconditional lemma here: the needed large-time condition is derived from the main budget.

`tdSource_final_accuracy_of_events` (`TDSourceFinalAccuracyComposition.lean`, SHA `3b764f48fe4f27c8c6c0ec320bd029eb43ceac8ed40b51269a79f3e8bc0b7fbb`) explicitly takes the two event premises and initial norm, then uses `tdErrorValue_eq_initial_add_increments`, the coordinate projection, and scalar absorption to obtain the target on their intersection. `tdSource_final_scalar_absorption` (`TDSourceFinalScalarBudgetConsumer.lean`, SHA `dfe035f37dcb83af43406fa3cfcb1e321b874e6cf8b12aa66b92c3d42a0ad597`) derives root ≤ ε/2, linear ≤ ε/4 and initial ≤ ε/4 from the same source budget and the selected c₃ bound; its terminal cancellation uses positive ε. The two failures cost δ/(2T) each; finite sample spaces make the events measurable and the union bound gives δ/T≤δ. No independence of these events is assumed. `tdErrorValue` is the actual iterate minus `M.trajectoryExpectedValue π`, and the trajectory-value/Bellman bridge is a separate existing production dependency.

## Exact-T source experiment and event transfer

The current outer source-facing export is `tdSource_policyEvaluation_exactSamples_accuracy_exists_universal_constants` in `TDSourceAccuracyExactSamples.lean`. Its body obtains the same constant-first padded-law theorem, defines the exact-T accuracy event, and proves the projection and event measurable using finiteness. It rewrites the target event probability with `tdUsedSampleProjection_map_law` and `Measure.map_apply`; for a padded-good outcome, it unfolds `tdErrorValue` to the padded sampled iterate and uses `tdSampledIterate_eq_sourceSampledIterate` to establish membership in the projected exact-T event. `measureReal_mono` then transfers the probability lower bound. The inequality direction and event set inclusion are correct, and no additional target-shaped premise appears. The map theorem asserts equality of the entire joint product measures, not just one-coordinate marginals; the iterate theorem is pointwise for every array.

The previous padded intermediate is now universe-polymorphic in State and Action. Comparison to the prior focused source shows that its proof body is unchanged; the declaration changed `Type` to `Type*`, alongside qualified imports and module documentation. Source fidelity of the new projection and source-facing statement was separately reviewed; this document's author contributed the projection proof and does not independently certify that component.

## Reviewed current source hashes

The following SHA-256 values identify the exact 14 current sources examined; these hashes are not build or axiom receipts.

- `Formalization/ModelFree/TDSourceFullAccuracyUniversal.lean`: `1bcc96d2b7dd6af07196a404e30ba9169df2227ae754c317b9ff4880bce4f6d5`
- `Formalization/ModelFree/TDSourceAccuracyExactSamples.lean`: `7afd0996fff921fdc91f22e53aad673e6485aa8dfffd472faf8d6b687e67f375`
- `Formalization/ModelFree/TDSourceFinalAccuracyComposition.lean`: `3b764f48fe4f27c8c6c0ec320bd029eb43ceac8ed40b51269a79f3e8bc0b7fbb`
- `Formalization/ModelFree/TDSourceFirstFreedmanUnion.lean`: `223457e58b420df3a2822125ab1097044211e39bdeb683ef60c184f4a8f54eeb`
- `Formalization/ModelFree/TDSourceFirstFreedmanAssembly.lean`: `15dd0b646592e456c8337f3f318cf8e1b721d3bdd9f55270f008f6debdb962c5`
- `Formalization/ModelFree/TDSourceFirstFreedmanComparisons.lean`: `a29ae10bee6e96d4f98f3dec3a64a01373e6b68e7808ea7ab269d1a656b81995`
- `Formalization/ModelFree/TDInitialErrorContraction.lean`: `2a95be0921d9262d45f0dc0e8a24de3ed7d18c8a53c2d42f08a450f884a1eb30`
- `Formalization/ModelFree/TDSourceFinalScalarBudgetConsumer.lean`: `dfe035f37dcb83af43406fa3cfcb1e321b874e6cf8b12aa66b92c3d42a0ad597`
- `Formalization/ModelFree/TDSourceVarianceProxyLemma.lean`: `58e5a56a635759aeb1d37071bb4d4a6eaad16f47658e77bac2ebb99452893670`
- `Formalization/ModelFree/TDTerminalHistory.lean`: `368cd60124697e1ffdc7c008e88ba5197720f5877dcbb91d8c8888db1006bc38`
- `Formalization/ModelFree/TDVarianceSum.lean`: `95b9fb946b306f81eefd07df33d877d7b5346f6e3a01902eb156d144ec813488`
- `Formalization/ModelFree/TDSourceRateFiniteExtension.lean`: `0092f57ccff71de878c6c16231d1cd7ec33a319d9dfbd604afa2c5b500fde23e`
- `Formalization/ModelFree/TDSourceSamplingDefinitions.lean`: `c7a55219c10f2e4f76b317a199aead2115fd24dd1d80c3ee5b4a76e9cc136a63`
- `Formalization/ModelFree/TDSourceSamplingProjection.lean`: `75b995e0bb0afd5520d6f8e31d2ecc8f2a184d24ed38d0fb6c2c682f770d3a99`

## Fourteen affected production modules

- `Formalization/ModelFree/TDSourceFreedmanScheduleCaps.lean`: `5ceea08b8316c1c63c4e6d4435f1e1722cab71551d85cd296440f8e92ed72b7a`
- `Formalization/ModelFree/TDSourceFirstFreedmanUnion.lean`: `223457e58b420df3a2822125ab1097044211e39bdeb683ef60c184f4a8f54eeb`
- `Formalization/ModelFree/TDSourceFirstFreedmanComparisons.lean`: `a29ae10bee6e96d4f98f3dec3a64a01373e6b68e7808ea7ab269d1a656b81995`
- `Formalization/ModelFree/TDSourceFirstFreedmanAssembly.lean`: `15dd0b646592e456c8337f3f318cf8e1b721d3bdd9f55270f008f6debdb962c5`
- `Formalization/ModelFree/TDVarianceLemmaComposition.lean`: `48a16fd5c5c8adf37af4550032dfa1388058c3d27dc571492b8b4c541b90bdf1`
- `Formalization/ModelFree/TDInitialErrorContraction.lean`: `2a95be0921d9262d45f0dc0e8a24de3ed7d18c8a53c2d42f08a450f884a1eb30`
- `Formalization/ModelFree/TDSourceFinalScalarArithmetic.lean`: `7e58e659c1a83b4b33e149e04aa04c077de5668f3602f8e99fc7bba8000a3992`
- `Formalization/ModelFree/TDSourceFinalScalarBudgetBridge.lean`: `b10542da0532c8c9868643731f7770ad4d972673c6a820716152cc72849e88f6`
- `Formalization/ModelFree/TDSourceFinalScalarBudgetConsumer.lean`: `dfe035f37dcb83af43406fa3cfcb1e321b874e6cf8b12aa66b92c3d42a0ad597`
- `Formalization/ModelFree/TDSourceFinalAccuracyComposition.lean`: `3b764f48fe4f27c8c6c0ec320bd029eb43ceac8ed40b51269a79f3e8bc0b7fbb`
- `Formalization/ModelFree/TDSourceFullAccuracyUniversal.lean`: `1bcc96d2b7dd6af07196a404e30ba9169df2227ae754c317b9ff4880bce4f6d5`
- `Formalization/ModelFree/TDSourceSamplingDefinitions.lean`: `c7a55219c10f2e4f76b317a199aead2115fd24dd1d80c3ee5b4a76e9cc136a63`
- `Formalization/ModelFree/TDSourceSamplingProjection.lean`: `75b995e0bb0afd5520d6f8e31d2ecc8f2a184d24ed38d0fb6c2c682f770d3a99`
- `Formalization/ModelFree/TDSourceAccuracyExactSamples.lean`: `7afd0996fff921fdc91f22e53aad673e6485aa8dfffd472faf8d6b687e67f375`
