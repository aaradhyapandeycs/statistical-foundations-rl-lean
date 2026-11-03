# Actual empirical continuation value: future factorization and independence

Stable staged `.local/FiniteHorizonEmpiricalContinuation.lean`, SHA-256 `4cdf6cc568915df0ab34ff2fff63f025f851cbe8231ab888a73939b4a39c29dc`.

Direct staged dependency: `.local/FiniteHorizonGenerativeSampling.lean`, SHA `c0e830fc8e3050ae0aadf8cfeec3c9d9209a72086d00a954ffa9e48024eb4e41`. Remaining imports are existing actual finite trajectory/optimality infrastructure and pinned Mathlib List/OfFn. The source target/dependency plan is `docs/source-finite-horizon-model-based-dependency-plan.md`.

## Source meaning and eleven exports

Source finite-horizon generative model discussion (chapter lines2546–2548) states that backward planning decouples later-stage continuation values from earlier empirical rows. This implementation proves the exact needed **continuation after current stage h** statement; it does not assert that the stage-h value is independent of its own stage-h transition rows.

`empiricalStages E N hN data` is `List.ofFn` of the actual empirical environment array, in chronological order. `empiricalStages_length` proves length exactly H. `empiricalContinuationValue` is defined as the actual expected finite trajectory return of the backward-optimal empirical policy on the environment suffix obtained by dropping h.val+1 stages. It is therefore the source next-stage optimal value at source stage h+2 when h.val is the current zero-based stage. At current final stage H−1 this is the terminal continuation.

`empiricalContinuationValue_eq_optimalValue` proves equality to the established backward optimal value via the actual trajectory bridge `EnvironmentStage.greedy_trajectoryValue`. Existing production `greedyStages_drop` also identifies this suffix greedy policy with the corresponding suffix of full backward planning. No independent Bellman/optimality conclusion is assumed. `empiricalContinuationValue_terminal` proves exact zero continuation at the last stage, using actual empty suffix trajectory semantics.

`empiricalStage_eq_of_data_eq` proves that agreeing current-stage observation rows give equal complete empirical environment stages, including unchanged known reward and transition distributions. `empiricalStages_drop_eq_of_future_eq` lifts equality of every strictly-later-stage observation to literal equality of the chronological empirical suffix list, before applying any value function. Its List/Fin index proof checks that each suffix position corresponds to a valid stage strictly larger than h, with no default or terminal extrapolation.

`completeFutureData h N x code` retains the exact supplied strictly-future observations and fills all current/past observations with an arbitrary fixed x. `empiricalContinuationValue_factors_future` proves the actual value vector is unchanged by this reconstruction. It does not assume factorization or equality of empirical models; models can differ arbitrarily on the discarded past/current stages.

`empiricalContinuationValue_measurable` proves the actual trajectory-valued map measurable on the finite discrete full-data experiment. Finally `empiricalContinuationValue_indep_row` composes the proved factorization with genuine future-block/current-row independence. Its conclusion is independence of the actual empirical optimal continuation **vector** from all N current stage/state/action row observations under the same true product sampling law. The arbitrary filler x is obtained from the current environment stage's existing nonempty-state evidence; it is not a random/data-dependent filler. No new nonemptiness or independence premise is introduced.

## Boundaries and limitations

H and N are arbitrary naturals in the underlying sampling foundation. Here actual empirical rows require N>0, and h:Fin H ensures a genuine current stage. H=0 has no such stage, while H=1 has the correctly proved zero continuation. The same original E, rewards, samples and sample law occur throughout. No discount, stationary kernel, tie gap or large-cardinality assumption is used.

Only the canonical empirical optimal **value** and its actual backward-optimal trajectory realization are handled. An arbitrary empirical optimal policy has the same suffix value only after the relevant all-states/all-stages optimality equivalence is proved; its selected actions may depend on past data, and no such policy independence is asserted here. The next stochastic ingredient can apply random-family Bernstein to this actual future-dependent continuation vector and current-row sample law. No finite-horizon probability radius, H³ sample rate or full `Thm:sample-compl-finite` result is claimed.

## Validation

Fresh exact staged sampling dependency compiled to isolated `.local/finite-horizon-build` artifacts. Focused new-source compilation succeeded. A final exact-source-copy `.local/finite-horizon-build/ContinuationAudit.lean` appended all11 definition/theorem axiom probes; it compiled exit0 without diagnostics, and every export reported only `propext`, `Classical.choice`, `Quot.sound`. The added terminal case was repaired using a length inequality to avoid rewriting dependent Fin H carriers; the final audit has no admission or `sorryAx`. Dependency artifacts were preserved and the compiler slot released immediately after completion.

Pending independent source/semantic review, qualified production integration and actual imported-export/project validation. Full sharp finite-horizon proof sourcing remains separate as recorded in the dependency plan.
