# Finite-horizon generative sampling foundation

Stable staged `.local/FiniteHorizonGenerativeSampling.lean`, SHA-256 `c0e830fc8e3050ae0aadf8cfeec3c9d9209a72086d00a954ffa9e48024eb4e41`. It imports only production finite optimal-trajectory/empirical-row infrastructure and pinned Mathlib independence. No staged proof dependency is required.

Source-first target/dependency plan: `docs/source-finite-horizon-model-based-dependency-plan.md`. Relevant pinned chapter locations are `eq:defn-empirical-P-finite` and the algorithm at lines2526–2548, then `Thm:sample-compl-finite` at2551–2575; chapter SHA `b7e7abfb2c2cb2c0dd82470db5ecac3a67d7163682246d499935d9130214ac4d`.

## Completed definitions and theorems

All18 exports live in `StatisticalRL.FiniteHorizonGenerative`. The true nonstationary environment is an array E:Fin H→EnvironmentStage State Action. Its stage0 corresponds to source stage1; there are exactly H decision stages. It does not impose stationary or discounted-model structure.

`SampleIndex` and `Samples` index all observations by `(Fin H×State×Action)×Fin N`; `sampleIndex_card` proves exact total cardinality H·S·A·N. `samplingLaw` is the actual independent product of each true stage/state/action transition row measure, with a probability-measure instance. `samplingLaw_marginal` and `samplingLaw_independent` establish actual complete-coordinate law/independence, not merely pairwise independence. `samplingLaw_row` proves the complete N-sample row pushforward equals the actual iid row product law by injective coordinate restriction and all coordinate marginals.

`empiricalStage` uses the actual N row observations and finite frequency distribution; its known reward and [0,1] bounds are copied unchanged from E h. `empiricalStage_reward` is exact function equality. `empiricalStage_transition_expectation` proves its actual empirical expectation is N⁻¹ΣV(data(h,s,a,i)). This stage has exactly the existing EnvironmentStage carrier needed by the proved finite trajectory/optimality APIs; it does not introduce an assumed optimal value or claim a new trajectory bridge.

`futureIndices` contains precisely stages strictly larger than h, and `rowIndices` contains all observations of current row(h,s,a). `FutureCode` and `futureData` restrict the actual data to that finite future block. `future_disjoint_row` proves the coordinate blocks disjoint. `futureData_indep_row` uses full independent-product block independence, followed by the exact current-row extraction; the complete future block is independent of the complete N-sample current row. This is valid at the last stage, where the future block is empty.

`futureStatistic_indep_row` composes with any deterministic statistic actually defined on that future code. Its measurability follows from the finite discrete code carrier; no measurable-statistic or independence conclusion is assumed. The final codomain can have an arbitrary measurable structure. This does **not** assume or claim an arbitrary data-dependent policy/value factors through that code. The next task must prove that canonical empirical optimal continuation values depend only on later stages; only then can this generic composition be instantiated with those actual values.

## Boundaries, source scope and missing theorem

Raw sampling laws and independence lemmas allow H=0 and N=0, which produce an empty observation-index product when appropriate. Empirical stages require N>0 for actual normalized frequency rows; their h:Fin H prevents fictitious stages when H=0. The intended finite sample theorem's 0<ε≤H implies H>0. No artificial large S/A/H restriction or discount parameter occurs. Source rewards remain fully known; stage transitions can differ arbitrarily.

This is a bounded foundational prerequisite. It does not prove fitted-value suffix factorization, finite random-family Bernstein event, simulation-error telescoping, sharp H³ per-row rate, all-tie performance guarantee or the source theorem. The pinned chapter refers full finite-horizon proof details to Li–Wei–Chi–Chen OR2024; the full external proof is not locally pinned here and must be checked against exact unperturbed planning/tie scope before a source-derived full proof graph is certified. The separate source-first plan records those obligations and the δ>0/H/ε boundaries.

## Validation

`bash scripts/lean-local.sh .local/FiniteHorizonGenerativeSampling.lean` compiled exit0 with no diagnostics. An exact-source-copy `.local/FiniteHorizonGenerativeSamplingAudit.lean` appended axiom probes for all18 aliases/definitions/instance/theorems; it compiled exit0 without diagnostics. The two initial aliases have no axioms, and all other exports use only `propext`, `Classical.choice`, `Quot.sound`. No placeholder/custom axiom or dependency artifact mutation occurs. Compiler slot released immediately after completion.

Pending independent source/semantic review, production integration and actual-export/project checks. No finite-horizon statistical theorem completion is claimed.
