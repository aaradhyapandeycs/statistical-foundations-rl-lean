# Independent source review: fixed-row Q-learning V* Freedman event

Reviewed the final staged sources reported by `docs/builder-q-learning-optimal-freedman-plan.md`:

- `.local/QLearningOptimalPredictableVarianceDraft.lean`, SHA-256 `195ecfb780926c2072d2d0770284fefb1cf5129e46469ad81859c6c6b967eee5`.
- `.local/QLearningOptimalFreedmanDraft.lean`, SHA-256 `4d9b33160de315f6fe613f0b8fca20359e104132798685ed2aa8073799c2f8bb`.

The current sources match those handoff hashes. This is an independent source review; fresh compilation and axiom probing are now complete and recorded below.

## Source semantics and quantifiers

The variance module uses the actual fixed-(V^\star) Q-learning fluctuation on the actual finite product sample law. The active zero-based layer (t) satisfies (t<T), (T/2<t+1), and (t+1\le u\le T), so its source update index is (i=t+1) and its sampled row is the actual array coordinate `i−1=t`. It conditions on the strict history through that layer. Inactive layers (including (t\ge T)) are zero and have zero conditional square.

For active layers, the source history bridge gives the conditional square ((\gamma\eta_i^{(u)})^2\operatorname{Var}_{P_{s,a}}(V^\star)) under the increment's own prior-increment sigma algebra. The value is the actual optimal-greedy trajectory value, fixed before sampling. The finite sum `historyPredictableVariance` is therefore, almost everywhere, exactly

`γ² · Var_P(V*) · Σ_{i=floor(T/2)+1}^u (η_i^(u))²`.

The active-square reindex uses the already reviewed (t\leftrightarrow i=t+1) equivalence and `u≤T`. The source schedule and positive-weight telescope derive the actual squared-weight cap; the variance theorem does not assume a target variance budget. The deterministic budget is (\gamma^2\bar\eta\operatorname{Var}_P(V^\star)), nonnegative because it is a true transition-row variance. No bounded-initialization or rate-dependent true-variance assumption is needed for this fixed-(V^\star) identity.

The Freedman wrapper has one fixed state-action row and one fixed terminal (u), under the actual complete Q-sample law. It explicitly requires `T≥2`, `u≤T`, positive `c₁,c₂`, the finite source schedule, `K>0`, and `0<δ<1`. It supplies the global all-layer increment bound (B=\gamma\bar\eta H), almost-everywhere predictable variance cap, and the natural increment-history centering/measurability already proved by the fixed-(V^\star) history module. Its event is for the actual source-indexed finite sum, via the exact reindex theorem. The threshold matches `freedman_natural_history`: `sqrt(8 * max(W_u, V/2^K) * log(2K/δ)) + (4/3) B log(2K/δ)`. This is a single-row/single-terminal event; there is no union over rows or terminals, no sharp (V^\pm) comparator, and no final Q-learning rate claim.

No semantic mismatch or hidden target-shaped premise was found. The fresh independent compile and axiom checks are recorded below.

## Prepared fresh compile audit

The audit is bound to the two hashes above. Rebuild the 24 staged modules below bottom-up in a new project-owned `.local` output directory, with repository production imports resolved from the existing `.lake/build/lib/lean` and package artifacts. Do not rebuild production dependencies. Then import `QLearningOptimalFreedmanDraft` and probe all nine declarations in the two target files:

`qOptimalVarianceBudget`, `qOptimalFluctuation_inactive_condExp_sq`, `qOptimalActiveWeightSquareSum`, `qOptimalActiveWeightSquareSum_eq_source`, `qRowVariance_eq_distribution`, `qOptimalRowVariance_nonneg`, `qOptimal_historyPredictableVariance_exact`, `qOptimal_historyPredictableVariance_le`, `qOptimalFluctuation_freedman`.

The staged build order is:

1. `QLearningIterateBounds`
2. `QLearningSynchronousSampling`
3. `QLearningCausalityDraft`
4. `QLearningConditionalMomentsDraft`
5. `QLearningPrefixFiltrationDraft`
6. `QLearningConditionalCenteringDraft`
7. `QLearningIndicatorConditionalDraft`
8. `QLearningIndicatorCondExpDraft`
9. `QLearningConditionalPulloutDraft`
10. `QLearningConditionalIncrementDraft`
11. `QLearningNaturalHistoryDraft`
12. `QLearningHistoryAdaptationDraft`
13. `QLearningIncrementCapsDraft`
14. `QLearningOptimalFluctuationDraft`
15. `QLearningOptimalFluctuationMomentsDraft`
16. `QLearningOptimalFluctuationHistoryDraft`
17. `QLearningOptimalFluctuationWindowDraft`
18. `QLearningOptimalLateBudgetDraft`
19. `QLearningWeightTelescopeDraft`
20. `QLearningSourceReindexDraft`
21. `QLearningLateRateScheduleDraft`
22. `QLearningSourceLateCapsDraft`
23. `QLearningOptimalPredictableVarianceDraft`
24. `QLearningOptimalFreedmanDraft`

The qualified production dependency `Formalization.Probability.FreedmanNaturalHistory` was already present in the project's production build and should be reused, not replaced by the similarly named unqualified staged draft. Its source SHA-256 is `7e1e189566bc48cd8551e8ce83c156d154f3c0cd07bf00bf9b78cdd410821b23`; it imports production `Formalization.Probability.FreedmanExactAssembly` (SHA-256 `8914080eb48351a84b53d23d361430e6b9b5beff9feda4b3af483517b56a5c4c`) and `Formalization.Probability.FreedmanVariancePeeling` (SHA-256 `010f97d59be568ea443fe38f40e51ac83b4cd95ebcde8f118bb3fb76935b15da`).

The exact target hashes were rechecked before compilation. All 24 staged modules compiled in the order above in `.local/q-optimal-freedman-audit-195ecfb7/`. All nine target declarations/definitions were probed; each reports only `propext`, `Classical.choice`, and `Quot.sound`. The qualified production Freedman imports were reused from existing project artifacts and not rebuilt. This focused check is not production integration.

Exact staged-source hashes used in the rebuild:

| Module | SHA-256 |
| --- | --- |
| `QLearningIterateBounds` | `594b96eede407a268bad69041146728a7456478c39c53990c53bef006a5b207e` |
| `QLearningSynchronousSampling` | `70dccffe5af0e7f824226c1d235257f4b0ea8e4ff7a5f9aaf8d9d1e06a830937` |
| `QLearningCausalityDraft` | `3eade75e34d1dc7c5a2f6e809e0fe2f8e7fe197ca2b288761df2078067276d37` |
| `QLearningConditionalMomentsDraft` | `ac450a4871fedcd8320e36c00d1379c2beaa385369b5fab08e709bbf4596176a` |
| `QLearningPrefixFiltrationDraft` | `266f86ca30a206f0bb471742970ca49013f04cf6326a29fd7d6ac0e02f26d30c` |
| `QLearningConditionalCenteringDraft` | `60daddba566a81f0d6ae72421153b0104bbde30e7efed60f0d0f1bc59dccdfc7` |
| `QLearningIndicatorConditionalDraft` | `2dc13db7db500f5128a9207e41dd98288a6df14c009d1799103726ad3ef03c76` |
| `QLearningIndicatorCondExpDraft` | `37defd8793aee4b50fcee3e16c576659411a98a51b7601506d041c1ef813936d` |
| `QLearningConditionalPulloutDraft` | `38362fac2b5eceea7d38dac6bb90b9b2f70b54d8001ceb69e0cc7d2d70efa939` |
| `QLearningConditionalIncrementDraft` | `37819b3b3e5114e277de9a124f2f5bdddffe0dfd679b92aa3948de30fb5483ab` |
| `QLearningNaturalHistoryDraft` | `841361faa2ba6d092b6f46ccb15e0bcda03d591e147f74b1f6d611de334b7ffd` |
| `QLearningHistoryAdaptationDraft` | `766309449c858a91456f82499c75e4de9c2af11fc8d6268f37f4e59815562c4f` |
| `QLearningIncrementCapsDraft` | `ca8a29d2bb7c1d60a8d52924da97df4d9011e5660eeb62be36d2df25edc154e1` |
| `QLearningOptimalFluctuationDraft` | `2bfbc447af7d3ca3616cd1c6abce92acf3d2fdacbf85655bcaa73923f2b14655` |
| `QLearningOptimalFluctuationMomentsDraft` | `c2fc20dace8514ce247f8928e8bcc3a138736b8bc77ce6a77d8a882a04707d97` |
| `QLearningOptimalFluctuationHistoryDraft` | `d05c9a25d561fc7d0df694e9eee00c979f1e3e964f8ab23e0672c63bb1693d6f` |
| `QLearningOptimalFluctuationWindowDraft` | `c9fe27f35cf462aff21cad39158ddd4a96af80eccf9d812ac3a878553a078f1a` |
| `QLearningOptimalLateBudgetDraft` | `a3bc86dcf25cbd91ddd7b089d67dd0b49b93931311abba0fc2982aa397dc6cb6` |
| `QLearningWeightTelescopeDraft` | `843652c1715876cd886a2612619e991bc5eaa4c6648278fc535417ef08e0dfda` |
| `QLearningSourceReindexDraft` | `fd294e8f541f63d6cf047d8a264027196fdfbeb87612f41dd1f73ea7a3d75226` |
| `QLearningLateRateScheduleDraft` | `685459d2eaecd6fda9e24d126d8947f9ea3c58c1194f9a18ddd163c097d6a494` |
| `QLearningSourceLateCapsDraft` | `2ab44ad698266be043b01d3985e388bfaa2eb9c90160dacf9bc951856d2befca` |
| `QLearningOptimalPredictableVarianceDraft` | `195ecfb780926c2072d2d0770284fefb1cf5129e46469ad81859c6c6b967eee5` |
| `QLearningOptimalFreedmanDraft` | `4d9b33160de315f6fe613f0b8fca20359e104132798685ed2aa8073799c2f8bb` |

## Production integration

The eight source-reviewed modules are now integrated under `Formalization/ModelFree/QLearningOptimalFluctuationWindow.lean` through `QLearningOptimalFreedman.lean`, with qualified imports and updated status comments. Its proof and declaration bodies match the reviewed staged source; imports and status comments were adjusted. The complete project check compiled 234 modules and audited 3,148 project declarations, using only `propext`, `Classical.choice`, and `Quot.sound`. This does not change the scope or imply the final source theorem.
