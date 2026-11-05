# Independent source review and fresh-build record: fixed-value comparator chain

## Scope and bound inputs

This review covers the five staged sources listed below, at the exact SHA-256 values supplied for review. It checks the mathematical/source correspondence of the deterministic fixed-value increment, actual conditional moments, history transfer, predictable-variance cap, and residual absorption interface against `source/upstream/tex/chapters/generative_model_model_free.tex`, especially the robust comparator argument at lines 1630–1684 and its referenced weight/range definitions. It does not approve these drafts for production or claim the missing concentration theorem.

| Draft | Reviewed source SHA-256 |
|---|---|
| `QLearningChiResidualUpperDraft.lean` (private staged draft, not shipped) | `8ffc72ddee531e1eabfd87d6a4b929b23cfd8d60024aa1318aa07d5db6a90dca` |
| `QLearningChiStochasticInterfaceDraft.lean` (private staged draft, not shipped) | `473970b3fea18f59461bfb59db99c20c6441289961864ed614da963e6ed87040` |
| `QLearningChiFixedValueMomentsDraft.lean` (private staged draft, not shipped) | `2ecb71cc994ac48b5853c99e471574a61fec7b91493b02e02f8ec9f26dfc5857` |
| `QLearningChiFixedValueHistoryDraft.lean` (private staged draft, not shipped) | `e0503045ad5f3a5d36df2e7f9fb2e69487d9813fb5bb50877086671345d21ace` |
| `QLearningChiFixedValueVarianceDraft.lean` (private staged draft, not shipped) | `4941863e949b8f8c5661cbd2ff386406f99e828f6a1c6f89493bd2dac162f15b` |

Source hash: `7f4eb058e00480bc0694cac93ac41e22f4cfe48aa58a00c4ccf909f805e60b22`.
The imported source-parameter bridge compiled in the fresh audit at `QLearningChiSourceParametersDraft.lean` (private staged draft, not shipped), SHA `f59901a3a4893d67f1df9f064b40c1aecd5c27c9ac7cbaae2903175e93b09e4e`.

## Source correspondence

The source defines, for a fixed terminal update `u` and deterministic comparator value `V`, increments

`Z_i = γ η_i^(u) ((P_i-P)V)(s,a)`

only for `floor(T/2)+1 ≤ i ≤ u`. In the project sample-array convention, update `i=n+1` uses the row sample at coordinate `((s,a),n)`. The draft's active guard `n<T ∧ T/2<n+1 ∧ n+1≤u`, its exact `qPositiveWeight η u (n+1)`, and its zero padding elsewhere implement this correspondence. The project's `qPastSigma T n` observes sample coordinates strictly below `n`; thus it is the source's history before update `n+1`, while the fresh row at coordinate `n` remains unobserved. The finite product law has the actual transition row as that coordinate's conditional distribution.

The source weight is `η_i^(u)=η_i ∏_{j=i+1}^u(1-η_j)`. The draft calls the same quantity `qPositiveWeight`; the active-sample reindex maps `n` to `i=n+1` and uses the explicit premise `u≤T`. The schedule cap is

`qSourceLateCap γ c₂ T = min 1 (2 log(T)^3 / (c₂ (1-γ) T))`,

matching the source's `\barη`. The inherited schedule lemmas prove the squared-weight budget from the actual schedule, rather than postulating it. The fixed value is a function `State → ℝ` with no sample-data argument, which is essential: its row variance is deterministic, so the conditional square can be identified with a constant and transferred by the tower property.

The moment layer derives zero mean and exact true-row variance under the actual fresh-sample law. It transfers the moments to the increment-generated strict history after proving that history is contained in the used data prefix. The variance layer combines active and inactive terms over exactly `range T`; its identity is `γ² (Σ_active weight²) Var_P(V)`, then the source schedule gives the `γ² \barη Var_P(V)` bound. The magnitude cap uses a pairwise span assumption `|V(x)-V(y)|≤H`, and bounds a centered draw by that span. This accommodates shifted robust comparators; it does not incorrectly assert that their values themselves lie in `[0,H]`.

The residual file consumes the actual constructed robust fixed points, their fixed-point specifications, their pairwise range bound, and the proved residual inequalities. It establishes the source residual upper bound and deterministic domination of the displayed stochastic radius for both signs. The interface defines the both-sign radius event and absorption event and proves pointwise set inclusion. This is only deterministic absorption: the interface contains no theorem bounding the probability of the radius event.

## Findings and limitations

The reviewed declarations are source-faithful for this deterministic layer, subject to their explicit assumptions (`T≥2`, `u≤T`, positive `c₁,c₂`, exact rate schedule where the cap is invoked, and pairwise comparator span). The indexing and filtration are consistent with source updates `i=n+1`. The drafts retain the actual transition rows and do not introduce an independence assumption beyond the existing finite product sampling law. The inactive and `n≥T` padded increments are zero.

There is no proof here of the radius event probability, Freedman application, finite row/time/sign union bound, or final Q-learning sample rate. In particular, `qChi_radiusEvent_subset_absorptionEvent` alone is not the high-probability source claim. The source's two signs require allocating failure probability across both signs and all `SA` rows and late terminals (for example, per scalar call `δ/(2SAT)`); the probability argument remains a separate obligation. These files also do not prove comparator closeness/stability (Lemma 4.10(ii)).

No forbidden placeholders (`sorry`, `admit`, or custom `axiom`) occur in the five reviewed source files. This is not a claim about uninspected downstream consumer files.

## Independent isolated build and axiom probe

A fresh serial build was performed in an isolated local audit directory (not shipped), using its private output directory and the previously isolated reviewed dependencies. The source-parameter bridge and all five exact target files compiled with exit status 0. Fresh `.olean` SHA-256 values:

| Module | Isolated output SHA-256 |
|---|---|
| `QLearningChiSourceParametersDraft` | `d933b894f1af0ec1dac01d80c7bad6941d5e9774e1e0631fcb1527a3991fc4a9` |
| `QLearningChiResidualUpperDraft` | `f24637b9e5011916503922d75cfa826c44ed5affed23d9b9111790eb0dc5afbe` |
| `QLearningChiStochasticInterfaceDraft` | `db051bdcbf7d683ce37498c0cdf167d83c982a311720dd744d9c4fb5f0b2641d` |
| `QLearningChiFixedValueMomentsDraft` | `6ccce42a9c120fc906b6efb59121bbef157e0e3c3750e77cdf5ab38c988d19bf` |
| `QLearningChiFixedValueHistoryDraft` | `1cb00642a727cad1faeedb4a5c22261acb27fb63dee9531ed1cb915bfc0c4c79` |
| `QLearningChiFixedValueVarianceDraft` | `f81c2e8f97d23e80e0f50737b20a86b6241e373061de9f8dd12e9519e72a8fb9` |

The fresh import-only probe is `QLearningChiFixedValueChainImportAudit.lean` (in an isolated local audit directory, not shipped), SHA `e755cb69784ef4d9dff2b0fa5213182099f854abb5e6470e1e35c82ab98d59a8`. It imports the variance module and probes all 27 exports across the chain. The resulting `axioms.log` SHA is `6f5afcda259c302ef08671779ad2bc4fee968dedf12c8acdc418932958cf4c0a`; every listed declaration depends only on `[propext, Classical.choice, Quot.sound]`. This independent probe covers the exports printed by that audit file; it is not a blanket audit of every transitive project declaration.

## Disposition

Independent review supports the fixed-value moment/history/variance and deterministic absorption statements at the bound hashes above. Keep them staged until the missing probability theorem and integrated source-facing checks are completed. The allocated compiler slot is released.

## Production integration

The reviewed residual-upper, deterministic interface, fixed-value moments, history and variance-budget results are integrated as the corresponding `Formalization/ModelFree/QLearningChi*.lean` modules. The probability event remains a separate obligation for this batch. The declaration and proof bodies match the reviewed staged source; imports and status comments were updated where required. The full project check compiled 258 modules and audited 3,407 project declarations, allowing only `propext`, `Classical.choice`, and `Quot.sound`.
