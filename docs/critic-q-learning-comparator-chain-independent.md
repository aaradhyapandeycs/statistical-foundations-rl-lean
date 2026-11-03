# Independent audit: comparator recursion through same-data probability sandwich

Status: source review plus fresh isolated compile and transitive axiom probe completed for the exact staged chain below. These are staged drafts; this does not certify production integration or the final Q-learning accuracy theorem.

## Exact hashes and independent build

| Artifact | SHA-256 |
|---|---|
| `.local/QLearningComparatorRecursionDraft.lean` | `5afb53aed98e0ff2e4997c9b30b4388804b454b55e601b9ec1644241a08ae2dd` |
| `.local/QLearningComparatorUnrollDraft.lean` | `bca8f09ad4448dfefb72345eefb062e1178b71a2dff8b0fd32a472117dfee72d` |
| `.local/QLearningComparatorSandwichDraft.lean` | `681229bc763fce35a7f8317f27e544c597000c4071372cd85f46e2d26841ef60` |
| `.local/QLearningComparatorSameDataDraft.lean` | `efbb587d08efabe00fa574b0b95692aeddc1bf156c6f6df2437d17ead17abe7b` |
| `Formalization/ModelFree/QLearningChiSourceRadiusUnion.lean` | `945cdc19f6fdf9a9755df5997f70c2a555ddcff45334ee2a4d66cc6a46c72948` |
| `Formalization/ModelFree/QLearningChiStochasticInterface.lean` | `6333498b596ebea6fa5792a104926a75e9d2935e2b1665f171114cfef587c71e` |
| `Formalization/ModelFree/QLearningSourceReindex.lean` | `f20d7d4ee17df8051ef0ad275d3b9bae0850292ce134abc004e307b18165a113` |
| `Formalization/ModelFree/QLearningSynchronousSampling.lean` | `7a815c6a48c98624649bdea4f53a9c69ef58c1a4209d5f2c1b2b468dbd7b820a` |
| Source `source/upstream/tex/chapters/generative_model_model_free.tex` | `7f4eb058e00480bc0694cac93ac41e22f4cfe48aa58a00c4ccf909f805e60b22` |
| Builder handoff `docs/builder-q-learning-comparator-same-data-draft.md` | `5ef3dcc33667acdf801dc15ae5bd47c4dfb05f61f8911fe1d216f3321d69e39f` |

A fresh serial build of all four exact staged Lean sources succeeded with exit 0 and empty logs. The outputs and logs are isolated in `.local/q-chi-comparator-chain-independent-efbb587d/`; no production artifact was overwritten. The fresh import audit imports the final SameData module and probes all 20 public exports across the four local layers. Each declaration reports exactly `[propext, Classical.choice, Quot.sound]`. The source files contain no `sorry`, `admit`, or `axiom` declaration. The final SameData source includes one proof-only reassociation repair (`ring` after the active-layer reindex simplification); no statement, assumption, sample coordinate, event, or confidence parameter changed.

## Source and mathematical review

The source correspondence is the update decomposition and cumulative fluctuation at lines 1564–1596 (`eq:Q-comparison-decomposition`), absorption at 1598–1614, the actual common absorption event at 1677–1683, and propagation/radius/sandwich at 1688–1739 (`eq:Q-comparison-radius`, `eq:Q-comparison-sandwich`). Source lines 1765 onward explicitly apply the analogous construction to the lower comparator. The source's final use of comparator-to-optimal stability and sample arithmetic remains downstream.

**Actual source update and both signs.** The first layer proves the actual one-step identities for arbitrary sample paths. The upper side uses `Q_t−Q⁺`, its correct `V_t−V⁺` continuation gap, centered `γ(P_t−P)V⁺`, and residual `Q⁺−r−γPV⁺`. The lower side is independently oriented as `Q⁻−Q_t`; it reverses the continuation and centered fluctuation and uses residual `r+γPV⁻−Q⁻`. The finite unroll retains the arbitrary warm-start error multiplied by `∏_{j=L+1}^t(1−η_j)` and uses source weights `η_i∏_{j=i+1}^t(1−η_j)`. It derives the residual coefficient `1−∏(1−η)` by the weight telescope; it does not assume the desired recursive conclusion.

**Propagation.** The plus and minus induction helpers consume the source cumulative absorption condition separately for each comparator sign and every strict-late terminal, residual nonnegativity, actual initial error-plus-residual estimates, and schedule rates in `[0,1]`. The actual wrapper proves the initial estimates and residual nonnegativity from in-range `Q₀`, robust shifted-comparator ranges, and production residual bounds. The contraction radius is derived by a scalar convolution identity. The resulting pathwise interval is `L≤t≤T`, where `L=floor(T/2)`; its warm-start endpoint uses the initial estimate without asking for a fluctuation event.

**Same-data indexing and law.** Q-learning source update `i` uses the zero-based product-array coordinate `i−1`. The fixed-value concentration increment is indexed by layer `n` and uses coordinate `n`; the bridge maps `i=n+1` and rewrites `qSamplesExtend ... (n+1)` to the actual coordinate `n`. Thus the product-law fluctuation and pathwise `ξ_t` agree pointwise on the same array. This is not a coupling or distributional equality. The source absorption event's index is `j:Fin T` with update `j.val+1`; for each pathwise terminal `t` with `floor(T/2)<t≤T`, taking `j=t−1` is valid and gives the identical source update. The absorption event's strict window and the sandwich's closed interval therefore align exactly.

The final probability statement uses the actual product law `qSamplingLaw M T`, and its Q iterates use `qSamplesExtend M T data` on that same `data`. The source radius event has two comparator signs, all `SA` coordinates, and all late terminals; its union allocation is `δ/(2SAT)` per sign-coordinate-terminal, yielding one common event of probability at least `1−δ`. The final theorem reuses this event once and applies measure monotonicity to the deterministic event inclusion; no second confidence split occurs. The radius is the source conversion `8·lateCap·log(4SAT/δ)`.

The theorem assumptions are `T≥2`, positive schedule constants, `0<δ<1`, the source finite rate schedule, and `Q₀∈[0,H]`. The schedule derives the positive-time bounds needed by propagation and is also the concentration premise. The initialization range is needed for the actual iterate bounds. The robust `hρ` witness supplies only the constructor's nonnegativity domain and is chosen before data.

## Scope and disposition

The audited staged chain proves a same-data, actual-law comparator sandwich with confidence at least `1−δ`, conditional on the project production dependencies used by the build. It does not prove Lemma 4.10(ii)'s robust-model stability estimate, the comparator-to-`Q*` distance, the final sample-budget/product-decay arithmetic, or the final true-optimal Q error statement. The build used already-built production artifacts from the pinned project environment; production-export verification and integration remain separate. No source mismatch was found in signs, update indexing, sampling law, confidence allocation, or deterministic assumptions.

## Production integration

The reviewed recursion, unroll, pathwise sandwich and same-data probability bridge are integrated as the corresponding `Formalization/ModelFree/QLearningComparator*.lean` modules. Comparator stability and the final error rate remain separate. Declaration and proof bodies match the reviewed staged sources; imports and status comments were updated where needed. The full project check compiled 272 modules and audited 3,576 project declarations, allowing only `propext`, `Classical.choice`, and `Quot.sound`.
