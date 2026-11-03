# Independent review: absorbing grid and source value cover

**Verdict: PASS for the complete named `LemValueCover` environment and the stated deterministic grid/logarithm prerequisites.** This is not a proof of the subsequent leave-one-out independence or policy-learning sample theorem.

Reviewed `.local/PolicyLearningAbsorbingGrid.lean` SHA-256 `9eb3bb60ee40b35f5c3fb378c1db43edc0d1648d1d230c0b06b5be028063e9ef` and its builder handoff against `source/upstream/tex/chapters/generative_model_model_based.tex:1280–1302, 2620–2629`, including the whole named lemma `LemValueCover`; source SHA-256 `b7e7abfb2c2cb2c0dd82470db5ecac3a67d7163682246d499935d9130214ac4d`.

## Exact grid and quantifiers

For positive natural `N` and the model's `h=1−γ>0`, the definitions give the exact source mesh `η=1/(Nh)` and parameter points `i/(Nh)=iη`, indexed by `i : Fin(N+1)`. The proofs establish every point is in `[0,1/h]`, identify both endpoints `0` and `1/h`, and use the positive denominator to prove injectivity and hence exactly `N+1` distinct parameters. `absorbingGrid_covers_interval` uses `⌊uNh⌋₊` for every `u` in the **closed** source interval; the upper endpoint is included, as are `N=1` and `γ=0`. No extraneous γ lower bound or accuracy hypothesis is introduced.

The parameter set computed from an empirical model is definitionally equal to that from the original model because it depends only on `N` and the unchanged discount. Thus the parameter grid is fixed before sampling. The actual absorbing value vectors indexed by these distinct parameters are also proved injective: evaluating at the absorbed state returns the parameter for every policy. Consequently this particular value family has exactly `N+1` members. The generic image theorem separately allows duplicate values under an arbitrary map; the cardinality proof does not conflate those two cases.

## Named lemma and empirical object

`absorbingGrid_covers_optimalValue` first takes the original actual optimal trajectory value at `x`, whose source interval bounds are proved by the existing trajectory API. The independently reviewed preservation theorem identifies the whole actual optimal trajectory value of the absorbing model at that parameter with the original value. The independently reviewed fixed-parameter Lipschitz result bounds the value difference to the grid point by the scalar parameter difference, and the floor-based grid cover bounds that by `η`.

`empirical_absorbingGrid_covers_valueEstimator` instantiates the preceding theorem for **each actual sample table** in the algorithm's empirical MDP. The imported empirical value identity matches `valueEstimator`, the trajectory value of the empirical optimal greedy policy, and its right-hand vector is the optimal trajectory value of the correct `x`-absorbing empirical model at that grid point. The witness is an index in `Fin(N+1)`; `absorbingGridPoint_mem` proves its parameter is in the source finite set. Thus, for every sample and every state x, there exists a source-grid parameter with sup-norm distance at most `1/(Nh)`: the exact quantifier order, endpoints, constant and conclusion of the full named lemma are present, with no assumed preservation or closeness premise.

The witness may depend on the full data. The file does **not** assert it is independent of the removed row. A subsequent proof must first establish the simultaneous fixed-grid concentration event using the separate reviewed fixed-u independence result, then select this witness within that event. Nothing here proves the subsequent all-row concentration or sharp policy-learning theorem.

## Source β comparison

For a nonempty finite-family size `k≤N+1`, `N>0`, and `δ>0`, the log lemma proves

```text
2 log(4k/[δ/(2SA)]) ≤ 2 log(16SAN/[(1−γ)δ]).
```

The left side is the existing Bernstein-family log with the source's per-row confidence allocation; the right side is the source β₁. The proof uses `N+1≤2N` and `0<1−γ≤1`, with positivity of `S,A,δ,k` for the logarithms. It is an algebraic comparison, not a probability union. It remains applicable if a later family has fewer distinct values, although the particular full absorbing-value grid is injective as proved here.

## Verification and limits

The unchanged staged source, retaining its production imports, was independently copied to a temporary directory with axiom probes for all 22 definitions and theorems and compiled with `bash scripts/lean-local.sh <temporary-probe>/policy_learning_grid_independent_audit.lean`. The compile passed without diagnostics; each probe reported only `propext`, `Classical.choice`, and `Quot.sound`. No `sorry`, `admit`, or custom axiom appears in the staged source. The integrated Lipschitz and preservation dependency hashes match the builder record: respectively `65c20456263f0ce790b7da68951776a01bc08dcd313ed09f6da07c7f25f361fe` and `883eb9411a0f9aadad8631346a3d5149d256a6fa610d1c769b4d66070c06bb71`.

This independently reviews the staged named-environment correspondence and exact source; the future production copy still requires byte comparison, actual export build, and imported axiom verification. No claim about the full monograph or statistical policy-learning theorem follows from this review.

## Integrated export verification

Production `Formalization/Generative/PolicyLearningAbsorbingGrid.lean` has SHA-256 `9eb3bb60ee40b35f5c3fb378c1db43edc0d1648d1d230c0b06b5be028063e9ef` and was confirmed byte-identical to the reviewed staged source. `lake build Formalization.Generative.PolicyLearningAbsorbingGrid` passed, rebuilding its project-owned import closure; it did not rebuild pinned dependencies. A separate probe importing the **actual production module**, with `#print axioms` for all 22 actual exports, compiled successfully; all 22 reported only `propext`, `Classical.choice`, and `Quot.sound`.

The source inventory identifies `LemValueCover` as **Lemma 3.4**, lines 1292–1300. Its entire named environment contains exactly the existence of a grid parameter for each state with the displayed sup-norm bound. The production export `empirical_absorbingGrid_covers_valueEstimator` supplies the equivalent indexed witness `i : Fin(N+1)` for every actual sample and state; `absorbingGridPoint_mem` proves the corresponding scalar belongs to the source grid, and `absorbingGridValue` is the corresponding actual absorbing-model value. The source's preceding discussion of independence and subsequent concentration are outside this named environment and are not claimed by the cover theorem. The focused Lake build noted above rebuilt only project-owned modules in this import closure; pinned dependency artifacts were preserved.
