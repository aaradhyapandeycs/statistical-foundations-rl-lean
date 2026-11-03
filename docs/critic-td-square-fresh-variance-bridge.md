# Independent critic review: TD square fresh-variance bridge

Status: source review and fresh isolated build completed for the exact staged files below. These remain quarantined drafts and are not production proof evidence. This note does not claim the full source square-martingale result.

## Hash-bound scope

| Artifact | SHA-256 |
|---|---|
| `.local/TDSharpFreshVarianceBridgeDraft.lean` | `34686d029e51a1739ae0891095e4212208a56ac5693882a65afc401583d308cc` |
| `.local/TDSharpLateWindowDraft.lean` | `e353b996e0b2e44920863d0f01dffbcfb04480a88360a35223865f6a63850df5` |
| `.local/TDSharpVarianceDraft.lean` | `c02b90230640c79603e38a7f8b7a0211537ab341c3b27f289b06099292e0845a` |
| `.local/TDSharpMartingaleDraft.lean` | `eeeee6f405bcc819cb4d609dc9fb83bc27fbc4e15612506502a27ab535961c68` |
| `.local/TDVariancePairwiseDraft.lean` | `eddac49017762311a11b0f86590414c8d21ed6279cff2d7b0df2b792c5bea022` |
| `.local/TDSharpEnergyDraft.lean` | `258e5936a583596c682b02682944aaf72da2e6ed26952dbe212c2e8b63f4d50d` |
| `Formalization/ModelFree/TDSquareEnergy.lean` | `8b846ebc5738515e18a9c5e6cff8a043ae9adf84ec6b0baa804fa9675c40a3be` |
| `Formalization/ModelFree/TDConditionalMoments.lean` | `82c1ad9cf6e8ae6f12173255af3ecbc29fd3c179334922073b80c010cfd45f7b` |
| `Formalization/ModelFree/TDLinearRowVariance.lean` | `0bffeb5bb20a5219933a04edd12ad18b9a24e03cefc4a00ebf3308d5bc5c7214` |
| Source `generative_model_model_free.tex` | `7f4eb058e00480bc0694cac93ac41e22f4cfe48aa58a00c4ccf909f805e60b22` |

The independent outputs and source are in `.local/td-square-fresh-variance-independent-review/`. Fresh serial compilation succeeded (exit 0; empty diagnostics) for the variance helper, late-window wrapper, and fresh-variance bridge. Their output hashes are respectively `936274a6f87934ef9154aff0871970c06fd978c50953a269358d26ed73eace78`, `39f4151914e5aece68b1ec01ff5632a88b435c1eed2ebd9dad883d2d06b10dda`, and `f3fb9945a60c1726a8a82855cc064776dfab03b7500c8689ff91299310ee3c63`. `ImportAudit.lean` imports the exact late-window and bridge objects and probes all 16 exported declarations. It compiled successfully; all 16 report exactly `[propext, Classical.choice, Quot.sound]`, with no project-specific axiom. No production object was overwritten.

## Source review

The source variance estimate is Appendix C.2, source lines 2423–2445: conditionally, `Var(V_k²) ≤ 4 H² Var(V_k)`, and the affine TD update contributes `η_k² γ² Var_{P^π(s,·)}(V_{k−1})`. The separate terminal-window statement is source lines 685–691: `floor(t/2)+1 ≤ k ≤ t`.

The bridge matches the actual synchronous sample convention. `TDSamples` uses coordinates `(s,k)` with time zero unused; update `k` reads that coordinate, and `tdPastSigma T (k−1)` contains only sample times through `k−1`. The draft identifies the update with `tdSquareFreshUpdate` at the actual `(s,k)` coordinate, and its conditional expectation is taken under the actual `M.policyTransition π s` row. The freshness helper is instantiated with `t=k−1`, so its `t+1` coordinate is exactly `k`. There is no full-support assumption and no replacement of the true transition row by a surrogate law.

With positive-time rates in `[0,1]`, initial values in `[0,H]`, source MDP reward/discount bounds, and `1≤k≤T`, the update remains in `[0,H]`. The bridge proves the centered-square conditional second moment equals the true-row variance of the squared fresh update, bounds it by `4H²` times the fresh-update row variance, and separately proves the affine row-variance identity with coefficient `(η_k γ)²`. Thus the two source factors are available by composition, but the bridge does not export one combined theorem whose right-hand side is already `4H²η_k²γ² Var_{Pπ}(V_{k−1})`.

The late-window wrapper maps Freedman index `n` to update `k=n+1`, filters `floor(t/2)≤n<t`, and proves the zero-padded sum equals the source interval sum; `t=0` is handled as an empty sum. Its reindexing identity is stated for arbitrary `t`, not under `t≤T`; a consumer applying the fresh-update variance theorem still has to supply the source horizon bound. This is a scope condition, not a flaw in the algebraic sum identity.

## Limitations and recommendation

This build does not prove that centered-square observations at distinct states have zero conditional covariance. The raw TD-noise cross-covariance result does not establish this square-specific fact; a consumer must separately expand the product of centered squares, including linear-square and square-square terms, against the joint fresh-indicator law. Nor do these files prove the source Freedman bound or final TD error theorem. Keep the drafts quarantined until that covariance dependency and the downstream concentration chain are independently established.

## Production integration

The reviewed source-window wrapper, TD square-variance definitions and actual single-state fresh-variance bridge are integrated as the corresponding `Formalization/ModelFree/TDSharp*.lean` modules. Declaration and proof bodies match the reviewed staged sources; imports and status comments were updated where needed. The full project check compiled 272 modules and audited 3,576 project declarations, allowing only `propext`, `Classical.choice`, and `Quot.sound`.
