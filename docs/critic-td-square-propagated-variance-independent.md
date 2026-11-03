# Independent review: propagated TD square conditional variance

Status: exact quarantined draft independently source-reviewed, freshly
compiled, and axiom-probed. No production file was changed.

## Hash-bound scope

| Item | SHA-256 |
|---|---|
| `.local/TDSharpPropagatedVarianceDraft.lean` | `f7b909fadd1c4ded5bc22e831f5aa0bd151afdd8157f4fac714454993e072132` |
| `.local/TDSharpLateWindowDraft.lean` | `e353b996e0b2e44920863d0f01dffbcfb04480a88360a35223865f6a63850df5` |
| `.local/TDSharpSquareCovarianceDraft.lean` | `0391af8b931384927f28fb9abcff12ba363deb245e01f099f521bcaf2e93db54` |
| `.local/TDSharpFreshVarianceBridgeDraft.lean` | `34686d029e51a1739ae0891095e4212208a56ac5693882a65afc401583d308cc` |
| `Formalization/ModelFree/TDPropagatorRows.lean` | `da421810c1087e83b134d1781d4be3dcd430a9f6c7da5b4b4461460c3ef6884e` |
| `Formalization/ModelFree/TDLinearRowVariance.lean` | `0bffeb5bb20a5219933a04edd12ad18b9a24e03cefc4a00ebf3308d5bc5c7214` |
| `Formalization/ModelFree/TDSquareEnergy.lean` | `8b846ebc5738515e18a9c5e6cff8a043ae9adf84ec6b0baa804fa9675c40a3be` |
| `Formalization/ModelFree/TDConditionalMoments.lean` | `82c1ad9cf6e8ae6f12173255af3ecbc29fd3c179334922073b80c010cfd45f7b` |
| `Formalization/Probability/Variance.lean` | `541714ed6173402131bece633476308c1c832f31d0cbb46534cc55f48dcd9553` |
| Source `generative_model_model_free.tex` | `7f4eb058e00480bc0694cac93ac41e22f4cfe48aa58a00c4ccf909f805e60b22` |

The target is Appendix C, equation `eq:TD-square-martingale` (source line 690)
and the per-increment conditional-variance derivation in lines 2404–2444.
This review covers the six exports in the staged file, ending with
`tdSquareLateWindowIncrement_condExp_sq_le_sourceProxy`. It does not certify
production integration or a cumulative variance/concentration result.

## Source and semantic review

The source increment at update `k` is the centered square vector
`V_k ∘ V_k − E_{k−1}[V_k ∘ V_k]`, propagated by the deterministic product over
updates `k+1,…,t`. In the draft, Freedman index `n` maps to `k=n+1`. Its active
premises `t/2≤n<t` therefore give exactly
`floor(t/2)+1≤k≤t`, and its conditional sigma-field is
`tdPastSigma T n = tdPastSigma T (k−1)`. The fresh square coordinates have the
actual `tdSamplingLaw` and true policy transition rows; the source filtration
and the fixed terminal are explicit.

The row is not supplied as an arbitrary weight vector in the final theorem.
It is `tdPropagatorRow M π η k t q`, identified by the actual chronological
propagator. The imported row lemmas prove nonnegativity and exact mass as the
contraction product over `k+1,…,t`; under the explicit positive-time rate
bounds, that mass is at most one. The helper row theorem uses only the
mathematical sufficient premises `u≥0` and `sum u≤1`. It derives `u r≤1` by
single-term domination, then `u r²≤u r`. Thus the needed diagonal reduction
does not assume a target-shaped estimate about the source random variance.

The exact conditional second-moment expansion has diagonal terms
`u(r)^2 Var_{Pπ(r)}(U_{k,r}(X)^2)` and zero off-diagonal terms from the
square-specific covariance theorem. The fresh-variance bridge proves
`Var(U²)≤4H² Var(U)` on the actual `[0,H]` interval and identifies the affine
fresh-update variance as `(η_k γ)^2 Var_{Pπ(r)}(V_{k−1})`. Finally the draft
uses the explicit premise `η_k≤barη`, plus nonnegativity of `η_k`, to obtain
`η_k²≤barη η_k`. This matches the source factor
`4 H² barη η_k γ²` in the source proxy, with `H=1/(1−γ)`. In the paper,
`barη` is instantiated by the late-time step-size bound at equation
`eq:defn-bar-eta-large-k-TD`; the Lean theorem exposes that bound as the
explicit premise `hbar` instead of hiding it in the theorem.

The centering needed to read the conditional second moment as a conditional
variance is supplied by the imported staged martingale theorem. The final
export itself states the conditional second-moment inequality. No full-support
or positive-atom premise is introduced. The proof does not establish the sum
over the late window, the deterministic cap on `W̄_t`, Freedman concentration,
or the final TD error/rate theorem.

## Independent build and axiom evidence

The exact target compiled with the pinned `.local/lean` into the fresh isolated
directory `.local/td-square-propagated-variance-independent-f7b909fadd/`.
`compile.log` is empty. The target artifact SHA-256 is
`fed908a3546f26038210808010033a5ad713a46e0237dd37d66b170e2f37fa3d`.
The separate six-export probe source has SHA-256
`b50a00bd8cd8e8fbd7df585be62d70c3c0f8a0279d0c9c08b04cb8ac695a1d64`; its
compiled artifact SHA-256 is
`d9ba49783a4d8a3f3091b22ed54e0fe1e4e7793bc4ab0163d1ae44b8f070abdf`.
Every export reports only `propext`, `Classical.choice`, and `Quot.sound`.
The exact target and probe contain no `sorry`, `admit`, or custom `axiom`.

The isolated `LEAN_PATH` used the fresh output directory, the independently
compiled square-covariance output, the staged late-window/fresh-variance
output, the independent martingale and pairwise-variance outputs, and existing
project and pinned package libraries. No package or production dependency was
rebuilt or overwritten. This is fresh compile and transitive-axiom evidence
for the exact staged draft with these imports; it does not count as a
production landing or close the downstream source targets listed above.

## Production integration

The reviewed per-update late-window propagated conditional variance result is integrated as `Formalization/ModelFree/TDSharpPropagatedVariance.lean`; cumulative proxy control and Freedman remain separate. Declaration and proof bodies match the reviewed staged sources; imports and status comments were updated where needed. The full project check compiled 272 modules and audited 3,576 project declarations, allowing only `propext`, `Classical.choice`, and `Quot.sound`.
