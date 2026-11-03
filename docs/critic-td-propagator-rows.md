# Source review: actual TD propagator rows

The initial source-only review covered `.local/TDPropagatorRows.lean`, SHA-256 `74c343fcc85f84cc1cd979ae75f3bfa30ddf7cefef36be7adcbb5b0fd8cfd8e7`, against the actual transition recursion and source equations `eq:TD-Zk-defn` and `eq:TD-L1-norm` in `generative_model_model_free.tex:350–385`. The final compiled source reviewed below is SHA-256 `d35be937b0ad24bca409814e4201539aa24eb5da6b7aa07b5abeed4d67fba486`.

## Findings

- The propagator starts at update `start+1` and applies through `t` in chronological recursion order. For a noise injected at source update k, `tdErrorPropagate ... k t` applies exactly the future transitions k+1,…,t, matching the source suffix product. The terminal remains explicit.
- `tdPropagatorRow` is the value at state s after applying the actual operator recursion to basis vector (1_{\{r\}}). The proved finite basis decomposition reconstructs every propagated vector as `Σ_r row(s,r)*U(r)`, with no assumed matrix representation or product-order convention.
- Positivity is derived from `0≤η_i≤1`, `0≤γ`, and positivity of the actual probability-row expectation. For rates in the source interval the scalar contraction `1−η_i(1−γ)` is nonnegative. The exact row mass is the product of these scalar contractions over precisely `start+1,…,t`; it is not just an upper bound.
- `tdWeightedPropagatorRow` contains the scalar `γ η_k` exactly once. Its row mass is `γ * tdRateWeight γ η t k`, and its application theorem reconstructs `γ η_k * tdErrorPropagate ...` exactly. The final identity expresses the actual fixed-terminal `tdWeightedErrorIncrement` as this weighted row applied to the actual raw centered noise at source time k. No duplicate η factor is introduced by the rate-weight abbreviation.

No source-level mismatch found in basis representation, chronology, positivity premises, row-mass indices, or the single `γη_k` factor. This draft does not prove a stochastic law or variance claim by itself; it supplies the deterministic propagator identification needed to specialize the generic linear-row conditional-variance foundation. Freedman still needs the actual finite-history filtration, conditional variance cap, increment bound and source late-time probability allocation.

## Final-source review and independent compilation

I re-read the final source at the hash above and compared its definitions and proof statements with the preceding review. The earlier documented conclusions still match: the recursion applies updates `start+1,…,t`, the finite basis expansion is an equality for the actual propagator, positivity and exact row mass use the stated positive-prefix rate assumptions, and `tdWeightedPropagatorRow` includes `γ η k` once. The final file retains the explicit-terminal actual-increment row identity. The earlier file contents were not retained for a byte-for-byte diff, so this is a semantic comparison against the prior recorded review, not a source diff.

Fresh exact-source audit ran in project-owned `.local/td-propagator-audit-d35be937/`, without rebuilding production dependencies. The eight staged modules compiled in dependency order: `TDCausality`, `TDErrorDecomposition`, `TDConditionalMoments`, `TDCrossCovariance`, `TDErrorUnroll`, `TDErrorCaps`, `TDLinearRowVariance`, and `TDPropagatorRows`. Production imports were read from the existing project build. All 14 declarations exported by the final propagator-rows file (the two row definitions and 12 theorems) were probed with `#print axioms`; each uses only `propext`, `Classical.choice`, and `Quot.sound`. This confirms the staged dependency closure at the listed source hashes, not production integration.

Exact staged-source hashes used for the rebuild:

| Module | SHA-256 |
| --- | --- |
| `TDCausality` | `8c8cfdf1271c2bd9736b9ec0eb8b3da7896f8f3f9c4bfd03ca33af1a6249fb29` |
| `TDErrorDecomposition` | `c0a838360290c7d47e16a0228d5a4ecfbfee06ddfc354a9e2ba4df07241a51fe` |
| `TDConditionalMoments` | `1edb87f6d84c82a9e1d242aae2dbac95701d33b173eda2f08d65deb4a9d6c227` |
| `TDCrossCovariance` | `709c414fef2264b3ef7b3790873ba0d3d813f87973cb447a01880c7ca86b1744` |
| `TDErrorUnroll` | `495d294dae15f39fd1fe7a4f07fc7a202eec9dddf0686a15fd36f56555538e48` |
| `TDErrorCaps` | `952f7f0f94634574f55b6ccc6cc97c8a535d4acfe0f62e71f80f141c418e0983` |
| `TDLinearRowVariance` | `b0068f5663d1edb5e298693aebaae7abb63facbfa2963e6c1f8cd0074c7f14c9` |
| `TDPropagatorRows` | `d35be937b0ad24bca409814e4201539aa24eb5da6b7aa07b5abeed4d67fba486` |

Production integration: the reviewed source declarations and proofs compile in the project export with qualified imports and updated staging-only comments where applicable. The full project audit checked 3,029 declarations, allowing only `propext`, `Classical.choice`, and `Quot.sound`.
