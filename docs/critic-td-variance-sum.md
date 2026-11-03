# Independent review: fixed-terminal TD variance sum

Reviewed `.local/TDVarianceSum.lean`, SHA-256 `8abae5134d4e7f9ff511e02540a383cf894d5b63b3dc2710679875db9f8ad197`, against the actual fixed-terminal `Z_j^t` source definition and its weighted conditional moment/proxy.

## Semantic findings

`tdPastIndices T n` contains exactly the sampled state coordinates at source times `1,…,n`; time zero is excluded. `tdPastSigma_mono` proves inclusion by restricting a longer finite prefix to the shorter one, and `tdSampleFiltration` uses this as a filtration. The terminal process is genuinely fixed-terminal: its increment at filtration index `n` is source (Z_{n+1}^t), evaluated on the actual finite sample array. Under `t≤T`, the finite sum over `range t` corresponds exactly to source updates (1,…,t); each update has the actual fresh coordinate `n+1` and old value `V_n`. The unused time-zero coordinate and any padding beyond the sample horizon do not enter the summed terms. `t=0` is the empty-sum case.

The equality theorem packages the already proved actual conditional-square identities for each `n : Fin t` into one almost-everywhere event and sums them. The result is the exact sum of squared actual propagator-row coefficients times true policy-row variances of the predictable (V_n), with terminal (t) retained throughout. The proxy theorem uses the previously proved nonnegative-row inequality termwise; its RHS keeps the actual step-dependent propagated variance vector. It introduces no deterministic cumulative cap, target variance bound, or concentration assumption. Its only rate premise is (0≤η_i≤1) for positive (i≤t), sufficient for nonnegative propagator rows; the time premise `t≤T` is what keeps all source draws within the actual finite experiment. This is a fixed-terminal predictable second-moment sum, equal to conditional variance sum because the preceding module proves each increment conditionally centered. It is not itself a Freedman bound or a deterministic upper bound.

No source-level mismatch was found in the filtration, update indices, padding, or row-variance/proxy sum.

## Independent compile and axioms

Freshly compiled the ten-module staged closure in `.local/td-variance-sum-audit-8abae513/`; production imports were resolved from existing project artifacts and not rebuilt. All eight declarations/definitions exported by the target file were probed (`tdRestrictPast`, `tdPastSigma_mono`, `tdSampleFiltration`, `tdTerminalIncrement`, `tdTerminalVarianceSum`, `tdTerminalVarianceProxy`, `tdTerminalVarianceSum_eq_squaredRows`, and `tdTerminalVarianceSum_le_proxy`). Each reports only `propext`, `Classical.choice`, and `Quot.sound`.

| Staged module | SHA-256 |
| --- | --- |
| `TDCausality` | `8c8cfdf1271c2bd9736b9ec0eb8b3da7896f8f3f9c4bfd03ca33af1a6249fb29` |
| `TDErrorDecomposition` | `c0a838360290c7d47e16a0228d5a4ecfbfee06ddfc354a9e2ba4df07241a51fe` |
| `TDConditionalMoments` | `1edb87f6d84c82a9e1d242aae2dbac95701d33b173eda2f08d65deb4a9d6c227` |
| `TDCrossCovariance` | `709c414fef2264b3ef7b3790873ba0d3d813f87973cb447a01880c7ca86b1744` |
| `TDErrorUnroll` | `495d294dae15f39fd1fe7a4f07fc7a202eec9dddf0686a15fd36f56555538e48` |
| `TDErrorCaps` | `952f7f0f94634574f55b6ccc6cc97c8a535d4acfe0f62e71f80f141c418e0983` |
| `TDLinearRowVariance` | `b0068f5663d1edb5e298693aebaae7abb63facbfa2963e6c1f8cd0074c7f14c9` |
| `TDPropagatorRows` | `d35be937b0ad24bca409814e4201539aa24eb5da6b7aa07b5abeed4d67fba486` |
| `TDWeightedVariance` | `9c99c1eaa1f39bbff926c4da0c4f66efcb5760e1d3e63bc92ada80d8203d0557` |
| `TDVarianceSum` | `8abae5134d4e7f9ff511e02540a383cf894d5b63b3dc2710679875db9f8ad197` |

The direct production import `Formalization.Probability.FreedmanExactAssembly` was reused at SHA-256 `8914080eb48351a84b53d23d361430e6b9b5beff9feda4b3af483517b56a5c4c`. This focused staged audit is not a production integration claim.

## Production integration

The reviewed result is now integrated as `Formalization/ModelFree/TDVarianceSum.lean`. Its proof and declaration bodies match the reviewed staged source; imports and status comments were adjusted. The complete project check compiled 234 modules and audited 3,148 project declarations, using only `propext`, `Classical.choice`, and `Quot.sound`. This does not change the scope or imply the final source theorem.
