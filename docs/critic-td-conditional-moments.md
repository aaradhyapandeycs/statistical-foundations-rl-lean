# Independent review: TD conditional moments

## Exact source and validation

Reviewed `.local/TDConditionalMoments.lean`, SHA-256 `1edb87f6d84c82a9e1d242aae2dbac95701d33b173eda2f08d65deb4a9d6c227`. Its staged dependencies were also hash-checked: `.local/TDCausality.lean` `8c8cfdf1271c2bd9736b9ec0eb8b3da7896f8f3f9c4bfd03ca33af1a6249fb29` and `.local/TDErrorDecomposition.lean` `c0a838360290c7d47e16a0228d5a4ecfbfee06ddfc354a9e2ba4df07241a51fe`. Production dependencies included synchronous TD sampling, TD learning weights, the trajectory-value bridge, finite variance, and empirical-row results.

Freshly compiled the two staged dependencies and target into `.local/td-conditional-moments-independent-audit`; all succeeded. An import-only audit probed all 19 target exports. Each uses only `propext`, `Classical.choice`, and `Quot.sound` transitively.

## Source review

- The experiment samples the state-indexed array at `Fin (T+1)`. Source time zero remains unused; update `t+1` uses coordinate `(s, ⟨t+1, …⟩)` under `t<T`, which guarantees the coordinate exists. The old iterate is `V_t` and is measurable with respect to the prefix containing source times 1 through t.
- The innovation sign is sampled value minus its expectation under the true policy row `M.policyTransition π s`. This matches `tdCenteredRowNoise` at source time `t+1`, whose synchronous old iterate is `V_t`. The final theorem identifies the finite-experiment increment with that exact noise on the same sample array.
- Prefix/fresh independence comes from the actual product sampling law. The fresh-coordinate marginal is the actual policy transition row, including zero-mass atoms; no support assumption is added. Integrability is valid for every real statistic because the actual sample experiment is finite.
- The predictable coefficient sum is pulled out under prefix strong measurability. Applying it to the value indicators gives the conditional mean equal to the true policy-row expectation; subtracting the predictable row mean yields conditional centering. Applying the same expansion to squared centered values yields exactly the true-row variance of `V_t` conditional on the full sample prefix.

Statements requiring `t<T` are vacuous when `T=0`; no out-of-range current coordinate is used. This module establishes prefix-conditional moments for the actual finite-experiment row increment and its link to the source noise. It does not establish a smaller increment-generated-history transfer, conditional variance cap, bounded increment, martingale concentration result, or TD rate.

No source-level issue found in the checked indexing, actual row, signs, integrability, or moment identities. This is staged evidence; production-module integration and production-export checking remain separate.

Production integration: the reviewed source declarations and proofs compile in the project export with qualified production imports and updated staging-only comments where applicable. The full project audit checked 2,970 declarations, allowing only `propext`, `Classical.choice`, and `Quot.sound`.
