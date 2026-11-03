# Independent review: actual-law high-sample policy evaluation

**Verdict: pass for the explicit high-sample statement.** The file assembles an actual algorithm/trajectory probability result with its explicit β and sufficient sample threshold. It does not itself prove the printed theorem's target-ε sample condition.

For a finite admissible MDP M, fixed stationary randomized policy π, actual positive natural per-state sample count N and `0<δ<1`, put `h=1−γ`, `m=⌈log(e/h)⌉₊`, `L=log(4S(m+1)/δ)` and β=2L. The positive-discount declaration assumes `N≥64β/h` and proves probability strictly greater than `1−δ` that `‖valueEstimator−trajectoryExpectedValue‖∞≤3√(8β/(h³N))`. The full-discount declaration uses the same assumptions and conclusion and handles γ=0 separately. The explicit inclusive m+1 logarithm corresponds to the source's levels 0 through m; comparison with the printed theorem's `log(S/(δh))` and sample parameter ε is a distinct later step.

## Common event and source objects

The proof starts from exactly one imported `auxiliaryValues_bernstein_explicit` event on the actual policy-row sampling law. Every state and every index in `Fin(m+1)` is controlled; the values on which the event concentrates are fixed true auxiliaries determined by M, π and the level. The row residual is rewritten as the literal matrix difference `(P̂π−Pπ)Vˡ`. Its linear coefficient is weakened from β/(3N) to β/N using nonnegativity, while the square-root term remains `√(β/N)`. There is no intersection of separate `1−δ` events and no assertion of independence of fitted values from the data.

On that same event the code supplies every l<m residual to the conditional inverse/resolvent recursion, weakens the reviewed scaled successor-growth constant 1 to √2, and uses γ≤1 to derive the source's b₁/b₂ recursion. The terminal residual is selected at exactly l=m from the same event and supplied to the separately proved conditional terminal error. True-value growth holds through m; the initial bound uses the actual trajectory-value norm. Thus the conditional arithmetic theorem's recursion, growth, terminal, depth and initial-value premises are discharged pointwise for the same data. The stipulated `64β/h` sample condition is passed unchanged.

At level zero, `empiricalAuxiliaryValue_zero` identifies the empirical auxiliary with the actual plug-in `valueEstimator`; `auxiliaryValue` reduces to the actual infinite-trajectory policy value. The event inclusion therefore produces the stated norm event rather than an abstract or independently fitted estimator. The imported finite-state norm is the sup norm. This is an actual-law statement for each fixed M and π, not a uniform guarantee for policies selected from the same sample.

For γ=0 the reviewed all-level identity makes the level-zero error identically zero for every data outcome. The resulting event is the entire sample space and the nonnegative radius remains well-defined. No division by γ is performed in that branch. N=1 and all finite state cardinalities are admitted when the displayed threshold is met. The source's final weaker sample cutoff and the exact printed ε theorem are not silently assumed.

## Scope and verification

This is source Steps 1–6 through the exact explicit high-sample radius. A separate bridge must compare β to the printed logarithm, instantiate positive natural N and ε, and address the one-state logarithm case; independently reviewing and integrating those ingredients remains necessary before a printed theorem closure claim.

Staged source SHA-256 `b8f4dd90e9571d730eb0203752e3299c8d4ee3c0cbabdfdd6961037f096ac601`; staged terminal dependency SHA-256 `29c50df335bf18e75083d8628817f16d5f076f6eb32e63465ed227752e306145`; source TeX SHA-256 `b7e7abfb2c2cb2c0dd82470db5ecac3a67d7163682246d499935d9130214ac4d`. The exact unchanged source with its original imports and four appended axiom checks compiled independently, exit 0; the staged terminal dependency was freshly built from its reviewed source in an isolated project-owned artifact directory. `policyEvaluationDepth`, `policyEvaluationBeta`, and both high-sample probability theorems use only `propext`, `Classical.choice`, and `Quot.sound`. Integrated export verification remains separate.

## Integrated export verification

The first production build failed because imported TerminalError and BernsteinRecursion contained identically auto-named local `DecidableEq` instances; the lead gave the TerminalError and HighSample local instances distinct explicit names. The repaired production HighSample SHA-256 `6dff4ef9cc1674feeca2a4712e38609f89596d667359b21d2729e9a0fe63b01f` differs from the reviewed staged source only in its qualified terminal import and named local instance. After rebuilding the repaired integrated TerminalError, the actual HighSample module compiled. An import-only audit of all four exports succeeded with only `propext`, `Classical.choice`, and `Quot.sound`.
