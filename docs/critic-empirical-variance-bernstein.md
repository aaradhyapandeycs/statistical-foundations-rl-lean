# Independent empirical-variance Bernstein review

Reviewed 2026-11-02. **PASS for the staged fixed-row identities and the explicitly restricted, probability-one bound; the source empirical Bernstein lemma remains unproved.** This review does not certify a general empirical Bernstein theorem.

## Identity and source

- `.local/EmpiricalVarianceBernstein.lean`: SHA-256 `ac0d89639cdf3396e92dd4c3c7ca5be302952481ca1b8f68751b6dbadd9120c5`.
- `Formalization/Probability/EmpiricalBernstein.lean`: `ceee7deadcbf30aad24c3c2b4f6e38a53eb5055f792a849ab95368ce95023cdf`.
- `source/upstream/tex/chapters/prelim.tex`: `2d27bb720d49020ce1d3ea362b1678a90c6208882accca90fef21c25e42031a5`.

The source lemma `empirical bernstein` (prelim lines 983–998) takes a finite family of nonnegative state vectors independent of the specified empirical row, `N≥2`, and `0<δ<1`. It claims, simultaneously over the family, strict success probability greater than `1−δ`, with radius `sqrt(2 log(4|𝒱|/δ)/(N−1)) sqrt(Var_P̂ V) + 7‖V‖∞ log(4|𝒱|/δ)/(3(N−1))`. The empirical variance is the variance of the empirical probability row, hence its own empirical average uses denominator N. The `(N−1)` appears in the radius, not in the empirical probability row.

## Mathematical and statement check

`sampleMeasure N` is the product of N copies of the actual finite row distribution; the imported empirical-row results establish its probability law, marginals, and mutual independence. The empirical row is the actual frequency distribution and the imported `empiricalValue_variance` uses those iid observations to prove the sample-mean variance is `Var_P(V)/N`. The audited integral identity consequently gives `E[Var_P̂(V)]=((N−1)/N) Var_P(V)` for N>0. The corrected result multiplies by `N/(N−1)` only for N≥2 and proves unbiasedness. This correctly handles N=2 and has no division-by-zero case.

For any finite probability vector and `0≤V≤B`, the proof establishes `Var(V)≤B²/4` using the moment inequality `E[V²]≤B E[V]`; its empirical specialization is valid on every data point. The comparison of empirical and population variance follows from the triangle inequality and the bound on the difference of squared means. The pointwise mean deviation bound `|P̂V−PV|≤‖V‖∞` correctly uses nonnegativity of V; both expectations lie in `[0,‖V‖∞]`.

`empiricalBernstein_fixedRow_smallConfidence` specializes to one fixed vector, so `|𝒱|=1` and the logarithm is `log(4/δ)` with exactly the source coefficients and empirical variance. It requires N≥2, V nonnegative and δ>0, plus the **extra condition** `3(N−1)≤7 log(4/δ)`. This condition implies the linear radius is at least `‖V‖∞`; therefore the success event is all sample outcomes and its probability is 1. Since δ>0, this yields the source's strict `1−δ < 1` conclusion. The theorem does not require δ<1, so it is valid in a larger ambient δ domain; its overlap with the source is `0<δ<1` plus the extra condition. Zero norm and zero empirical variance are covered without cancellation. For larger N at fixed δ, the condition eventually fails: this is a bounded/trivial-radius case, not a general concentration result.

There is no random or finite-family quantification, no proof of uniform simultaneous bounds, no conditioning or mixing for a family independent of the empirical row, and no bound in the remaining confidence range. These missing pieces cannot be inferred from the probability-one special case. The source's independence assumption is independence of the family and the empirical row; any eventual lifting argument must establish the source's exact form rather than silently assuming a stronger or different independence condition. The builder report correctly marks this boundary.

## Validation

An exact temporary copy of the staged source with eight appended `#print axioms` checks compiled using `bash scripts/lean-local.sh` against the integrated dependency. The copied probe was removed. The checks cover empirical nonnegativity, integral identity, corrected unbiasedness, population and empirical range bounds, variance comparison, mean-deviation bound, and the restricted source-radius result. Each depends only on `propext`, `Classical.choice`, and `Quot.sound`. The compiler reported the documented harmless tactic-sequencing lint warning; no `sorryAx` or custom axiom appeared. Compiler use was coordinated within the two-compiler limit.

Independent review and compilation of the eventual integrated export remain necessary. A full source-lemma claim additionally requires the nontrivial empirical-variance concentration in the unrestricted source parameter regime and the independently sampled finite-family simultaneous extension.
