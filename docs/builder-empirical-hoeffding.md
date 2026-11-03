# Fixed-vector Hoeffding builder handoff

Source: `source/upstream/tex/chapters/prelim.tex` lines 916–950,
`lem:Hoeffding-prelim`, SHA-256
`2d27bb720d49020ce1d3ea362b1678a90c6208882accca90fef21c25e42031a5`.
Implementation: `.local/EmpiricalHoeffding.lean`, SHA-256
`fd8be9002c7e5c6e418461818e7842c96520ca604e10e466f8431b1307798b55`.

For the actual independent product sample measure from
`Formalization/Probability/EmpiricalRow.lean`, `centeredSample_independent`
proves independence of the centered observations via measurable composition.
`centeredSample_subgaussian` applies Mathlib's bounded-variable Hoeffding
lemma to each sample, using its independently proved exact expectation.
`centeredSum_subgaussian` applies the independent-sum result with sharp proxy
`N (B/2)^2` for vectors satisfying `0 ≤ V(s) ≤ B`.

`empiricalRow_hoeffding` proves the following two-sided bound for `N > 0`,
`B > 0`, `0 ≤ V ≤ B`, and `ε ≥ 0`:

```text
P[ ε ≤ | empiricalRow(V) − d(V) | ] ≤ 2 exp(−2 N ε² / B²).
```

The probability is Mathlib's real-valued measure of the stated event. The
proof relates the centered sum exactly to `N` times the genuine empirical
row deviation, applies the upper and lower sub-Gaussian bounds, and unions
them; neither independence nor a tail inequality is assumed. The theorem
`empiricalRow_hoeffding_norm` instantiates `B = ‖V‖` for arbitrary nonnegative
finite vectors, and `empiricalRow_norm_zero_deviation` handles the zero-norm
case exactly, on every sample, without a division by zero. The extra general
interval theorem `empiricalRow_zero_deviation` handles `B=0` similarly.

This is the source-constant **fixed-vector tail bound**, not the full Lemma 2.4:
no finite-family union, random-family independence, conversion to the
particular logarithmic threshold, or source's strictly greater success
probability is claimed. `N>0` explicitly follows the sampling convention;
the source does not state the `N=0` boundary clearly. No matrix-wide or
Bernstein result is claimed.

Validation: a temporary copy of the exact final staged source, with
`#print axioms`, compiled using
`bash scripts/lean-local.sh <temporary-probe>`.
The seven checked declarations `centeredSample_independent`,
`centeredSample_subgaussian`, `centeredSum_subgaussian`,
`centeredSum_twoSided`, `empiricalRow_hoeffding`,
`empiricalRow_hoeffding_norm`, and `empiricalRow_norm_zero_deviation` used
only `propext`, `Classical.choice`, and `Quot.sound`. The temporary probe was
removed. Independent source/semantic review, integration, and the full
source lemma remain for later work.

Dependency SHA-256: `Formalization/Probability/EmpiricalRow.lean`
`6e87c90ff1150f7053845acff92d60a5c35035c7a78adcd394e0da5f3d9dc154`.
