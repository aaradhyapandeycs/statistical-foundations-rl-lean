# Variance-sensitive fixed-row concentration: builder handoff

Source: `source/upstream/tex/chapters/prelim.tex` lines 916–927 and 954–966,
`lem:Bernstein-prelim`, SHA-256
`2d27bb720d49020ce1d3ea362b1678a90c6208882accca90fef21c25e42031a5`.
Staged source: `.local/EmpiricalBernstein.lean`, SHA-256
`ceee7deadcbf30aad24c3c2b4f6e38a53eb5055f792a849ab95368ce95023cdf`.

## Proved results

All probabilities below are for the actual `N`-fold independent product of
the finite transition row `d`, and empirical values are from its proved
frequency row; no desired tail inequality is a premise.

- `sampleValue_variance` identifies Mathlib variance of each actual sampled
  `V(sᶦ)` with the project's finite row variance `σ² = d.variance V`.
  `sampleSum_variance` proves the variance of the independent sum is `Nσ²`,
  and `empiricalValue_variance` proves exactly `σ²/N` for `N>0`.
- `empiricalRow_chebyshev` gives the variance-sensitive polynomial bound
  `P(|d̂V−dV|≥ε) ≤ σ²/(Nε²)` for `ε>0`, in `ℝ≥0∞` form. In particular,
  `empiricalRow_zeroVariance_tail` proves every positive deviation event has
  probability zero when `σ²=0`.
- `centeredSample_mgf_factor`, `centeredSample_mgf_eq_row`, and
  `centeredSample_mgf_pow` prove the exact independence factorization and
  identify every factor with the genuine centered row MGF. The proved
  `empiricalRow_chernoff_mgf` is a one-sided Chernoff bound in terms of that
  actual MGF; it does not assume any variance-sensitive MGF bound.
- `centeredRow_mgf_le_exp_variance` proves a **weaker** variance-sensitive
  estimate `MGF(u) ≤ exp(u²σ²)` when `u≥0`, `uB≤1`, and `0≤V≤B`.
  It uses Mathlib's quadratic exponential remainder bound, the source row's
  exact centered mean and variance, and not a Bernstein assumption.
  `empiricalRow_twoSided_variance_tail` proves for any such `u` the actual
  two-sided bound

  ```text
  P(|d̂V−dV|≥ε) ≤ 2 exp(−u N ε + N u² σ²).
  ```

  Choosing `u=ε/(2σ²+Bε)` gives, for `N>0`, `B>0`, `ε>0`,

  ```text
  P(|d̂V−dV|≥ε)
    ≤ 2 exp(−N ε²(σ²+Bε)/(2σ²+Bε)²).
  ```

  This exact bound is exported as `empiricalRow_variance_tail_explicit`;
  `empiricalRow_variance_tail_norm` specializes `B=‖V‖∞` for source
  nonnegative finite vectors. The separately proved zero-variance tail handles
  `σ²=0`, and the existing Hoeffding module handles `‖V‖∞=0` by exact zero
  deviation.

## Source Bernstein gap

The bounded pinned-library search for Bernstein/Bennett/sub-gamma and
variance-sensitive exponential tail theorems found no direct exact theorem;
see `docs/probability-api-discovery.md` for filenames and search scope. This is
not a claim of global nonexistence. The source's sharp denominator requires an
estimate such as

```text
log MGF(u) ≤ u²σ² / (2(1−uB/3)),    0≤u<3/B,
```

and its optimized two-sided tail
`2 exp(−Nε²/[2σ²+(2/3)Bε])`. The proved MGF and displayed explicit tail have
weaker constants and therefore do **not** establish that source tail or its
particular Bernstein threshold. A future exact proof must establish that sharp
bounded-centered MGF estimate (including the zero and endpoint cases), perform
the valid optimization and strict-probability/finite-family transfer. The
pinned library's Chebyshev or the weaker bound above cannot be substituted
without changing the source constants. No family union, random-family
independence, matrix-wide statement, or full Lemma 2.5 is claimed. `N>0` is an
explicit sampling convention; the source's `N=0` boundary is unspecified.

## Checks and dependencies

`bash scripts/lean-local.sh .local/EmpiricalBernstein.lean` compiled. A
separate temporary copy of the exact staged source with thirteen axiom checks
also compiled via the same wrapper. The checked results were
`sampleValue_variance`, `sampleSum_variance`, `empiricalValue_variance`,
`empiricalRow_chebyshev`, `centeredSample_mgf_factor`,
`centeredSample_mgf_eq_row`, `centeredSample_mgf_pow`,
`empiricalRow_chernoff_mgf`, `empiricalRow_zeroVariance_tail`,
`centeredRow_mgf_le_exp_variance`, `empiricalRow_twoSided_variance_tail`,
`empiricalRow_variance_tail_explicit`, and `empiricalRow_variance_tail_norm`.
Each used only `propext`, `Classical.choice`, and `Quot.sound`. The probe was
removed. Independent review and source-export integration remain.

Dependency SHA-256:

- `Formalization/Probability/EmpiricalRow.lean`: `6e87c90ff1150f7053845acff92d60a5c35035c7a78adcd394e0da5f3d9dc154`
- `Formalization/Probability/EmpiricalHoeffding.lean`: `fd8be9002c7e5c6e418461818e7842c96520ca604e10e466f8431b1307798b55`
- `Formalization/Probability/Variance.lean`: `541714ed6173402131bece633476308c1c832f31d0cbb46534cc55f48dcd9553`
