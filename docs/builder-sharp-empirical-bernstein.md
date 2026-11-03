# Sharp fixed-vector Bernstein development

Staged source: `.local/SharpEmpiricalBernstein.lean`, SHA-256
`f47b57d451b8ee49c8b702a834ee99747ec5cca36288bf9344dd08c11a596e67`.
This is a bounded fixed-vector contribution toward `prelim.tex` lines 961–978,
not the entire source lemma.

## Established statements

For any finite transition row `d`, actual `N`-sample product law (with `N > 0`),
deterministic `V` satisfying `0 ≤ V s ≤ B`, `B ≥ 0`, and `L > 0`,
`empiricalRow_source_threshold_strict` bounds the probability (as `Measure.real`)
of the strict violation of

```
|P̂ V − P V| ≤ sqrt(2 L Var_P(V) / N) + 2 B L / (3 N)
```

by `2 exp(-L)`. The conclusion includes zero variance and zero range. Take
`B = ‖V‖∞`; `sqrt(2 L Var/N)` equals the source's
`sqrt(2 L/N) * sqrt(Var)` by nonnegativity. This is the source's variance and
range constants for a single vector, and its strict violation is the complement
of the claimed non-strict error bound. `N = 0` is not covered; the sample mean
itself requires a positive sample count.

The proof uses Mathlib's `Nat.factorial_mul_pow_le_factorial` with `m = 2`
to show `(n+2)! ≥ 2·3^n`, bounds the exponential tail by a geometric series,
and proves the scalar majorant for `|z| < 3`. Averaging the resulting pointwise
bound against the actual finite row yields

```
MGF(u(V − EV)) ≤ exp(u² Var(V) / (2 (1 − u B / 3)))  (0 ≤ u, uB < 3).
```

It then uses the existing iid Chernoff theorem and `u = ε/(Var+Bε/3)` to obtain
both tails by reflection and their union, with the classical exponent
`−N ε²/(2(Var+Bε/3))`. A direct threshold calculation gives the stated
source constants. Zero variance uses the already established zero-probability
bound, while `B = 0` is handled directly. No tail estimate is an assumption.

## Strictness and remaining extensions

The source's logarithm has an extra factor 2 of slack. For a nonempty finite
family of cardinality `k` and `0 < δ < 1`, set `L = log(4k/δ)`; one vector's
strict-failure bound is `δ/(2k)`, and a finite union would give failure at most
`δ/2 < δ`. Thus strict success needs no finite-support minimum-gap argument.
This calculation has not yet been formalized here for a family. In particular,
random independent families, measurable family laws, the whole-matrix union,
and the subsequent empirical-variance inequality are not claimed. Existing
Hoeffding family code may supply an independent-family integration pattern, but
this Bernstein module does not yet use or prove that extension.

## Validation

- `bash scripts/lean-local.sh .local/SharpEmpiricalBernstein.lean`: passed with
  no diagnostics, against the integrated `EmpiricalBernstein` dependency.
- A temporary copied-source probe printed transitive axioms of
  `exp_remainder_le`, `centeredRow_mgf_le_sharp`,
  `empiricalRow_upper_sharp_chernoff`, `empiricalRow_upper_sharp`,
  `empiricalRow_lower_sharp`, `empiricalRow_twoSided_sharp`,
  `empiricalRow_source_threshold`, and
  `empiricalRow_source_threshold_strict`: all report only `propext`,
  `Classical.choice`, and `Quot.sound`. No custom axioms or placeholders.
- An independent review is required before integration.
