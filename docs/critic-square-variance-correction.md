# Independent review: signed square variance

## Finding

The second inequality in Lemma 5.22 (`lemma:sqv`) is false for general signed
random variables as printed in `chapters/onlineRL.tex:3612–3615`. With
`X = 1` of probability `1/8` and `X = −1` of probability `7/8`, the largest
possible magnitude is 1, the mean is `−3/4`, and

\[
\operatorname{Var}(X)=\frac{7}{16},\qquad
\operatorname{Var}((X-\mathbb E X)^2)=\frac{63}{64}.
\]

Thus the printed coefficient-one inequality would require `63/64 ≤ 7/16`,
which is false. The proof at lines 3627–3631 uses
`|X−E[X]| ≤ Cmax`; for this example `|1−E[X]| = 7/4 > 1`.

The source’s first inequality, `Var(X²) ≤ 4 Cmax² Var(X)`, is valid as
printed. For the second inequality, replacing the coefficient 1 by 4 gives
a valid bound: `|X−E[X]| ≤ 2 Cmax`, so the fourth centered moment is at most
`4 Cmax² Var(X)`, and the variance of the centered square is no larger than
that fourth moment.

## Formal statement and counterexample

`StatisticalRL.Statements.Lemma5_22_corrected` states both inequalities on
an arbitrary probability space, for measurable real `X` with a pointwise
absolute bound. It keeps coefficient 4 in the first clause and uses 4 in
the second. The proof wrapper applies the two general probability-space
exports in `Formalization/Probability/SquaredVarianceBounds.lean`. Their
integrability requirements are derived from boundedness; the statement adds
no `MemLp` or finite-space assumption.

The counterexample is also realized on an actual finite product probability
space in `Formalization/Counterexamples/CenteredSquareVarianceMeasure.lean`.
Its coordinate sample is measurable, has absolute value 1 everywhere, and
uses Mathlib’s measure-theoretic variance. The bridge from the finite
distribution calculation identifies the measure variances with `7/16` and
`63/64`, and the exported theorem disproves the general coefficient-one
claim. This is a counterexample to the second clause, not the first.

The restriction `0 ≤ X ≤ Cmax` makes coefficient 1 valid and is already
available in the finite-distribution result. The UCBVI proof uses
nonnegative bounded-value estimates, so this signed-variable correction
does not invalidate the separately proved UCBVI result.

## Verification reviewed

The combined Chapter 5 statement and applying proof are pinned at SHA-256
`895fd593b8b9e0d01bc66d89585122df404e9a51bb9f8d728ecb58db3a14ade8` and
`7c34f64a40c6f13413a9acd2b9ac966f7b0beab8d2efc76d575f13d46c4eb0d0`.
The general bounds module is pinned at
`0801d5a41fd169c2870db1d94eddfcd8445cb544d2d7ad7a0a9c60fd78defb69`; the
exact-measure counterexample is pinned at
`27276d005d77d7002de583a86cfbf32fcaf9356950e4400875766dd6d8fce1fc`.
The separate focused checks covered both provider exports, the finite and
measure counterexamples, and ten actual Chapter 5 statement/proof exports;
their transitive axioms were only `propext`, `Classical.choice`, and
`Quot.sound`.

The affected integration run `20261104T154754690164Z` passed with 7 rebuilt
modules and 664 verified reused modules. The full audit inspected 6,484
declarations and found only the standard three axioms. Its manifest is
`22db88489b141ab493ad3f1fa7a24ca8869e18770b7e3399c54e198715d961ea`; the
guarded driver is `e22e42f24d15f7bb88f1129830e6d968c85b4219da6d176854498b0c2b2b132a`.
All 671 current workspace source hashes matched the frozen manifest, and
the seven rebuilt workspace `.olean` files matched their recorded hashes.
This is an affected rebuild against the verified 668-module base; the 418
module clean ancestor is provenance, not a fresh 671-module clean build.
The historical clean ancestor did not pin package or `.olean` bytes; the
verification records this limitation and pins the current base chain and
tool paths.

This review supports only the corrected variance statement and its exact
counterexample. The false original second clause is not certified, and the
result does not close Chapter 5 or the monograph.
