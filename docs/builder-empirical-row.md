# Independent sampling and empirical row builder handoff

Source: `source/upstream/tex/chapters/prelim.tex` lines 916–927, SHA-256
`2d27bb720d49020ce1d3ea362b1678a90c6208882accca90fef21c25e42031a5`.
Implementation: `Formalization/Probability/EmpiricalRow.lean`, SHA-256
`95cb82a08660326b01667e822f948470c33d0df47595df708649c280bd72282c`.

For an arbitrary actual finite transition row `d`, `rowMeasure` converts its
nonnegative normalized weights to a probability measure using the project's
existing PMF bridge. `sampleMeasure d N` is Mathlib's independent product
measure on `Fin N → State`. `sampleMeasure_coordinate` and
`sampleMeasure_coordinate_singleton` prove each observation has the actual
row law and its exact masses, and `sampleMeasure_independent` proves the full
coordinate family is mutually independent using Mathlib `iIndepFun_pi`.
`empiricalRow N hN ω` is the source's frequency formula, provided `hN : 0 < N`;
its `FiniteDistribution` construction proves nonnegativity and total mass one.
`empiricalRow_expectation` identifies evaluation at arbitrary real `V` with
the actual arithmetic mean of observed values. `rowMeasure_integral` bridges
the measure integral and the project's finite expectation, and
`empiricalRow_unbiased` proves the empirical evaluation is unbiased under the
actual product law. In particular no source independence or target conclusion
is assumed as a proposition field.

The sample measure itself is meaningful at `N = 0` (there are no coordinates),
but no empirical frequency row is defined there: the source formula divides
by `N`, and the manuscript does not explicitly discuss that boundary. The
positive-N premise is therefore an explicit sampling convention, not an
unqualified transcription or a silently repaired concentration lemma. No
Hoeffding/Bernstein bound, random-vector-family independence, matrix-wide
sampling law, or source lemma is claimed here.

Validation: `bash scripts/lean-local.sh Formalization/Probability/EmpiricalRow.lean`
passed before adding the final singleton marginal theorem. A temporary copy of
the exact final source with axiom checks appended compiled using the same
wrapper; `sampleMeasure_coordinate_singleton`, `sampleMeasure_independent`,
`empiricalRow`, `empiricalRow_expectation`, `rowMeasure_integral`, and
`empiricalRow_unbiased` used only `propext`, `Classical.choice`, and
`Quot.sound`. The temporary probe was removed. Independent source review,
actual facade/export integration and integration build remain.

Dependency SHA-256: `Formalization/MDP/InfiniteTrajectory.lean`
`60c4f2c0279014ba54f6d0165e01d86ba407f2f72f93f4e9c493a6b8b86e33e9`;
`Formalization/MDP/Basic.lean`
`ecf28ee04a78405be352f5453d957f34a7883d33304b21255a9f7f444e0bc088`.
