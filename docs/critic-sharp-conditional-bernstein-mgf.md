# Independent review: sharp conditional Bernstein MGF

Reviewed `.local/BernsteinExponentialEnvelope.lean` SHA `3c587678634f4a362d10e207eb107a187de90873f16298a8943c1a0500ccc086`, `.local/ConditionalBernsteinSharpMGF.lean` SHA `c00cec33172e670630243f93b66a0eb61b175028efdf8feef831c3449177581c`, and `docs/builder-sharp-conditional-bernstein-mgf.md` against the source Freedman setup (`prelim.tex:1056–1073`). The staged declarations establish the stated analytic ingredient with the sharp Bernstein denominator; they do not yet establish the source Freedman inequality.

`bernstein_factorial_lower` supplies `2·3^k ≤ (k+2)!`. The scalar exponential envelope is proved from the signed exponential series, with the first two terms separated and every remaining term bounded above by the positive geometric majorant. This preserves the signed linear term for negative inputs. It establishes `exp z ≤ 1+z+z²/[2(1−|z|/3)]` for `|z|<3`. The envelope variant allows `|z|≤r<3`; positivity of the denominator and its monotonic direction are correct, including `z=r=0`.

The conditional declaration uses a genuine probability measure, an ambient-measurable bounded random variable, an actual conditioning sigma-algebra `m≤m₀`, and the a.e. equation `E[X|m]=0`. It derives integrability of `X`, `X²`, and `exp(tX)` from the bound rather than assuming the desired MGF or a concentration event. Conditional monotonicity and linearity give `1+c E[X²|m]`, then `1+u≤exp u`; `c=t²/[2(1−|t|B/3)]`. The strict domain `|t|B<3`, both signs of `t`, and a.e. nature of the conclusion are explicit. On a probability space the a.e. bound itself excludes an impossible negative `B`; no extra positivity premise is smuggled in.

The source requires adapted martingale increments, a predictable variance sum, two-sided concentration and dyadic probability bookkeeping. A sharp exponential supermartingale, legal tuning and fixed-time tail, sign reversal, the zero-variance endpoint and the source bin union remain to be proven; this module claims none of them. The prior weaker fixed-time bound cannot supply the source's `4/3` linear coefficient just by citation of this MGF.

## Independent compiler and axiom audit

Freshly compiled the exact staged scalar dependency into an isolated project-local directory and compiled exact source copies of both modules with all four export axiom inspections appended. Every compilation exited zero; all four exports depend only on `propext`, `Classical.choice`, and `Quot.sound`. This is a staged-source audit; integrated source and imported exports require separate checks.

## Integrated production audit

Production `Formalization/Probability/BernsteinExponentialEnvelope.lean` is byte-identical to the reviewed source SHA `3c587678634f4a362d10e207eb107a187de90873f16298a8943c1a0500ccc086`. Production `ConditionalBernsteinSharpMGF.lean` SHA `3691aaa5832a7016c89f453b2acbe85bdbe6be6fac53b90a3` differs solely by qualifying its scalar-envelope import. Both compiled; all four imported exports use only `propext`, `Classical.choice`, and `Quot.sound`. The initial attempt to use a sparse isolated `LEAN_PATH` failed because it shadowed the existing production dependency tree; recompiling these requested production modules into the project build directory and then auditing actual imports succeeded.
