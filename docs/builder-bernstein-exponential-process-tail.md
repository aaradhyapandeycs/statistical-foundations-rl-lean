# Sharp Bernstein exponential process and fixed-time tail

Stable staged sources:

- `.local/BernsteinExponentialProcess.lean`, SHA-256 `0970ad8baedf963dde4611f89ad018ce474f12da5ee087927659a550a9b3650f`.
- `.local/BernsteinFixedTimeTail.lean`, SHA-256 `12f302ffc27db189b57a9ccd3775d36a5672542b50338ca19e60d0c9c3907b3d`.

Process dependency: `ConditionalBernsteinSharpMGF.lean` SHA `c00cec33172e670630243f93b66a0eb61b175028efdf8feef831c3449177581c`, which imports scalar envelope SHA `3c587678634f4a362d10e207eb107a187de90873f16298a8943c1a0500ccc086`. Tail additionally imports `BoundedIncrementFixedTimeTail.lean` SHA `b7631878ff4ba0ad2fea7c952157d7807da9c320296d727be37313833a3fb1fc` only to reuse the already defined actual increment sum and predictable second-moment sum; its weaker probability theorems are not used to prove the new tail. That import transitively includes the prior preliminary process/MGF. The new probability route uses the sharp conditional MGF and new sharp process throughout.

## Actual sharp process (eight exports)

`bernsteinCoefficient B t=t²/[2(1−|t|B/3)]`; `bernsteinCoefficient_nonneg` derives its nonnegativity on |t|B<3. The recursively defined `bernsteinExponentialProcess` starts at1 and multiplies at step n by exp(tXn−cE[Xn²|ℱn]). Its exact exponential-sum representation, positivity, filtration adaptedness, and a.e. envelope exp(n|t|B) are proved. `bernsteinExponentialProcess_supermartingale` derives the full actual Mathlib Supermartingale, including integrability at every finite time and conditional ordering, from actual filtration-style assumptions: Xn is ℱ(n+1)-strongly measurable, |Xn|≤B a.e., and E[Xn|ℱn]=0 a.e. The real t is fixed, B≥0 and |t|B<3; both signs, t=0 and B=0 are allowed. The proof pulls out the predictable factor and consumes the actual sharp conditional MGF; no exponential-process property or integrability conclusion is assumed.

## Fixed-time sharp tail (six exports)

`bernsteinExponentialProcess_integral_le_one` derives expectation≤1. `bernstein_variance_restricted_chernoff` proves `P{Yn≥x,Wn≤v}≤exp(cv−tx)` for each legal t≥0, using the actual Zn formula and Markov. Here Yn and Wn are actual sums on the identical probability space; Wn retains its random conditional second moments.

`bernstein_exact_tuning` proves, for B≥0,x>0,v>0, that t=x/(v+Bx/3) is nonnegative and satisfies tB<3, and the exponent is exactly `−x²/[2(v+Bx/3)]`. It explicitly proves the Bernstein denominator identity `1−tB/3=v/(v+Bx/3)`. `bernstein_variance_restricted_tail` therefore proves that exponent bound for the actual joint event. No desired tail or tuning optimality is assumed.

`bernstein_source_radius_arithmetic` proves that x=2sqrt(vL)+(4/3)BL is positive and makes x²/[2(v+Bx/3)]≥L for v,L>0 and B≥0. `bernstein_variance_restricted_source_radius` yields the actual bound

`P{Yn≥2sqrt(vL)+(4/3)BL, Wn≤v}≤exp(−L)`.

This is a valid conservative fixed-bin radius chosen for the printed source peeling: vbin≤2max(Wn,σ²/2^K) implies `2sqrt(vbin L)≤sqrt(8max(Wn,σ²/2^K)L)`, with the desired **unchanged linear coefficient4/3**. The new results thus close the earlier linear-coefficient obstruction without weakening the source target. The copied module header in the tail file calls the process “preliminary quadratic”; the actual declaration/proof uses the exact sharp coefficient above, as its imports and statements show.

## Precise remaining scope

These are one-sided fixed-time variance-restricted events. They do not yet prove the source two-sided random-variance probability event. Remaining work: negate-increment/lower-tail transfer, K-bin union with two signs and exact log(2K/δ), and σ²=0/global-zero-variance endpoint. Positive v is explicit in tuning/radius theorems; no division-by-zero case is hidden. B=0 is already included whenever v>0. A deterministic positive variance ceiling suffices for every positive-scale dyadic bin; σ²=0 needs a separate argument. No uniform-in-time/stopping-time claim is made.

## Validation

Fresh sharp conditional dependency and sharp process compilation into `.local/sharp-bernstein-build` exited0. The reused exact preliminary tail source and new sharp tail source were then compiled serially there, both exit0. Exact-source-copy probes appended axiom checks for all eight process and all six tail exports; every compile exited0 without diagnostics, and all14 declarations reported only `propext`, `Classical.choice`, `Quot.sound`. The process and tail proof bodies contain no placeholder or custom axiom. Dependencies were consumed from isolated exact staged artifacts and actual production/pinned package artifacts; no dependency artifact deletion or modification occurred. Compiler slot released immediately after the final probe.

Independent review, qualified production imports/landing, actual export audit and shared project build remain separate gates. This handoff does not certify full `lem:Freedman-prelim` yet.
