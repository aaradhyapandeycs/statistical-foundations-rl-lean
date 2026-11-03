# Exact Bernstein scalar envelope and conditional MGF

Stable sources:

- `.local/BernsteinExponentialEnvelope.lean`, SHA-256 `3c587678634f4a362d10e207eb107a187de90873f16298a8943c1a0500ccc086`.
- `.local/ConditionalBernsteinSharpMGF.lean`, SHA-256 `c00cec33172e670630243f93b66a0eb61b175028efdf8feef831c3449177581c`.

The conditional file imports the scalar file by its staged name. All other imports are pinned Mathlib. Neither file assumes any tail bound, concentration event or desired conditional-MGF inequality.

## Three scalar exports

`bernstein_factorial_lower` proves `2·3^k≤(k+2)!` from the existing `Nat.factorial_mul_pow_le_factorial` at m=2. `exp_le_one_add_add_bernstein` then proves

`exp(z)≤1+z+z²/[2(1−|z|/3)]`, for every real z with |z|<3.

It uses the actual signed exponential series (`NormedSpace.expSeries_div_hasSum_exp` and `Real.exp_eq_exp_ℝ`), removes its first two terms with `hasSum_nat_add_iff' 2`, bounds each tail term by `(z²/2)(|z|/3)^k`, and compares the actual sums against the geometric sum via `hasSum_le`. Negative z is included; it is not silently replaced by |z| in the linear term. `exp_le_one_add_add_bernstein_of_abs_le` proves the common envelope version for |z|≤r<3, with denominator `2(1−r/3)`. Equality at |z|=r is allowed; the strict boundary r<3 guarantees denominator positivity. z=0 and r=0 are valid.

The search of pinned Mathlib found factorial/exponential-series/geometric primitives but no ready-made scalar Bernstein envelope with this exact denominator. This helper is not another copy of the weaker norm remainder estimate used previously.

## Actual conditional Bernstein MGF

`conditional_mgf_le_exp_bernstein_secondMoment` proves, under a probability measure, ambient-measurable real X, actual conditioning sigma-algebra m≤m₀, |X|≤B almost everywhere, |t|B<3, and E[X|m]=0 almost everywhere,

`E[exp(tX)|m]≤exp(t² E[X²|m]/[2(1−|t|B/3)])` almost everywhere.

All integrability is derived from boundedness/measurability, including X² and exp(tX). The scalar envelope is applied to z=tX and r=|t|B; conditional monotonicity/linearity and actual conditional centering produce `1+c E[X²|m]`, then 1+u≤exp(u) gives the result. X is explicitly measurable for the ambient sigma-algebra, not prematurely measurable for m. Both signs of t, t=0 and zero increments are included. A separate B≥0 premise is unnecessary because its almost-everywhere absolute bound on a probability space already enforces it.

This is the sharp Bernstein coefficient, not the earlier weaker t² coefficient with |t|B≤1. It directly removes that previously documented analytic obstruction to the source Freedman constants. It still does not itself prove a supermartingale/tail theorem or a dyadic probability union.

## Route to exact source constants

Replace the preliminary process compensator t² by the proved deterministic `c=t²/[2(1−|t|B/3)]`, prove c≥0 from |t|B<3, and reproduce actual adaptedness/integrability and predictable pull-out. The same envelope `Zn≤exp(n|t|B)` remains valid because cVn≥0. Markov yields `P{Yn≥x,Wn≤v}≤exp(cv−tx)` for legal t≥0. For v>0,x>0, t=x/(v+Bx/3) is legal and algebraically yields exponent `−x²/[2(v+Bx/3)]`. Positive dyadic variance ceilings can use this tuning; exact zero global variance needs a separate zero-increment argument or an explicit limit, not division by v. Then prove the desired fixed-variance radius and two-sign/K-bin union with exact log(2K/δ). These steps remain open until compiled/reviewed; no source Freedman completion is claimed here.

## Validation

Both exact sources compiled. Fresh scalar dependency compilation wrote only isolated `.local/sharp-bernstein-build` artifacts. Exact-source-copy probes appended all three scalar axiom checks and the conditional theorem axiom/signature check; every run exited0 without diagnostics, and all four exports reported only `propext`, `Classical.choice`, `Quot.sound`. Signature inspection confirms actual conditional expectation, ambient measurability, exact coefficient and strict tuning boundary. No placeholder or custom axiom occurs. Compiler slot released immediately after the final audit. Independent review, production qualification/landing and actual export checks remain separate gates.
