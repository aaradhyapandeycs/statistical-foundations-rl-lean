# Actual bounded-increment exponential supermartingale

Stable staged source `.local/BoundedIncrementExponentialProcess.lean`, SHA-256 `5bead892af3f42dd581d80b8625581ad7fee6d71654c1135382da55b8cc1bea0`.

Staged dependency: `.local/ConditionalBernsteinMGF.lean`, SHA `b8680a852d7e27875ae277481959efffbcb570c0421ac9fcc1252f615fdffa8d`. Other imports are actual pinned Mathlib Martingale/Basic and ConditionalExpectation/PullOut.

## Actual process and source-style assumptions

For a genuine natural-number filtration ℱ of an ambient probability space, increments X n are strongly ℱ(n+1)-measurable, satisfy |X n|≤B almost everywhere for deterministic B≥0, and have actual conditional mean E[X n|ℱ n]=0 almost everywhere. With a fixed real t obeying |t|B≤1, define V n=E[(X n)²|ℱ n] and the recursive process

`Z0=1; Z(n+1)=Zn exp(t Xn−t²Vn)`.

The file proves its exact closed form `Zn=exp(t Σ(k<n)Xk−t²Σ(k<n)Vk)` for every n and outcome. Index0 denotes the first increment revealed at time1; this is the source's X1 convention shifted once. No independence, tail inequality, target Freedman theorem, exponential-supermartingale property, or integrability of Z is assumed.

## Six exports

1. `boundedIncrementExponentialProcess`: actual recursive definition using actual conditional second moments.
2. `boundedIncrementExponentialProcess_eq_exp_sum`: exact compensated exponential formula.
3. `boundedIncrementExponentialProcess_pos`: strict positivity at every outcome.
4. `boundedIncrementExponentialProcess_adapted`: derived ℱ-adaptedness from newly revealed increment measurability and predictability of Vn. It uses filtration inclusions explicitly.
5. `boundedIncrementExponentialProcess_bound`: actual finite-time envelope `Zn≤exp(n|t|B)` almost everywhere. Conditional second-moment nonnegativity follows from `condExp_nonneg`, so each compensation only decreases the exponential. This bound is proved without the conditional-mean-zero assumption.
6. `boundedIncrementExponentialProcess_supermartingale`: the full pinned Mathlib `Supermartingale Z ℱ μ`, including integrability at every time and conditional ordering for every earlier/later pair.

The final proof derives integrability of every Zn from the envelope, positivity and ambient measurability obtained from adaptedness. For one step it factors `Z(n+1)=A·E`, with predictable `A=Zn exp(−t²Vn)` and `E=exp(tXn)`. Integrability of E is derived from |tXn|≤1; integrability of the product is precisely that of the already bounded Z(n+1). The actual conditional pull-out API then combines with the proved conditional quadratic MGF bound to give `E[Z(n+1)|ℱn]≤Zn`. `supermartingale_nat` proves the full structure, rather than accepting a supermartingale as a premise or stopping at a one-step claim.

No bounded initial process or arbitrary compensator is substituted. The deterministic initial value is exactly1; t may be negative or0, and B=0/all zero increments are included. Bounds are almost everywhere as appropriate for conditional expectation; the closed form and positivity are pointwise.

## Source relation and remaining constants/gaps

This is a genuine adapted bounded martingale-difference construction relevant to `lem:Freedman-prelim`, but uses the preliminary quadratic coefficient t² and domain |t|B≤1. It is **not** the sharp Bernstein compensator t²/(2(1−|t|B/3)); consequently the exact printed Freedman constants √8 and4/3 have not been established. There is no tail or stopped-process theorem in this file. Remaining work includes a variance-restricted exponential tail argument with a legal tuning parameter, two-tail/dyadic event union, and sharp coefficient work if needed to recover the exact source radius. The existing deterministic peeling helper alone does not discharge these stochastic steps.

The source uses the past increment filtration; this file legitimately proves the more general arbitrary-filtration construction by requiring conditional centering for that actual filtration, not deducing it from a smaller history. A TD/Q-learning application still must prove its own fresh-sample conditional mean/variance identities and adaptedness.

## Validation

Freshly compiled the exact conditional-MGF dependency into isolated `.local/supermartingale-build`, then the exact new source to its own artifact there, using only production and pinned package paths below that directory. Both exited0. An exact-source-copy probe appended `#print axioms` for all six exports and checked the final declaration; it exited0 without diagnostics, and every export uses only `propext`, `Classical.choice`, `Quot.sound`. No admitted proof or custom axiom occurs. No dependency artifacts were removed or overwritten. Compiler slot released immediately after the final probe.

Independent review and qualified production integration/actual-export audit remain separate gates.
