# Exact source Freedman random-variance bound

Stable staged `.local/FreedmanExactAssembly.lean`, SHA-256 `f67328390c02b1fbe10b778993976ce227312187012419afb54947e222c25009`.

Direct staged imports: `BernsteinFixedTimeTail.lean` SHA `12f302ffc27db189b57a9ccd3775d36a5672542b50338ca19e60d0c9c3907b3d`; `FreedmanVariancePeeling.lean` SHA `010f97d59be568ea443fe38f40e51ac83b4cd95ebcde8f118bb3fb76935b15da`. The sharp tail imports the actual sharp process/MGF/scalar series infrastructure recorded in their handoffs. All these are proved dependencies, not assumptions of the final theorem.

## Final source-shaped declaration

`StatisticalRL.freedman_source_bound` proves for an arbitrary probability space and genuine natural-number filtration ℱ, real increments Xn strongly measurable at ℱ(n+1), actual conditional mean E[Xn|ℱn]=0 a.e., a deterministic B≥0 with |Xn|≤B a.e., and a nonnegative deterministic variance scale σ₂ with actual Wn≤σ₂ a.e.:

For every n, positive integer K and δ∈(0,1), probability is at least1−δ that

`|Yn|≤sqrt(8max(Wn,σ₂/2^K)log(2K/δ))+(4/3)B log(2K/δ)`.

Yn is the actual sum of the first n increments; Wn is the actual sum of their conditional second moments. Index0 is the first increment revealed at time1. σ₂ names the source's σ² (an arbitrary nonnegative scale); it is not a new assumption about a different variance surrogate. All measures, increments and predictable variances in the event are identical to those in the hypotheses. There is no iid assumption, exponential-supermartingale premise, tail premise, or independence of an adapted iterate. The arbitrary-filtration formulation requires centering for that actual filtration; it does not infer centering for a larger history from a smaller one.

## Nine exports / argument

`predictableSecondMomentSum_neg` proves equality under increment negation; `predictableSecondMomentSum_nonneg` derives a.e. nonnegativity. `bernstein_variance_restricted_lower_chernoff` applies the actual upper-tail theorem to genuine negated increments and transports conditional means/variances. No distributional symmetry is assumed. `bernstein_abs_variance_restricted_source_radius` unions both signs to give `2exp(−L)` for each positive fixed variance ceiling, at radius `2sqrt(vL)+(4/3)BL`. `bernstein_abs_variance_restricted_chernoff` similarly gives the two-sided generic legal-t bound, including variance ceiling0.

`bernstein_abs_zero_variance_radius` handles σ₂=0 with B>0 using t=1/B, which is strictly legal since tB=1<3. Its exponent at radius (4/3)BL is at most−L. It never divides by the variance or appeals to an unproved continuity limit. `incrementSum_eq_zero_of_zero_bound` proves actual zero increment sums a.e. when B=0.

`freedman_source_failure_bound` first sets L=log(2K/δ)>0 and proves exp(−L)=δ/(2K). It treats B=0 by zero actual sums and nonnegative radius. It treats σ₂=0 by the zero-variance two-sided bound and actual a.e. Wn=0. For σ₂>0 each of the K dyadic bin ceilings is strictly positive. The proved dyadic cover selects j<K with Wn≤vbin and `sqrt(4vbin L)≤sqrt(8max(Wn,σ₂/2^K)L)`. Hence each failure belongs to a two-sided fixed-bin event. Union over Fin K costs K·2exp(−L)=δ. The actual a.e. variance cap/nonnegativity are consumed through `measure_mono_ae`, not strengthened to pointwise version assumptions. No extra confidence loss occurs for signs or bins beyond the exact2K inside the logarithm.

`freedman_source_bound` proves measurability of Yn, Wn and the exact radius, then uses the complement relation to translate failure probability≤δ to the printed non-strict confidence event. Fixed-time n=0, K=1, B=0 and σ₂=0 all remain valid. The theorem does not claim uniformity over all times on one event.

## Exact source relation

The target is `lem:Freedman-prelim`, `prelim.tex:1056–1080`, source SHA `2d27bb720d49020ce1d3ea362b1678a90c6208882accca90fef21c25e42031a5`. Both the variance coefficient8 and linear coefficient4/3, random Wn cutoff, log(2K/δ), non-strict event and at-least probability match. Earlier preliminary coefficient2 tail theorems are not used as substitutes for the sharp bound. Those files are transitively imported only to reuse actual sum definitions; the proof route is the exact scalar Bernstein envelope→sharp conditional MGF→actual sharp exponential supermartingale→Markov/tuning→two-sided dyadic union. Source missing sharp constants are now proved in this staged candidate rather than weakened.

The source describes conditioning on the past increments; the abstract filtration is standard explicit machinery. Its adaptedness condition is fulfilled by that natural history when constructing an application, and the theorem also permits larger filtrations if centering is actually proved there. Routine measurable/integrable infrastructure is not a statistical restriction: boundedness plus ambient measurability derives integrability in the dependencies. No source completion is certified until independent full-chain review and actual production export checks succeed.

## Validation

Fresh dyadic dependency compilation used isolated `.local/sharp-bernstein-build` artifacts. Exact assembly compilation was checked incrementally. The final exact-source-copy `.local/sharp-bernstein-build/FreedmanAssemblyAudit.lean` appended all nine export axiom probes and the final signature check; it exited0 without diagnostics. Every export reported only `propext`, `Classical.choice`, `Quot.sound`. The sharp process/tail dependencies were freshly built in the same isolated directory, with their own complete axiom probes documented separately. No custom axiom or placeholder occurs; dependency artifacts were not deleted/modified. Compiler slot released immediately after completion.

Pending: rigorous independent full-source and transitive semantic review, staged-to-production qualification, actual imported-export compilation/axiom checks and shared project build. No TD/Q-learning sample theorem follows without proving its specific adapted fresh-sample increment identities.
