# Fixed-time variance-sensitive martingale upper tail

Stable source `.local/BoundedIncrementFixedTimeTail.lean`, SHA-256 `b7631878ff4ba0ad2fea7c952157d7807da9c320296d727be37313833a3fb1fc`.

Dependency: staged `BoundedIncrementExponentialProcess.lean`, SHA `5bead892af3f42dd581d80b8625581ad7fee6d71654c1135382da55b8cc1bea0`, and its reviewed conditional-MGF dependency SHA `b8680a852d7e27875ae277481959efffbcb570c0421ac9fcc1252f615fdffa8d`. No target tail theorem is assumed.

## Actual quantities and assumptions

`incrementSum X n` is Σ(k<n)Xk. `predictableSecondMomentSum μ ℱ X n` is the actual Σ(k<n)E[Xk²|ℱk]. The probability space, filtration, newly revealed increment measurability, almost-everywhere |Xk|≤B and actual conditional mean-zero identities are exactly those of the proved exponential-supermartingale construction. Index0 denotes the increment revealed at time1. No iid claim is made for increments.

## Eight exports and justified constants

Two definitions above plus:

- `boundedIncrementExponentialProcess_integral_le_one` derives E[Zn]≤1 from the actual proved Supermartingale, its initial value1 and Mathlib set-integral ordering on the full space.
- `boundedIncrement_variance_restricted_chernoff` proves the fixed-time joint-event bound `P{Yn≥x, Wn≤v}≤exp(t²v−tx)` for every t≥0 with tB≤1. It uses literal exponential-process identity, event inclusion and Markov, and accepts arbitrary real x,v. No variance-tail or process-expectation estimate is an input premise.
- `boundedIncrement_quadratic_tuning` proves that for B>0,x>0,v≥0, t=x/(2v+Bx) is nonnegative and legal, and `t²v−tx≤−x²/(4v+2Bx)`.
- `boundedIncrement_variance_restricted_tail` combines these to prove `P{Yn≥x,Wn≤v}≤exp(−x²/(4v+2Bx))` for B,x>0,v≥0.
- `boundedIncrement_radius_arithmetic` proves the explicit radius conversion x=2sqrt(vL)+2BL satisfies x>0 and x²/(4v+2Bx)≥L when B,L>0,v≥0.
- `boundedIncrement_variance_restricted_radius` consequently proves `P{Yn≥2sqrt(vL)+2BL,Wn≤v}≤exp(−L)`.

All quantities use the same actual sample outcome and law. This is a variance-restricted joint event, not an unconditional claim with deterministic variance v unless Wn≤v is separately proved. No deterministic upper variance assumption is needed to state the joint bound. The Chernoff lemma includes t=0; tuned/radius lemmas include v=0 and n=0. They explicitly require B>0 and positive x or L to keep tuning denominators positive. The degenerate B=0 tail is not claimed here; it requires an exact zero-increment argument or a separate limiting step. In applications with nonzero bounded increments one can supply their positive deterministic bound directly.

## Relation to source Freedman

These constants follow rigorously from the preliminary t² compensator and restricted tuning range. The exponent denominator4v+2Bx and radius2sqrt(vL)+2BL are valid conservative choices, not a claim of optimal tuning or sharp Bernstein constants. After the existing dyadic cover, the variance part becomes sqrt(8max(Wn,σ²/2^K)L), but the linear term remains **2BL**, larger than the printed source (4/3)BL. This file therefore does not establish `lem:Freedman-prelim` with its exact constants. It proves only a one-sided fixed-time bound; lower tail, union over K bins/two signs, probability bookkeeping and the source sharp coefficient remain separate work. There is no unproved optimization or tail premise hidden in its final declaration.

## Validation

Focused exact-source compilation exited0. An exact-source-copy probe `.local/supermartingale-build/TailAudit.lean` appended axiom checks for all eight exports; it exited0 without diagnostics and each export reported only `propext`, `Classical.choice`, `Quot.sound`. It imported the previously freshly built exact staged supermartingale/conditional-MGF artifacts in the isolated directory, with actual production/pinned package dependencies. No custom axiom/admission occurs and no dependency artifacts were modified. Compiler slot released immediately after the probe.

Independent source/axiom review, qualified production integration and actual imported-export checks remain separate requirements.
