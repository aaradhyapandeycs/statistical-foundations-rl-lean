# Exact self-bounding structure of empirical variance

Builder result, 2026-11-02. Target `.local/EmpiricalBernsteinSelfNormalized.lean`, SHA-256 `57b62e5173016cef76514262607696eaf5dc7c679e7143fd714d126d0663ebfc`.

**Proved deterministic prerequisites; source empirical Bernstein concentration remains open.** The file assumes no probability tail, moment estimate, final radius, or custom axiom. It imports the existing empirical-variance module and uses actual observed coordinates throughout. This file is staged infrastructure, not an approved frozen source declaration, and independent review is required before integration.

## Discovery and scope

I read the repository workflow, search/discovery, and proof-pattern instructions and searched the pinned Mathlib probability tree, then the entire Mathlib tree for `empirical Bernstein`, `bounded difference`, `McDiarmid`, `Efron–Stein`, `self bound`, standard deviation, and variance concentration. No directly applicable finite-product self-bounding or empirical Bernstein concentration theorem was found. The martingale Borel–Cantelli occurrence of bounded differences is an asymptotic theorem, not the required finite-sample tail. Existing sub-Gaussian/Hoeffding concentration suffices for the earlier additive two-moment result but not the source's sharp self-normalized radius.

Rather than postulate the missing concentration theorem, this file proves its exact leave-one-out structural input. Source locators: `source/upstream/tex/chapters/prelim.tex:983–998`, label `empirical bernstein`, and variance definition at lines 428–437. The source variance is the empirical frequency-row variance with denominator N, retained exactly here.

## Mathematical objects and exports

For N≥2, sample values x_i=V(ω_i), empirical mean m=N⁻¹∑x_i, and Z=Var_P̂(V), define

- `leaveOneOutMean`: m_{−i}=(N−1)⁻¹∑_{j≠i}x_j.
- `leaveOneOutResidual`: Z_i=N⁻¹∑_{j≠i}(x_j−m_{−i})².

The residual deliberately keeps denominator N for comparison with Z. It is **not** the ordinary deleted-sample variance with denominator N−1 and must not be substituted for it without the corresponding scaling. Both definitions have their actual formulas on the entire declared source domain N≥2, with no fallback branch or arbitrary witness.

The following are all proved:

1. `leaveOneOutResidual_congr`: Z_i depends only on coordinates other than i. Changing coordinate i while preserving all others leaves it unchanged.
2. `leaveOneOutResidual_minimizes`: for every real c, Z_i≤N⁻¹∑_{j≠i}(x_j−c)². Thus the chosen center is the actual minimizing mean, not merely a selected value.
3. `empiricalVariance_sub_leaveOneOutResidual`: Δ_i:=Z−Z_i=(x_i−m)²/(N−1).
4. `sum_empiricalVariance_leaveOneOut_decrement`: ∑Δ_i=N Z/(N−1).
5. `empiricalVariance_leaveOneOut_decrement_nonneg`: every Δ_i≥0.
6. `leaveOneOutMean_mem_Icc`: if all 0≤V≤B, then 0≤m_{−i}≤B.
7. `empiricalVariance_leaveOneOut_decrement_le_sharp`: Δ_i≤(N−1)B²/N². The proof establishes the exact alternate identity Δ_i=(N−1)(x_i−m_{−i})²/N² internally.
8. `sum_sq_empiricalVariance_leaveOneOut_decrement_le_sharp`: **∑Δ_i²≤(B²/N) Z**.

Two earlier looser range/quadratic estimates also remain as correctly proved named lemmas; the final `_sharp` exports improve them. All statements are deterministic, apply to every actual sample, and use no premises that encode unproved stochastic bounds. The sharp quadratic estimate follows by Δ_i²≤((N−1)B²/N²)Δ_i and the exact sum identity.

No strict positivity of B is required: B=0 and V=0 are included, with every decrement zero. Constant vectors and deterministic distributions are included. N=2 is included. N=0 and N=1 are excluded by the source-compatible N≥2 restriction needed for the deleted mean. The deterministic statements need no d or sample measure; when used for any genuine iid row law, they hold pointwise without additional independence assumptions. The existing definition of `sampleMeasure` supplies product independence for the future concentration proof.

## Missing probability step and source constants

These estimates have the desired variance-sensitive scaling B²/N and are useful input for a finite-product entropy/self-bounding concentration argument. They do not themselves prove a tail theorem. The existing expectation identity gives E[Z]=(N−1)Var_P(V)/N. Still required is a proved finite-product lower-deviation bound for empirical standard deviation (or an equivalent direct empirical Bernstein route), with constants sufficient for the source radius. Neither an Efron–Stein variance estimate alone nor a generic bounded-difference bound establishes the required exponential self-normalized inequality.

The final source obligation remains the simultaneous mean-error event with radius

`√(2 log(4|𝒱|/δ)/(N−1)) √Var_P̂(V) + 7 ‖V‖∞ log(4|𝒱|/δ)/(3(N−1))`,

success probability strictly greater than 1−δ, N≥2, 0<δ<1, and an independent finite random family of nonnegative vectors. This file establishes none of the source concentration constants, confidence inversion, strict probability margin, or random-family lifting. Those are explicit remaining obligations. In particular the earlier additive O(B²√(log(1/δ)/N)) variance estimate is not promoted to the sharper source result by these deterministic identities.

## Validation

Pinned Lean `v4.27.0-rc1` and Mathlib `32d24245c7a12ded17325299fd41d412022cd3fe`. Used the repository wrapper, without rebuilding or changing dependency artifacts. All compiler slots coordinated with the lead/other workers; at most two Lean compilers active.

- `bash scripts/lean-local.sh .local/EmpiricalBernsteinSelfNormalized.lean`: exit 0. A final unused-instance warning was removed by omitting the unused finite-state instance from that purely finite-index lemma.
- Final exact-source copy `/tmp/EmpiricalBernsteinSelfNormalizedAxioms.lean` plus twelve `#print axioms` checks: `bash scripts/lean-local.sh /tmp/EmpiricalBernsteinSelfNormalizedAxioms.lean`, exit 0, no warnings. Both definitions and all ten public theorems have exactly `[propext, Classical.choice, Quot.sound]`; no `sorryAx` or custom axioms. The temporary file was deleted.

Only the assigned staged Lean file and this builder note were written. No source lemma closure, frozen approval, or independent certification is claimed. Integration and independent semantic review remain with the lead/critic.
