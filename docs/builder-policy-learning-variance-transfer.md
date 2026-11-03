# Standard-deviation stability and leave-one-out Bernstein transfer

`.local/PolicyLearningVarianceTransfer.lean` proves the sharp deterministic standard-deviation perturbation bound and the exact fixed-grid-to-empirical-value radius transfer used at `generative_model_model_based.tex:1345–1371`, especially the standard-deviation triangle inequality at `:1364–1368`. It consumes an explicit fixed-grid concentration inequality as a conditional intermediate input; it does not assume or prove the final probability event. Independent source review and integration remain pending.

## Discovery and mathematical route

I searched the existing project variance infrastructure and pinned Mathlib probability/finite-sum APIs. `Formalization.Probability.Variance` already supplies the actual finite population variance, its centered-square characterization, nonnegativity and the coarser estimate `|Var(f)−Var(g)|≤4Bε`. That variance perturbation estimate is insufficient for the source's **linear ε** standard-deviation transfer; taking its square root would give a weaker sqrt(Bε) error.

The pinned Mathlib finite-sum theorem `Real.sum_mul_le_sqrt_mul_sqrt` supplies Cauchy–Schwarz. The new file applies it to `sqrt(p_s)f_s` and `sqrt(p_s)g_s` for the actual finite probability row, proves Minkowski for square roots of second moments, and applies that to the exact centered vectors. No measure-theoretic variance conversion or unproved covariance inequality is assumed.

## General reusable inequalities

All exports are in `StatisticalRL.FiniteDistribution`, for actual normalized nonnegative finite probability rows and arbitrary real state vectors. No interval bound or positive-variance assumption is required.

- `expectation_mul_le_sqrt_secondMoments` is weighted Cauchy–Schwarz for the actual expectation.
- `sqrt_secondMoment_add_le` proves the corresponding square-root second-moment triangle inequality.
- `sqrt_variance_add_le` proves `sqrt(Var(f+g))≤sqrt(Var(f))+sqrt(Var(g))` using exact expectation centering.
- `sqrt_variance_le_norm` proves `sqrt(Var(f))≤‖f‖∞`.
- `sqrt_variance_le_add_norm_sub` and `abs_sqrt_variance_sub_le_norm` prove the sharp stability

  `|sqrt(Var(f))−sqrt(Var(g))|≤‖f−g‖∞`.

- `sqrt_variance_le_of_norm_sub_le` is the exact source direction: if `‖f−g‖∞≤ε`, then `sqrt(Var(g))≤sqrt(Var(f))+ε`.

The source f is the actual fitted empirical optimal value, and g its close fixed-grid value. The stability lemma is deterministic and applies pointwise even when both vectors depend on data; it does not falsely assert independence for those data-dependent vectors.

Zero variance and constant vectors are included without dividing by any variance, norm or standard deviation. Signed functions are allowed. Finite normalized row semantics, not coordinate independence, are what the deterministic triangle inequality uses.

## Residual and exact source radius

For any two probability rows p,q,

`residual_sub_le_two_norm` proves

`|[(q−p)f]−[(q−p)g]|≤2‖f−g‖∞`.

It uses the two actual row expectation bounds and exact linear algebra. Taking q as the empirical frequency row and p as its true transition row gives precisely the source's `2ε` residual approximation.

`bernstein_radius_transfer` consumes a nonnegative coefficient a, a covering distance `‖f−g‖∞≤ε`, and the explicit intermediate estimate

`|(q−p)g|≤a sqrt(Var_p(g))+b`.

It produces

`|(q−p)f|≤a sqrt(Var_p(f))+(2+a)ε+b`.

The close vector's concentration bound is a visible premise of this deterministic helper, not a hidden assumed success event or a premise of a claimed source probability theorem. No independence assertion is needed for the algebra. The stochastic application must prove that bound simultaneously for every fixed-grid member before selecting a covering g from data.

`source_cover_radius_arithmetic` proves the final numerical simplification at ε=1/(Nh), N≥1 and β≥4:

`(2+sqrt(β/N))/(Nh)+β/(3Nh)≤2β/(Nh)`.

It derives `sqrt(β/N)≤β/2` and uses only positive h, positive natural N and the displayed source β domain. `bernstein_radius_transfer_source` combines the actual generic transfer and this arithmetic to yield exactly

`|(q−p)f|≤sqrt(β/N) sqrt(Var_p(f))+2β/(Nh)`

from `‖f−g‖∞≤1/(Nh)` and the source fixed-grid radius `sqrt(β/N)sqrt(Var_p(g))+β/(3Nh)`. Thus the precise coefficient 2 is proved, not assumed or inflated.

## Scope and remaining application

These results apply at every true state-action row with q chosen as the actual empirical row. The reviewed grid/value-cover construction provides the required close g, and the separate fixed-u independence/Bernstein argument must supply its concentration bound uniformly over that finite family. This file does not connect those probability pieces, prove measurability/independence of a random family, or establish an actual-law event by itself.

The source β lower bound `β≥4` is an explicit **numerical domain premise** of the final simplification. A source application must discharge it from β=2log(16SAN/((1−γ)δ)), positive finite counts, 0≤γ<1 and 0<δ<1. No arbitrary variance comparison, final error bound, or self-bounding resolvent estimate is assumed. The later choice of the fitted policy and the sharp policy-learning value-error/sample-complexity theorem remain separate.

The generic helper covers zero discount by any h=1 normalization; no division by γ occurs. For all source discounts, h=1−γ>0 justifies the denominators. N=1 and zero variances are valid; N=0 is excluded explicitly in source-radius arithmetic. No asymptotic condition is introduced.

## Validation

The new file imports the existing integrated finite variance definition and pinned real square-root API. It was compiled after the lead explicitly allocated one compiler slot. `bash scripts/lean-local.sh .local/PolicyLearningVarianceTransfer.lean` passed without diagnostics after routine algebra/centered-function rewriting fixes. An exact unchanged-source copy `.local/VarianceTransferAxiomAudit.lean` with eleven appended `#print axioms` commands also compiled without warnings/errors. Every exported theorem reported only `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, `admit` or custom axiom occurs. The temporary probe was deleted, and the compiler slot released immediately.

SHA-256 of `.local/PolicyLearningVarianceTransfer.lean`: `b601af7ce8d8bc5935e11b299c27875ded4f50674d37867bd991c68f5464b9d0`.

This is staged builder evidence, not independent source certification. Imports already use integrated/pinned paths. Production integration should be independently reviewed, built and audited as actual exports.
