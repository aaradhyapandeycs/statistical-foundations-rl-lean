# Critic review: C47(2) printed rectangle under-coverage

Public copy of the independent critic report; local paths removed. The probe file named below (`Probe.lean`) was kept in a private folder and is not published.

Post-review note (added to this public copy, 2026-11-09): F1 was applied: the general standard-Gaussian and quantile lemmas (`stdCDF_zero`, `stdCDF_neg`, `strictMono_stdCDF`, `tendsto_stdCDF_atTop`, `gaussianReal_real_Icc_neg_self`, `gaussianReal_abs_le_mul_sqrt`, `two_mul_stdCDF_sub_one_le_gaussianReal`, `le_mul_sqrt_of_quantile`, `exists_two_mul_stdCDF_sub_one_ge`, `exists_two_mul_stdCDF_sub_one_eq`, `isQuantile_mul_sqrt`) moved to `Formalization/Probability/GaussianQuantile.lean` (namespace `StatisticalRL.Probability.Stein`), and the small helpers (`sqrt_coe_toNNReal`, `sqrt_one_div_eq`, `tendsto_mul_sqrt_one_div`, `abs_sub_le_of_mem_pi_Icc`, `sum_pathWeight_indicator_*`) are now `private`; the moved proof of `gaussianReal_abs_le_mul_sqrt` now uses a private scaling lemma in the new file instead of `gaussianReal_eq_map_mul_add` (a Chapter 7 lemma). The two Props, their proofs and the other theorem statements are unchanged, so the file hash and line count quoted below refer to the reviewed version. F2 was applied: both modules are imported by `Formalization.lean`, and the full `Audit.lean` axiom audit passes. F3 and F4 were applied: the addendum below was added to C47 in `SOURCE-ISSUES.md` without citing the finite-T figures as machine-checked. The review text below is otherwise unchanged.

Reviewer: independent critic (not the builder). Date 2026-11-09.
File under review: `Formalization/TDInference/Confidence/PrintedRectangleEvidence.lean`
(SHA-256 c7697b02f5f01c8c2c5fe6d7bdf127dfd11df4960b57393e3348bfaa53258d45, 395 lines).
Source: `chapters/inference.tex` (pinned SHA-256 82707713adb6c9296d9ee41faa84b2d0a12eaf1b34864a6d294de02132e648f2, matches pin),
rule :187–196, rectangles :198–205, plug-in :180–182, step size :133.

## Verdict: ACCEPT WITH FIXES

The mathematics and encoding are sound. The fixes are integration and hygiene items, plus the
SOURCE-ISSUES addendum below. No fix touches the two Props or their proofs.

## Commands run (by the critic)

- `bash scripts/lean-local.sh Formalization/TDInference/Confidence/PrintedRectangleEvidence.lean`: exit 0, no output
  (no errors or warnings). One Lean process at a time, gated on `pgrep -x lean | wc -l` < 2.
- Probe `Probe.lean` (private; imports `Formalization` and the module; module
  olean newer than source): exit 0. `#print axioms` gives exactly `[propext, Classical.choice, Quot.sound]` for
  `c47_rectangle_printed_undercovers`, `c47_rectangle_printed_undercovers_plugin`,
  `oracleRectangle_coverage_le`, `exists_oracle_rectangle_quantile`, `exists_plugin_rectangle_quantile`,
  `isQuantile_mul_sqrt`, `le_mul_sqrt_of_quantile`. The probe also contains an `example` that combines
  `exists_oracle_rectangle_quantile` with `c47_rectangle_printed_undercovers` at η₀ = 1, V₀ = 0, which elaborates
  (so the hypotheses are jointly satisfiable and the conclusion is actually reached).
- `grep sorry|admit|axiom` on the module: no hits.

## Findings

R1 (fidelity, PASS). Printed text :205: R̂ > 0 is "the (random) quantile of the ℓ∞ norm of a centered Gaussian
random vector with covariance Λ̂_T/T"; half-width R̂/√T at :202. The Props use variance Λ/T (oracle) or
Λ̂_T(ω)/T (plug-in, pathwise), ℓ∞ norm = |x| for S = 1 (Unit → ℝ, `Set.univ.pi` box), and half-width
`R T / √T`. This is the printed rule, not a straw man. The level 1 − α is not printed next to R̂ but is
forced by `eq:convex.Cdelta` (:191–193); lower-quantile encoding (mass ≥ 1−α at R, < 1−α below R) is a fair
reading, and the proofs only use the "< 1−α below R" half, i.e. the result holds for every R̂ at most the
lower quantile, which also covers any upper-quantile/other tie conventions since for N(0,v), v > 0, the
quantile is unique (continuous strictly increasing CDF). Printed "R̂ > 0" is not imposed; omitting it only
widens the class of R covered (the Prop is stronger). Minor note: display :193 prints the covariance as
`\widehat{Λ/T}`, a typographical variant; it does not affect the reading.

R2 (one instance suffices, PASS). The printed rectangle claim is universal ("such sets serve as approximate
confidence regions", :196, with (i) as a natural choice); a single model (S = 1, instance O of
TDInferenceC47Evidence711, step-size range 0 < η₀ ≤ 1 containing the printed 0 < η₀ < 1/4 of :133, all V₀)
where coverage → 0 refutes it. Disclosed in the module docstring. The module does not claim anything about
the multi-dimensional ℓ∞ quantile; disclosed.

R3 (derivations, PASS). Oracle: `le_mul_sqrt_of_quantile` gives R_T ≤ z√(Λ/T) = z/√T (Λ = 1 via
`oneState_oracleLambda`), so half-width ≤ z/T = (z/√T)·√(1/T); the half-space two-sided bound
`abs_coverage_twoSided_sub_le` (u = 1, level ℓ = z/√T ≥ 0) yields coverage ≤ 2Φ(z/√T) − 1 + 2K T^{-1/3}
with K independent of T and of ℓ, and 2Φ(0) − 1 = 0. Correct; K is existential and uniform in α, z, T, R.
Plug-in: R_T(ω) ≤ z√(Λ̂_T(ω)/T) (via `sqrt_coe_toNNReal`, consistent with `Real.sqrt` of a negative being 0,
which is also how `tendsto_coverage_twoSided_plugin` reads the radius), half-width ≤ c√(Λ̂_T/T) once
z/√T < c, and the plug-in two-sided limit 2Φ(c) − 1 (from consistency `eq_defn_hat_Lambda_corrected`) is
below any b > 0 for small c > 0. Correct; qualitative only (no rate), disclosed.

R4 (non-vacuity, PASS). `isQuantile_mul_sqrt` proves R = z√v is the exact lower quantile for all v ≥ 0,
including v = 0 (point mass; then R = 0 and every R' < 0 gives mass 0 < 1 − α). Hence both Props'
hypotheses are satisfiable, including on paths with Λ̂_T(ω) ≤ 0 (read as N(0,0) via toNNReal; in instance O
Λ̂_T = 4Γ̂_T ≥ 0, so the negative case is not exercised). Note on R̂ > 0: on paths with Λ̂_T(ω) = 0 the exact
quantile is 0, so the printed "R̂ > 0" cannot hold there; this is harmless (Prop does not assume R̂ > 0) but
could be mentioned.

F1 (helper names; fix before merge, low severity). Generic declarations are placed in
`StatisticalRL.Ch7Rest.TDInference`: `stdCDF_zero`, `stdCDF_neg`, `strictMono_stdCDF`,
`tendsto_stdCDF_atTop`, `gaussianReal_real_Icc_neg_self`, `gaussianReal_abs_le_mul_sqrt`,
`two_mul_stdCDF_sub_one_le_gaussianReal`, `le_mul_sqrt_of_quantile`, `exists_two_mul_stdCDF_sub_one_ge/_eq`,
`isQuantile_mul_sqrt`, `sqrt_coe_toNNReal`, `sqrt_one_div_eq`, `tendsto_mul_sqrt_one_div`,
`abs_sub_le_of_mem_pi_Icc`, `sum_pathWeight_indicator_*`. No current collision in `Formalization/` (grepped),
but the file opens `StatisticalRL.Probability.Stein`, where `stdCDF` lives; if `stdCDF_neg`/`stdCDF_zero`
are later added there, every file opening both namespaces gets ambiguous-identifier errors. Recommended:
move the stdCDF / Gaussian-quantile lemmas into `Formalization/Probability/SteinGaussian.lean` (namespace
`StatisticalRL.Probability.Stein`) or a new `Formalization/Probability/GaussianQuantile.lean`; make
`sqrt_coe_toNNReal`, `sqrt_one_div_eq`, `tendsto_mul_sqrt_one_div`, `abs_sub_le_of_mem_pi_Icc` `private`
(or check Mathlib: `Real.sqrt_inv`, `Real.coe_toNNReal`). Not blocking if deferred, but record it.

F2 (integration, required). The module is not imported from `Formalization.lean`, so the repo axiom audit
does not cover it yet. Add the import (and to any gate list such as `scripts/gates/*` if module lists are
checked) in the integrating change.

F3 (ledger, required). SOURCE-ISSUES C47 still lists "(2)" as open and says (2) is "Paper calculation, not
Lean-checked". Add the addendum below; do not change the C47 header text or the printed-issue description.
No statement-index entry is needed: these are library refutation Props, not proved source results.

F4 (not overclaimable). The finite-T claim "printed set violates eq:convex.Cdelta for T > 1" and the
number 0.16 at T = 100 are NOT machine-checked by this module (the module's quantitative bound carries an
unknown constant K). The addendum must not cite them as Lean-checked.

## Final addendum text (for docs/SOURCE-ISSUES.md, C47)

**Lean evidence for (2) (2026-11-09, `Formalization/TDInference/Confidence/PrintedRectangleEvidence.lean`).** On the
one-state instance of (1) (S = 1, oracle Λ = 1; all 0 < η₀ ≤ 1, which contains the printed range
0 < η₀ < 1/4 of `:133`, and all V₀), the printed rectangle `∏_s [V̄_T(s) − R̂/√T, V̄_T(s) + R̂/√T]`
(`:201–203`), with R̂ any number at most the lower (1−α)-quantile of `‖X‖∞`, X ~ N(0, covariance/T)
(`:205`), has coverage tending to 0, for every 0 < α < 1, both with the oracle covariance Λ
(`C47_rectangle_printed_undercovers`, via the bound coverage ≤ 2Φ(z/√T) − 1 + 2K·T^(-1/3) for any z ≥ 0
with 2Φ(z) − 1 ≥ 1 − α, `oracleRectangle_coverage_le`, a corollary of the half-space result, no CLT) and with
the printed plug-in Λ̂_T taken pathwise (`C47_rectangle_printed_undercovers_plugin`, via the plug-in two-sided
limit and consistency of Λ̂_T; qualitative, no rate). The quantile hypotheses are satisfiable: R = z√v is the
exact lower quantile for every variance v ≥ 0, including the point mass v = 0
(`exists_oracle_rectangle_quantile`, `exists_plugin_rectangle_quantile`). For S = 1 the ℓ∞ quantile is the
two-sided Gaussian quantile; nothing about the S-dimensional ℓ∞ quantile is formalized, and one instance
suffices to refute the printed general claim. The finite-T figures in (2) (coverage 2Φ(1.96/√T) − 1, 0.16 at
T = 100, violation of `eq:convex.Cdelta` for T > 1) remain paper calculations. Independently critic-reviewed
([review](critic-c47r.md)). Not author-approved.
