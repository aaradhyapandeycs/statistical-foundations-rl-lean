# Critic report: chi-squared law of Gaussian quadratic forms + TD ellipsoid at the chi^2(S) quantile (2026-11-10)

Public copy, scrubbed (local paths, probe files and agent identifiers removed). Independent review of the χ²(k) law of Gaussian quadratic forms (`Formalization/Probability/ChiSquaredQuadForm.lean`) and the corrected oracle ellipsoid at the χ²(S) quantile (`Formalization/Ch7Rest/TDInferenceConfChiSq711.lean`, exports `gaussCov_ellipsoid_eq_chiSquared`, `exists_chiSquared_quantile`, `exists_confRegion_oracle_chiSquared`), with drafted statement entry `Eq_convex_Cdelta_ellipsoid_corrected_oracle_chiSquared`. Probes are local scratch files (`<local probe>`).

Integration note: verdict ACCEPT-WITH-FIXES; findings 4, 6 and 7 applied (the entry includes the quantile-existence conjunct; χ²(S) is written inline as `gammaMeasure (card State / 2) (1/2)` with Mathlib gamma/CDF imports only, so the frozen `Formalization.*` imports of `Statements/Ch7.lean` are unchanged; both modules imported from `Formalization.lean` and the TD module from `Statements/Ch7Proofs.lean`; stale "χ²(S) identification not proved" text updated in the `_corrected_oracle` and `_calibrated` docstrings, `TDInferenceConfCalib711.lean`, the COVERAGE `eq:convex.Cdelta` row and the SOURCE-ISSUES C47 addendum). The entry landed as drafted below, with an expanded docstring.

Reviewed files sha256: `TDInferenceConfChiSq711.lean` a7c44f38bbd278562c9345c79ca2cce77ff662c8bd920569da0f3dcdbe3e440c (108 lines), `ChiSquaredQuadForm.lean` 1266d744a3a7930fe70e40aea950a1562837108f2d76aada00583a619b8b190b (232 lines).

Targets: Formalization/Probability/ChiSquaredQuadForm.lean, Formalization/Ch7Rest/TDInferenceConfChiSq711.lean (unimported at review time).
Source: chapters/inference.tex:207-213; SOURCE-ISSUES C47(3). Critic did not edit Formalization/, docs/, Formalization.lean.

## Verdict: ACCEPT-WITH-FIXES (fixes are integration/doc only; no Lean change required)

## Evidence (commands actually run, all EXIT 0, no errors/warnings)
- bash scripts/lean-local.sh Formalization/Probability/ChiSquaredQuadForm.lean
- bash scripts/lean-local.sh Formalization/Ch7Rest/TDInferenceConfChiSq711.lean
- bash scripts/lean-local.sh <local probe> (sanity checks)
  #print axioms on 11 exports: all [propext, Classical.choice, Quot.sound].
  Sanity (proved): cdf (chiSquared 2) q = 1 - exp(-q/2) for q >= 0 (via Mathlib expMeasure = gammaMeasure 1 r),
  and cdf (chiSquared 2) (2 log 20) = 1 - 1/20, i.e. the textbook 95% chi^2(2) quantile 5.991.
- bash scripts/lean-local.sh <local probe> (draft entry, imports only
  Mathlib.Probability.Distributions.Gamma, Mathlib.Probability.CDF, Formalization.Ch7Rest.TDInference711Defs)
- bash scripts/lean-local.sh <local probe> (draft entry + _holds wrapper; axioms clean)

## Findings
1. chi^2 definition correct. Mathlib gammaPDFReal a r x = r^a/Gamma(a) x^(a-1) e^(-r x) on x >= 0: r is a RATE.
   gammaMeasure (k/2) (1/2) is the standard chi^2(k) (density x^(k/2-1)e^(-x/2)/(2^(k/2)Gamma(k/2))). The proved MGF
   (r/(r-t))^a is the rate form; k=2 numeric sanity confirms. PASS.
2. MGF uniqueness (ext_of_integral_exp_eq_of_lt): sound. Integrability for all t<c gives Iio c in integrableExpSet,
   hence {Re z < c} is inside the analyticity domain of complexMGF (Mathlib analyticOnNhd_complexMGF). The half-plane is
   convex hence preconnected, contains 0 (c>0), and the real points -1/(n+1) -> 0, n != 0, lie in it, so the identity
   theorem gives agreement on the whole half-plane, which contains the imaginary axis (Re = 0 < c); complexMGF id mu (tI)
   = charFun mu t, then Measure.ext_of_charFun (finite measures). Hypothesis c > 0 is genuinely needed and assumed.
   Integrability of the pushforward is derived from a nonzero integral value (Integrable.of_integral_ne_zero) - valid
   since the integral would be 0 junk otherwise. No gap found. PASS.
3. Linear image: gaussCov A Gamma = law of A^-1(sqrt Gamma . Z) = law of L Z with L = gaussCovFactor = A^-1 diag(sqrt Gamma);
   gaussCovFactor_mul_transpose gives L L^T = A^-1 diag(Gamma) (A^-1)^T, syntactically trueLambda. L invertible from
   tdA invertible (full-support mu) and Gamma_true > 0. quadForm identity x^T (L L^T)^-1 x = |z|^2 proved with genuine
   nonsingular inverses. PASS.
4. TD corollary quantifiers: exists K0 > 0 (taken from exists_confRegion_oracle_bounds, independent of alpha and q),
   forall alpha in (0,1), forall q with F_{chi^2(S)}(q) = 1-alpha: Gaussian mass = 1-alpha and coverage bound for all
   T >= 1. Composition: rewrites the Gaussian term of component .2.1 of the accepted export by 1-alpha. Correct.
   Note: chi^2(S) cdf is continuous and strictly increasing on (0,inf), so "every quantile" = the unique quantile R.
   The forall-q form is vacuous on its own if no q existed; existence is a separate lemma (exists_chiSquared_quantile).
   FIX (entry): include the existence conjunct in the statement entry (draft below does).
5. Docstrings honest: threshold q = R not R^2, d = S, oracle Lambda (plug-in not treated), extra log(2T) all stated.
   Minor: library export assumes eta0 <= 1 (weaker than printed 0 < eta0 < 1/4); fine, wrapper uses linarith.
6. FIX (integration, stale text): after landing, update text that says the chi^2 identification is open/not part:
   Statements/Ch7.lean docstrings of Eq_convex_Cdelta_ellipsoid_corrected_oracle (~:825-827) and
   ..._calibrated (~:893-894); COVERAGE.md eq:convex.Cdelta row ("Not proved: the chi^2(S) law of x^T Lambda^-1 x",
   "Open: the chi^2(S)/l_inf-quantile identification"); SOURCE-ISSUES C47 addendum (:1620 "Still open: the chi^2(S)
   ..."). Keep: l_inf-quantile identification, plug-in Lambda-hat versions, printed R^2 formula, log-free rate remain open.
7. Imports for the entry: g2_statement_imports.txt freezes Formalization.* edges of Statements/ChN.lean ("may only shrink");
   ChiSquaredQuadForm is a new edge and contains proofs, so it may NOT be imported by Ch7.lean. Mathlib imports are not
   gated (only bare `import Mathlib` is). So chi^2(S) is written inline as gammaMeasure (card State / 2) (1/2) with
   added imports Mathlib.Probability.Distributions.Gamma and Mathlib.Probability.CDF (verified to elaborate).
   Ch7Proofs.lean must import Formalization.Ch7Rest.TDInferenceConfChiSq711; Formalization.lean must import both new files.

## Draft entry (compiled in <local probe>)
Prop: forall State Action [Fintype State][DecidableEq State][Nonempty State][Fintype Action][Nonempty Action] M pi mu eta0 V0,
 (forall s, 0 < mu.prob s) -> 0 < eta0 -> eta0 < 1/4 -> (forall s, 0 < trueGamma M pi mu s) ->
 exists K0 > 0, forall alpha, 0 < alpha -> alpha < 1 ->
  (exists R >= 0, cdf (gammaMeasure (card State/2) (1/2)) R = 1 - alpha) /\
  forall R, cdf (gammaMeasure (card State/2) (1/2)) R = 1 - alpha ->
   N(0,Lambda).real {x | sum x_s x_s' Lambda^-1 ss' <= R} = 1 - alpha /\
   forall T >= 1, |P(T (V^pi - Vbar_T)^T Lambda^-1 (V^pi - Vbar_T) <= R) - (1 - alpha)| <= K0 T^(-1/3) log(2T),
 with Lambda = (tdA)^-1 * diagonal (trueGamma) * (tdA)^-1 transposed written out.
Wrapper: obtain from exists_confRegion_oracle_chiSquared (eta0 <= 1 by linarith) + exists_chiSquared_quantile Fintype.card_pos.

## Five-bin (draft entry)
| binder | bin | citation |
|---|---|---|
| State, Action, Fintype x2, DecidableEq, Nonempty State, Nonempty Action | TYPING (7) | finite MDP conventions |
| M, pi, mu | SOURCE | :49-64 |
| eta0, V0 (forall) | SOURCE | :133, :72 |
| forall s, 0 < mu.prob s | STANDING | :51-67 |
| 0 < eta0, eta0 < 1/4 | STANDING | :133 |
| forall s, 0 < trueGamma | DISCLOSED (C43/C47; Thm 7.11 definedness of Gamma^-1) | |
| exists K0 > 0 before alpha, T | DISCLOSED (rate form, instance constant) | |
| alpha in (0,1) | SOURCE | :213 |
| R with F_{chi^2(S)}(R) = 1-alpha | SOURCE (R the 1-alpha quantile, d = S) | :213, C47(3) |
| forall T >= 1 | SOURCE | |
| threshold R not R^2; oracle Lambda; extra log(2T) | DISCLOSED | C47(3), C43 |
Counts: TYPING 7, SOURCE 7, STANDING 3, DISCLOSED 5, EXCESS 0. PASS-DISCLOSED (corrected oracle variant, not the printed formula).
