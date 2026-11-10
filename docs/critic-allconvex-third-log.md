# Critic review: abs_lawProb_convex_sub_gaussCov_le_third_log

Public copy, scrubbed (local paths, probe files and agent identifiers removed). Infrastructure review of `Formalization/Ch7Rest/TDInferenceConvexThird711.lean` (written by the lead; reviewed independently). Partial result toward Theorem 7.11, not a source result; no statement-index entry. Probes are local scratch files (`<local probe>`).

Integration note: verdict ACCEPT WITH FIXES; all three applied (module title says log(2T); module imported in `Formalization.lean`; COVERAGE Theorem 7.11 row rewritten as recommended).

Target: Formalization/Ch7Rest/TDInferenceConvexThird711.lean (lead-authored; reviewed independently, no edits made).
Source: Theorem 7.11, thm:Berry-Esseen-linear, source/upstream/tex/chapters/inference.tex:132-141 (d_cvx at 124-127, Lambda* / Gamma at 104-117).

## Verdict: ACCEPT-WITH-FIXES (fixes are documentation/integration only; the Lean theorem is accepted as is)

## Checks

1. Statement. `∃ K, 0 < K ∧ ∀ T ≥ 1, ∀ C, Convex ℝ C → |lawProb M π μ η₀ V₀ T C − (gaussCov (tdA) (trueGamma)).real C| ≤ K·(T^(-1/3)·log(2T))`.
   K is chosen after (M, π, μ, η₀, V₀) and before T and C, so it is a uniform-in-T, uniform-over-convex-sets bound.
   Binders are identical to `abs_lawProb_convex_sub_gaussCov_le_quarter` (TDInferenceConvexLog711.lean:219-225):
   [Nonempty State], h0 : 0 < η₀, h1 : η₀ ≤ 1, V₀, hμ (full support), hΓ (Γ_true ≻ 0). No extra hypotheses.
   The proof is a direct composition of `abs_linLaw_convex_sub_gaussCov_le_third` (same binders minus V₀) and
   `abs_lawProb_convex_sub_gaussCov_le_of_linRate` with a = 1/3; no hidden inputs.
   Non-vacuity: probe instance G (Γ_true = (25/128, 1/128) ≻ 0, η₀ = 1/8, every V₀) instantiates it (`g_allConvex_third_log`).

2. Algebra. For T ≥ 1: log 2 ≤ log(2T), log 2 > 0, so 1 ≤ log(2T)/log 2 and T^(-1/3) ≤ (1/log 2)·T^(-1/3)·log(2T)
   (T^(-1/3) ≥ 0). Hence K(T^(-1/3) + T^(-1/3)log(2T)) ≤ K(1/log 2 + 1)·T^(-1/3)log(2T). Final constant
   K(1/log 2 + 1) ≈ 2.443 K > 0. Correct.

3. Honesty vs source. Docstrings correctly state: partial result, not Theorem 7.11, no statement-index entry;
   extra log(2T) factor vs printed T^(-1/3); instance constant (may depend on M, π, μ, η₀, V₀), printed coefficient
   not established; covariance Γ_true (C43) assumed ≻ 0; η₀ ∈ (0,1] covers the printed (0,1/4); the printed
   rate without log remains open. "Outer measure" remark for non-measurable C is accurate (`Measure.real` of a set).
   This is consistent with how the T^(-1/4) theorem is described and with the COVERAGE row's existing claims.

4. Compilation (this critic, 2026-11-10):
   - `bash scripts/lean-local.sh Formalization/Ch7Rest/TDInferenceConvexThird711.lean`: rc 0, no output (no errors/warnings), ~2 s.
   - `bash scripts/lean-local.sh <local probe>: no errors/warnings/sorry, ~24 s.
     `#print axioms` for `abs_lawProb_convex_sub_gaussCov_le_third_log` and `g_allConvex_third_log`:
     [propext, Classical.choice, Quot.sound]. All other probed exports likewise.
   No lake, no git used.

## Findings

1. (minor, doc) Module header title says "`T^{-1/3} log T`"; the theorem is `T^{-1/3} log(2T)` (log T vanishes at T = 1,
   so the distinction matters for the stated range T ≥ 1). Change the title to `log(2T)`.
2. (integration) The module is not yet imported from Formalization.lean, so the project axiom audit does not
   cover it. Add `import Formalization.Ch7Rest.TDInferenceConvexThird711` when integrating.
3. (docs/COVERAGE.md, Theorem 7.11 row) After integration the row should:
   - name the new headline partial all-convex result: with Γ_true ≻ 0, printed step sizes (0 < η₀ ≤ 1, covering
     the printed 0 < η₀ < 1/4), full-support i.i.d. sampling and every V₀, there is an instance constant K with
     |P(√TΔ̄_T ∈ C) − N(0, A⁻¹Γ_trueA⁻ᵀ)(C)| ≤ K·T^(-1/3)·log(2T) for all T ≥ 1 and all convex C
     (TDInferenceConvexThird711.lean, export `abs_lawProb_convex_sub_gaussCov_le_third_log`; linear part at
     T^(-1/3) in TDInferenceConvexLinSharp711.lean, export `abs_linLaw_convex_sub_gaussCov_le_third`);
     keep the T^(-1/4) and T^(-2/9) results as earlier/weaker bounds;
   - replace the counterfactual "so even a = 1/3 would leave a log factor short" with the fact that a = 1/3 is now
     proved and the remaining gap to the printed rate is exactly the log(2T) factor (plus the printed coefficient);
   - keep: "partial, not a restricted variant, not counted in the ledger, no named-result entry", Γ_true / C43,
     "Theorem 7.11 over all convex sets at the printed rate T^(-1/3) remains open", not author-approved;
   - link this review and the two m5b2 reviews (CRITIC-allconvex-m5b2-A/-B, copied into docs/ as the project does
     for other critic reports).
   No statement-index entry or named-result-status change is warranted (not the printed result, not a disclosed
   corrected/restricted variant of it).
