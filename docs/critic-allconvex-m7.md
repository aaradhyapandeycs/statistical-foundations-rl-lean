# Critic review: M6.3 (TDInferenceConvexLin711.lean) and M7 (TDInferenceConvexAll711.lean)

Public copy, scrubbed (local paths, probe files and agent identifiers removed). Infrastructure review for the all-convex Theorem 7.11 route, not a source result: no COVERAGE row, statement-index entry or named-result change follows from it. Reviewed: the linearised statistic at `T^{-1/4}` (`Formalization/TDInference/ConvexSets/LinearisedRate.lean`) and the full statistic at `T^{-2/9}` over all convex sets (`Formalization/TDInference/ConvexSets/AllConvexRate.lean`), a partial result weaker than the printed `T^{-1/3}`. Probes are local scratch files (`<local probe>`).

Integration note: F2 (headings reworded to "Partial result toward Theorem 7.11 (not the printed result)"), F4 (`tdNoiseBound_nonneg'` removed in favour of `(tdNoiseBound_pos M π).le`), F6 (docstring notes that `η₀ ≤ 1` is weaker than the printed `η₀ < 1/4`) and F1 (import into `Formalization.lean`) were applied; plan-file references were removed from the module docstrings. F3 and F5 (duplicate generic lemma, placement of generic lemmas) are left as nits.

Date 2026-11-09. Critic independent of the builder. No library files edited.

Files reviewed (sha256 of the reviewed versions, before the integration fixes listed above):
- Formalization/TDInference/ConvexSets/LinearisedRate.lean  3d4b86bf276f737fe491c2415195fd2926f7815dbea64617465433572c983f9e
- Formalization/TDInference/ConvexSets/AllConvexRate.lean  fb12714d8c01a188bf378c7f2e3b78e1f67eadc1c54e2d590326c0200de21b8d

Commands run (guarded: at most 2 Lean processes, no check_parallel):
- `bash scripts/lean-local.sh Formalization/TDInference/ConvexSets/LinearisedRate.lean`: clean, no output (15 s).
- `bash scripts/lean-local.sh Formalization/TDInference/ConvexSets/AllConvexRate.lean`: clean, no output (16 s).
- Scratch file (scratchpad, not in repo) `#print axioms` on both exports: [propext, Classical.choice, Quot.sound].
  `#check` of the M7 export matches the statement quoted below.
- No `sorry`/`admit`/`axiom` in either file.

## Verdict: ACCEPT-WITH-FIXES (no blocking findings)

## What was checked

1. Statement fidelity.
   - `lawProb M π μ η₀ V₀ T C = ∑_ω pathWeight ω · 1_C(scaledError ω)`, `pathWeight = ∏_t μ(s_t)π(a_t|s_t)P(s'_t|s_t,a_t)`
     (the i.i.d. law of inference.tex:54–61), `scaledError = √T (V̄_T − V^π)`, `V̄_T = T⁻¹∑_{t=1}^T V_t`,
     `V_{t+1}` uses sample `ω t` with `η_{t+1} = η₀ (t+1)^{-2/3}` (inference.tex:72, 82, 88, 134). Correct.
   - `tdA = diag(μ)(I − γP_π)` (:110); `gaussCov A Γ = law of A⁻¹(√Γ ⊙ Z)` = N(0, A⁻¹diag(Γ)A⁻ᵀ); `trueGamma` is the
     C43-corrected diagonal. Correct and disclosed.
   - Quantifiers: `∃ K, 0 < K ∧ ∀ T ≥ 1, ∀ C convex, … ≤ K T^{-2/9}`. K is chosen before T and C;
     K = K₁ + Csh + S·K_E², all instance-only (K₁ itself from an ∃ before T). Not T- or C-dependent.
   - Hypotheses: `0 < η₀ ≤ 1` is weaker than the printed `0 < η₀ < 1/4`; `hμ` is the printed `λ₀ > 0`;
     `hΓ : Γ_true ≻ 0` is the C43 proposed-correction hypothesis (SOURCE-ISSUES C43 line "with Γ ≻ 0 assumed")
     and is disclosed in both docstrings. V₀ arbitrary (source has no restriction). No hidden strengthening.
   - Non-measurable C: the data side is a finite sum of indicators, meaningful for any set. `ν.real C` is
     `(ν C).toReal` with ν C the outer measure (inf over measurable supersets). The proof uses only
     `measureReal_mono`, `measureReal_union_le` (valid for arbitrary sets of a finite measure) and dependency
     lemmas (`abs_pexp_convex_sub_twinLaw_le_quarter`, `abs_real_convex_gaussian_sub_le`,
     `tdGaussCov_convexShell_le_diagMin`) whose signatures take arbitrary convex `K` without measurability.
     Nothing false is relied upon. Since Γ_true ≻ 0 makes ν absolutely continuous and convex frontiers are
     ν-null (`tdGaussCov_frontier_convex_eq_zero`), convex sets are ν-null-measurable, so the outer-measure
     reading coincides with the natural one; the claim is meaningful.

2. Non-vacuity. Probe `M7acProbe.g_allConvex` / `g_linConvex` <local probe>,
   probe.out) instantiate both exports on instance G (S = A = 2, γ = 1/2, s' = a, r(0,0) = 1 else 0, μ, π uniform,
   η₀ = 1/8). I re-derived by hand V^π = (3/4, 1/4) and Γ_true = (25/128, 1/128) ≻ 0. The bound is not forced
   vacuous: K is fixed per instance while T^{-2/9} → 0, so the statement gives convergence in convex distance at
   rate T^{-2/9}. (The `|P − N| ≤ 1` absorption in M6.3 is used only for the finitely many T < burn-in N, via
   `1 ≤ N^{1/4} T^{-1/4}`; K = |K₁| + N^{1/4} + 1 is T-independent. Correct.)

3. Math of the δ-shell argument (`abs_sum_indicator_sub_le_of_perturb`).
   Upper: 1_C(X) ≤ 1_{C^δ}(Y) + 1{‖X−Y‖>δ}; ν(C^δ) ≤ ν(C) + ν(shell). Lower: 1_I(Y) ≤ 1_C(X) + bad with
   I = {y | B̄(y,δ) ⊆ C}; ν(C) ≤ ν(I) + ν(shell) via `diff_innerParallel_subset_convexShell`. Both I and C^δ are
   convex (new lemma; `Convex.cthickening`), so the M6.3 bound applies to them. Chebyshev:
   1{‖Z‖_∞ > δ} ≤ ∑_s Z_s²/δ², giving S (K_E T^{-1/3})²/δ². With δ = T^{-2/9}: S K_E² T^{-2/3+4/9} = S K_E² T^{-2/9};
   shell Csh·δ; linear part K₁T^{-1/4} ≤ K₁T^{-2/9}. δ³ = T^{-2/3} is the balancing choice. Exponent arithmetic
   (`rpow_third_sq_div_rpow_twoNinths_sq`) correct. M6.3: reservoir Lindeberg (T^{-1/4}) + Gaussian–Gaussian
   comparison linear in entryMax(Λ_T − Λ) = O(T^{-1/3}) ≤ O(T^{-1/4}); lower covariance bounds for both sides
   supplied (reservoir condition; `quadForm_target_ge`, whose D = S R² + 1 bound I checked). Sound.

4. Docstrings: both say partial, not Theorem 7.11, no statement-index entry, weaker rate, instance constant,
   C43. Honest overall (see F2 for wording).

5. Axioms clean; no name collisions within a namespace (see F3).

## Findings

F1 (should-fix, integration) Formalization.lean (near line 941, after `TDInferenceConvexReservoir711`): neither
   new module is imported, so `lake build` / `Audit.lean` / `scripts/check.py` do not cover them yet, and
   docs/PROGRESS.md has no ownership entry for them. Lead must add both imports and the PROGRESS entry before
   claiming the results.

F2 (should-fix, wording) TDInferenceConvexAll711.lean:222 docstring opens "**Theorem 7.11 over all convex sets at
   the weaker rate `T^{-2/9}`**"; :4 module title "# Theorem 7.11, all-convex route (M7)"; similarly
   TDInferenceConvexLin711.lean:7. The body disclaims it, but a skimming reader (or the site reader that shows
   first lines) sees "Theorem 7.11". Rephrase to "Partial result toward Theorem 7.11 (not the printed result): …".

F3 (nit) TDInferenceConvexAll711.lean:42 `StatisticalRL.Probability.convex_setOf_closedBall_subset` duplicates
   `StatisticalRL.Analysis.ConvexSmoothIndicator.convex_setOf_closedBall_subset`
   (Formalization/Analysis/ConvexSmoothIndicator.lean:383). Different namespaces, so no clash today, but it is a
   duplicate proof; reuse the existing one.

F4 (nit) TDInferenceConvexLin711.lean:44 `tdNoiseBound_nonneg'` is a primed name with no unprimed sibling;
   `(tdNoiseBound_pos M π).le` (TDInferenceNoise711.lean:56) already gives it. Drop or rename `tdNoiseBound_nonneg`.

F5 (nit, hygiene) TDInferenceConvexAll711.lean:33–176: generic finite-weight lemmas
   (`abs_sum_indicator_sub_le_of_perturb`, `sum_mul_ite_lt_norm_le`) live in `StatisticalRL.Probability` inside a
   Ch7Rest file; consider moving them to a Probability/ module. Same for `abs_sub_le_one_of_mem_unit`
   (TDInferenceConvexLin711.lean:70), a generic fact placed in the TDInference namespace.

F6 (nit, docs) Plan §M7 names the file `TDInferenceConvex711.lean`; the built file is `TDInferenceConvexAll711.lean`.
   Update the plan/PROGRESS reference. Optionally also note in the M7 docstring that `η₀ ≤ 1` is weaker than the
   printed `η₀ < 1/4` and that convex sets are ν-null-measurable here, so "outer measure" is not a semantic caveat.

No source-fidelity overclaim, hidden hypothesis, vacuity or unsound step found.
