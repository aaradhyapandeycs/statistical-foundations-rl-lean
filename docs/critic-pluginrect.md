# Critic report: plug-in ℓ∞ rectangle (corrected C47(2)) (2026-11-10)

Public copy, scrubbed (local paths, probe files and agent identifiers removed). Independent review of `Formalization/TDInference/PluginCovariance/Rectangle.lean` with drafted statement entry `Eq_convex_Cdelta_rectangle_corrected_plugin`. Probes are local scratch files (`<local probe>`).

Integration note: verdict ACCEPT-WITH-FIXES; findings 5 and 7 applied (scaling relation R̂ = r̂_T/√T marked not formalized in the docstrings; module imported from `Formalization.lean` and `Statements/Ch7Proofs.lean`; stale "plug-in rectangle remains open" text updated in COVERAGE, SOURCE-ISSUES C47 and the Ch7 docstrings). The entry landed as drafted below, with the oracle-rectangle docstring wording adjusted; `Statements/Ch7.lean` Formalization.* imports unchanged.

Critic: independent (did not build). Date 2026-11-10. Read-only on Formalization/, docs/.
Target: `Formalization/TDInference/PluginCovariance/Rectangle.lean`, sha256
`e61ed5eb0976dccd2b38d50e4e5d36fb19c4f94e8ea4726878bc01aa78c20b1a`.
Source read: `source/upstream/tex/chapters/inference.tex:156–213` (estimators :165–177, `eq:defn-hat-Lambda`
:180–182, rule :187–196, rectangle (i) :198–205), Theorem 7.11 :132–141 (η₀ ∈ (0,1/4), λ₀ = min μ);
SOURCE-ISSUES C47 (1)–(4), C43.

## Verdict: ACCEPT-WITH-FIXES
Mathematics and Lean are sound; fixes are documentation/integration only.

## Evidence (commands run)
- `bash scripts/lean-local.sh Formalization/TDInference/PluginCovariance/Rectangle.lean` (guarded: <2 lean, no
  check_parallel): exit 0, no messages, ~15 s wall.
- `bash scripts/lean-local.sh <local probe>`: exit 0. `#print axioms` for
  `tendsto_coverage_rect_plugin`, `tendsto_coverage_rect_plugin_quantile`, `exists_delta_abs_supBoxProb_sub_lt`,
  `posSemidef_lambdaHat`, `isSupBoxQuantile_supBoxQuantile`, and the draft wrapper
  `Eq_convex_Cdelta_rectangle_corrected_plugin_holds`: [propext, Classical.choice, Quot.sound] only.
- `grep sorry|admit|axiom` on the target: none. No lake, no git.

## Findings
1. **gaussOfCov well defined (OK).** Factor-independence is proved: `gaussOfCov_eq_map` (any factor F, any
   finite column type, F Fᵀ = Σ) via `map_mulVec_stdGaussianPi_eq` (char.-function uniqueness). Agreement with the
   project's `gaussCov` at Λ = A⁻¹diag(Γ)A⁻ᵀ (Γ ≥ 0) checked in the scratch file (`example`, from
   `gaussCov_eq_map_mulVec` + `gaussCovFactor_mul_transpose`); the main proof uses the same factor L =
   `gaussCovFactor`, so `exists_confRegion_oracle_bounds` / `exists_supBox_level_eq` transport correctly
   (`hGL`). Suggestion (optional): export `gaussOfCov_eq_gaussCov` as a library lemma.
2. **Λ̂_T PSD on every outcome (OK).** `posSemidef_lambdaHat`: Γ̂_T = Σ w_t v vᵀ with w_t ≥ 0 is PSD and X Γ̂ Xᵀ
   is PSD for every X, including Lean's junk inverse 0 on the singular event (then Λ̂_T = 0, N(0,0) = δ₀).
   The `dirac 0` branch of `gaussOfCov` is therefore never reached for Λ̂_T. Not a fallback that changes content.
3. **Quantile notion (OK).** `IsSupBoxQuantile Σ α r` ⇔ r ∈ [q⁻, q⁺] with q⁻ = inf{F ≥ 1−α},
   q⁺ = inf{F > 1−α}, F the (right-continuous) cdf of ‖X‖∞: exactly the set of (1−α)-quantiles. With S ≥ 1
   and α < 1 it forces r ≥ 0 (F = 0 on (−∞,0)), so no negative half-widths. `supBoxQuantile` (sInf) = q⁻ is
   proved to satisfy it for α ∈ (0,1) (set nonempty by continuity from below, bounded below by 0). Edge cases:
   α ∉ (0,1) is excluded by hypothesis (printed 1−α ∈ (0,1), :189); on the singular event the quantile is 0
   (degenerate interval), probability → 0. The theorem quantifies over every per-outcome selection, which
   generalizes "the (random) quantile" (:205). No convergence of r̂_T is assumed.
4. **Continuity argument and sandwich (OK).** Checked by hand and by the compiler: entrywise δ ≤ κ/C gives
   |xᵀ(Σ−Λ)x| ≤ (κ/C)(Σ|xᵢ|)² ≤ κ xᵀΛx, hence P = Σ − (1−κ)Λ ⪰ 0; F = [√(1−κ)L | Q], F Fᵀ = Σ;
   |F − [L|0]| < δ₁ entrywise (|Qᵢⱼ|² ≤ Pᵢᵢ ≤ δ₁²/4 + κΛᵢᵢ ≤ δ₁²/2). Dominated convergence along F → F₀ with
   N(0,Λ)-null box frontier (`confCalib_frontier_null`, needs Γ_true ≻ 0). Order of limits is correct: ε → ν →
   fixed exact levels r⁻ (mass 1−α−ν), r⁺ (mass 1−α+ν) → δ's → bad event B_T → T large. On Bᶜ:
   F_Λ̂(r⁻) < 1−α ⇒ r⁻ ≤ r̂, F_Λ̂(r⁺) > 1−α ⇒ r̂ ≤ r⁺. Two-sided bounds via `pathProb_union_le`. Only two fixed
   levels are needed, no uniformity in r.
5. **Printed vs corrected (docstring claim correct but unproved — FIX, minor).** If X ~ N(0, Λ̂_T/T) then
   ‖X‖∞ =d ‖Y‖∞/√T with Y ~ N(0, Λ̂_T), so (T ≥ 1) the printed R̂ (quantile under Λ̂_T/T) is R̂ = r̂_T/√T, the
   printed half-width R̂/√T = r̂_T/T (C47(2)), and the corrected half-width r̂_T/√T = R̂. So the result is the
   printed rectangle with half-width R̂ instead of R̂/√T, i.e. C47's proposed correction. The module and theorem
   docstrings say "equivalently R̂ = r̂_T/√T …" as if established; this scaling identity is not formalized.
   Fix: append "(scaling identity of the Gaussian quantile; paper fact, not formalized)" or add a lemma
   `IsSupBoxQuantile ((T:ℝ)⁻¹ • Σ) α (r/√T) ↔ IsSupBoxQuantile Σ α r` (T > 0).
6. **Hypotheses (OK, disclosed).** `0 < η₀ ≤ 1` ⊇ printed (0,1/4); `Γ_true ≻ 0` is an added non-degeneracy
   hypothesis (stated in the docstring; consistent with the other plug-in entries; C43). Asymptotic only, no
   rate — stated. Limit covariance Λ = A⁻¹diag(Γ_true)A⁻ᵀ (C43) — stated.
7. **Integration (FIX, required at landing).** The file is unimported: add it to `Formalization.lean` and to
   `Statements/Ch7Proofs.lean`. Stale text that must change in the same change: COVERAGE row "Confidence-set
   rule" ("The plug-in ℓ∞ rectangle (C47(2)) remains open", "Open: … the plug-in rectangle"), SOURCE-ISSUES C47
   paragraph "Lean evidence for the corrected ellipsoid with the printed plug-in" ("The plug-in ℓ∞ rectangle …
   is still open"), and the `Eq_convex_Cdelta_ellipsoid_corrected_plugin` docstring ("Not covered: the plug-in
   ℓ∞ rectangle (C47(2))") and the oracle rectangle entries' "the plug-in version … remains open" (the plug-in
   version *with a rate* remains open; reword rather than delete).
8. **G2 import gate (OK, no change needed).** `gaussOfCov`/`supBoxQuantile` live in a proof module and
   `exists_mul_transpose_eq_of_posSemidef` is in `GaussianCovCompare` (proof module), so they cannot be used in
   `Statements/Ch7.lean`. The draft below avoids them: N(0, Λ̂_T) is written as the law of Q Z,
   Z ~ `Measure.pi (fun _ ↦ gaussianReal 0 1)`, for a factor Q Qᵀ = Λ̂_T quantified in the Prop. It needs only
   Mathlib + `TDInference711Defs` (already on the G2 list). Existence of such r̂ (non-vacuity) is a conjunct.
   Draft entry and wrapper compiled (scratch `pluginrect-critic/Draft.lean`).

## Draft statement entry (compiled in scratch; for Statements/Ch7.lean)
```lean
open StatisticalRL StatisticalRL.Ch7Rest.TDInference MeasureTheory ProbabilityTheory Matrix Filter Topology in
/-- Corrected, plug-in-covariance hyper-rectangle confidence region (`chapters/inference.tex:198–205`, item (i)
of the rule `eq:convex.Cdelta` :187–196; plug-in `Λ̂_T` `eq:defn-hat-Lambda` :180–182). See
`docs/SOURCE-ISSUES.md#C47` (items (2), (4)) and `#C43`.

Differs from the printed text: (1) half-width `r̂_T/√T` with `r̂_T` a `(1 − α)` quantile of `‖X‖∞`,
`X ~ N(0, Λ̂_T)`; the printed `R̂/√T` with `R̂` the quantile under `Λ̂_T/T` applies `√T` twice (C47(2)). Since
`R̂ = r̂_T/√T` (Gaussian scaling; not formalized), this is the printed rectangle with half-width `R̂`.
(2) Asymptotic coverage only; no rate (plug-in consistency `Eq_defn_hat_Lambda_corrected` has none).
(3) Added non-degeneracy hypothesis `Γ_true ≻ 0`; the limit covariance is `Λ = A⁻¹ diag(Γ_true) A⁻ᵀ` (C43).
(4) Junk value: on the singular event `Ā_T` (C47(4)) Lean's `Matrix.inv` gives `Λ̂_T = 0`, so `N(0, Λ̂_T)` is
the point mass at `0` and `r̂_T = 0`; that event has vanishing probability.
`N(0, Λ̂_T)` is written as the law of `Q Z`, `Z` standard Gaussian on `State → ℝ`, `Q Qᵀ = Λ̂_T` (`Λ̂_T` is always
PSD; the law does not depend on `Q`). `r̂` is a quantile when every `r` with box mass `< 1 − α` is `≤ r̂` and
every `r` with box mass `> 1 − α` is `≥ r̂`. Kept: i.i.d. sampling, full-support `μ`, `0 < η₀ < 1/4` (:133),
every `V₀`, `α ∈ (0,1)` (:189).

Statement: such quantile levels `r̂_T(ω)` exist, and for every choice of them,
`P(∀ s, V̄_T(s) − r̂_T/√T ≤ V^π(s) ≤ V̄_T(s) + r̂_T/√T) → 1 − α`. -/
def Eq_convex_Cdelta_rectangle_corrected_plugin : Prop :=
  ∀ (State Action : Type) [Fintype State] [DecidableEq State] [Nonempty State]
    [Fintype Action] [Nonempty Action]
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (μ : FiniteDistribution State) (η₀ : ℝ) (V₀ : State → ℝ),
    (∀ s, 0 < μ.prob s) → 0 < η₀ → η₀ < 1 / 4 → (∀ s, 0 < trueGamma M π μ s) →
    ∀ α : ℝ, 0 < α → α < 1 →
    (∃ rhat : (T : ℕ) → (Fin T → Tuple State Action) → ℝ,
      ∀ (T : ℕ) (ω : Fin T → Tuple State Action), ∃ Q : Matrix State State ℝ,
        Q * Qᵀ = lambdaHat M η₀ V₀ ω ∧
        (∀ r : ℝ, ((Measure.pi fun _ : State ↦ gaussianReal 0 1).map (Q *ᵥ ·)).real
            {x | ∀ s, |x s| ≤ r} < 1 - α → r ≤ rhat T ω) ∧
        (∀ r : ℝ, 1 - α < ((Measure.pi fun _ : State ↦ gaussianReal 0 1).map (Q *ᵥ ·)).real
            {x | ∀ s, |x s| ≤ r} → rhat T ω ≤ r)) ∧
    ∀ rhat : (T : ℕ) → (Fin T → Tuple State Action) → ℝ,
      (∀ (T : ℕ) (ω : Fin T → Tuple State Action), ∃ Q : Matrix State State ℝ,
        Q * Qᵀ = lambdaHat M η₀ V₀ ω ∧
        (∀ r : ℝ, ((Measure.pi fun _ : State ↦ gaussianReal 0 1).map (Q *ᵥ ·)).real
            {x | ∀ s, |x s| ≤ r} < 1 - α → r ≤ rhat T ω) ∧
        (∀ r : ℝ, 1 - α < ((Measure.pi fun _ : State ↦ gaussianReal 0 1).map (Q *ᵥ ·)).real
            {x | ∀ s, |x s| ≤ r} → rhat T ω ≤ r)) →
      Tendsto (fun T : ℕ ↦ ∑ ω : Fin T → Tuple State Action, pathWeight M π μ ω *
          {ω' : Fin T → Tuple State Action | ∀ s,
            prAverage M η₀ V₀ ω' s - rhat T ω' / Real.sqrt T ≤ M.valueFixedPoint π s ∧
              M.valueFixedPoint π s ≤ prAverage M η₀ V₀ ω' s + rhat T ω' / Real.sqrt T}.indicator 1 ω)
        atTop (𝓝 (1 - α))
```
Wrapper (Ch7Proofs; applies the export, only glue: `gaussOfCov_eq_map` rewriting, η₀ < 1/4 ⇒ η₀ ≤ 1):
```lean
theorem Eq_convex_Cdelta_rectangle_corrected_plugin_holds :
    Eq_convex_Cdelta_rectangle_corrected_plugin := by
  intro State Action _ _ _ _ _ M π μ η₀ V₀ hμ h0 h1 hΓ α hα0 hα1
  have h1' : η₀ ≤ 1 := by linarith
  refine ⟨⟨fun _ ω ↦ supBoxQuantile (lambdaHat M η₀ V₀ ω) α, fun T ω ↦ ?_⟩, fun rhat hrhat ↦ ?_⟩
  · have hS := posSemidef_lambdaHat M η₀ V₀ ω
    obtain ⟨Q, hQ⟩ := StatisticalRL.Probability.exists_mul_transpose_eq_of_posSemidef hS
    have hG := gaussOfCov_eq_map hS Q hQ
    obtain ⟨q1, q2⟩ := isSupBoxQuantile_supBoxQuantile (lambdaHat M η₀ V₀ ω) hα0 hα1
    refine ⟨Q, hQ, fun r hr ↦ q1 r ?_, fun r hr ↦ q2 r ?_⟩
    · rw [supBoxProb, hG]; exact hr
    · rw [supBoxProb, hG]; exact hr
  · refine tendsto_coverage_rect_plugin M π μ h0 h1' V₀ hμ hΓ hα0 hα1 rhat fun T ω ↦ ?_
    obtain ⟨Q, hQ, q1, q2⟩ := hrhat T ω
    have hG := gaussOfCov_eq_map (posSemidef_lambdaHat M η₀ V₀ ω) Q hQ
    refine ⟨fun r hr ↦ q1 r ?_, fun r hr ↦ q2 r ?_⟩
    · rw [supBoxProb, hG] at hr; exact hr
    · rw [supBoxProb, hG] at hr; exact hr
```
(The existence conjunct uses `posSemidef_lambdaHat`, `exists_mul_transpose_eq_of_posSemidef`,
`isSupBoxQuantile_supBoxQuantile` — library lemmas, not a second proof.)

## Five-bin (draft entry)
| binder | Lean | bin | citation |
|---|---|---|---|
| State, Action, Fintype, DecidableEq State, Nonempty ×2 | types/instances | TYPING | finite MDP, :49–64 |
| M, π, μ, V₀ | model, policy, sampling law, init | SOURCE/STANDING | :49–64, TD algorithm |
| η₀ | ℝ | STANDING | :133 |
| ∀ s, 0 < μ s | full support | STANDING | λ₀ = min μ in Thm 7.11 :138; C47(4) |
| 0 < η₀ < 1/4 | | STANDING | :133 |
| ∀ s, 0 < Γ_true s | non-degeneracy | DISCLOSED | docstring (3); C43; Thm 7.11 uses ‖Γ⁻¹‖ |
| α, 0 < α < 1 | | SOURCE | :189 |
| rhat | ℕ → paths → ℝ | SOURCE (random quantile) | :205 |
| quantile hyp. (∃Q, QQᵀ = Λ̂_T, two-sided quantile under law of QZ) | | SOURCE scale-corrected = DISCLOSED | C47(2); N(0,Λ̂_T) expanded; Λ̂_T junk on singular event C47(4) |
| conclusion: coverage → 1 − α | Tendsto | DISCLOSED (asymptotic, no rate) | :196 "approximate"; docstring (2) |
| existence conjunct | ∃ rhat | extra conclusion (non-vacuity) | — |
Counts: TYPING 6, SOURCE/STANDING 9, DISCLOSED 3, EXCESS 0. Junk checks: `Real.sqrt 0 = 0`, `x/0 = 0` at T = 0
only (irrelevant to the limit); `lambdaHat` junk disclosed; Prop self-contained; hypotheses satisfiable
(existence conjunct). Verdict for the draft entry: **PASS-DISCLOSED**.

## Proposed wording
COVERAGE (row "Confidence-set rule"), replace "The plug-in ℓ∞ rectangle (C47(2)) remains open" with:
"Corrected, plug-in Λ̂_T rectangle (`Eq_convex_Cdelta_rectangle_corrected_plugin`, exports
`tendsto_coverage_rect_plugin`, `tendsto_coverage_rect_plugin_quantile`,
[Rectangle.lean](../Formalization/TDInference/PluginCovariance/Rectangle.lean)): for every per-outcome
(1−α)-quantile r̂_T of ‖X‖∞, X ~ N(0, Λ̂_T) (e.g. the lower quantile), P(∀s, |V̄_T(s) − V^π(s)| ≤ r̂_T/√T) → 1 − α
(half-width r̂_T/√T = R̂, not the printed R̂/√T, C47(2)); asymptotic only, no rate; Γ_true ≻ 0; junk Λ̂_T = 0 on
the singular event (C47(4)) ([review](critic-pluginrect.md)). Open: the plug-in rectangle with a rate." and drop
"the plug-in rectangle" from the Open list.
SOURCE-ISSUES C47, new paragraph: "**Corrected rectangle with the printed plug-in Λ̂_T (2026-11-10,
`Formalization/TDInference/PluginCovariance/Rectangle.lean`).** For full-support μ, 0 < η₀ ≤ 1, every V₀, Γ_true ≻ 0 and
α ∈ (0,1): for every random level r̂_T that is, outcome by outcome, a (1−α)-quantile of ‖X‖∞ with X ~ N(0, Λ̂_T)
(N(0,Σ) := law of QZ, QQᵀ = Σ; Λ̂_T is always PSD), the rectangle ∏_s[V̄_T(s) ± r̂_T/√T] has coverage → 1 − α
(`tendsto_coverage_rect_plugin`; concrete lower quantile `tendsto_coverage_rect_plugin_quantile`). With R̂ the
quantile under Λ̂_T/T as printed, R̂ = r̂_T/√T (scaling; not formalized), so this is the proposed correction
'half-width R̂ (not R̂/√T)'. Asymptotic only, no rate. Independently critic-reviewed ([review](critic-pluginrect.md)).
Not author-approved." and change "The plug-in ℓ∞ rectangle with a random level (C47(2)) is still open." to
"… is now proved asymptotically (next paragraph); a rate remains open."
