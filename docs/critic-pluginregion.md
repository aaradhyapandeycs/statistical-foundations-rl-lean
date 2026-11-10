# Critic report: Formalization/Ch7Rest/TDInferencePluginRegion711.lean (plug-in χ²(S) ellipsoid)

Public copy, scrubbed (local paths, probe files and agent identifiers removed). Independent review of the plug-in-covariance confidence ellipsoid (`Formalization/Ch7Rest/TDInferencePluginRegion711.lean`; exports `tendsto_coverage_ellipsoid_plugin`, `tendsto_coverage_ellipsoid_plugin_chiSquared`), with drafted statement entry `Eq_convex_Cdelta_ellipsoid_corrected_plugin`. Probes are local scratch files (`<local probe>`).

Integration note: verdict ACCEPT; minor 7 applied (the theorem docstring now cites `inference.tex:180–182`); minor 8 kept (the unused α hypotheses match the printed quantifier). The entry landed as drafted below (section EqConvexCdelta of `Statements/Ch7.lean`, no new `Formalization.*` imports), with its `_holds` wrapper in `Ch7Proofs.lean`; module imported from `Formalization.lean`. COVERAGE and SOURCE-ISSUES C47(3) wording applied; the plug-in rectangle and a finite-T rate stay open.

Critic, independent of the builder. Read-only review: no edits to Formalization/, docs/ or Formalization.lean.
Source: source/upstream/tex/chapters/inference.tex:180-182 (eq:defn-hat-Lambda), :187-196 (eq:convex.Cdelta), :207-213 (ellipsoid item (ii)).

## Verdict: ACCEPT (two minor non-blocking notes, findings 7 and 8)

## Evidence
- `bash scripts/lean-local.sh Formalization/Ch7Rest/TDInferencePluginRegion711.lean`: rc=0, no output (no errors or warnings), 11 s. 
- The olean in .lake/build has mtime 1794307467, newer than the source (1794307462), so the axiom probe tests the current text.
- `<local probe>`: both exports and the helpers continuous_cdf_chiSquared, exists_inv_entry_close and exists_sum_abs_sq_le_mul_sumSq use only [propext, Classical.choice, Quot.sound]. Log: axioms.log
- The file contains no sorry, admit or axiom.

## Findings
1. Event fidelity: PASS. The event is `T * Σ_{s,s'} (V^π(s) − V̄_T(s))(V^π(s') − V̄_T(s')) (lambdaHat)⁻¹(s,s') ≤ q`. `M.valueFixedPoint π` is the unique fixed point of the policy Bellman operator, which is V^π. `prAverage` is V̄_T = T⁻¹ Σ_{t=1}^T V_t. `lambdaHat` is exactly Ā_T⁻¹ Γ̂_T Ā_T⁻ᵀ with the printed weights. The printed set is {V : T(V − V̄_T)ᵀ Λ̂⁻¹ (V − V̄_T) ≤ R²}; coverage means V = V^π. Because the form is quadratic, the sign of V − V̄ does not matter. The threshold is R rather than R², the disclosed C47(3) correction, and the scaling T matches the print.
2. Sandwich: PASS. Off the bad event B_T = {∃ s s', δ < |Λ̂ − Λ|}, `exists_inv_entry_close` gives entrywise error κ/C in the inverse. `abs_quadForm_sub_le` together with (Σ|x|)² ≤ C·xᵀΛ⁻¹x gives |plug-in form − Q| ≤ κQ, where Q ≥ 0. The inclusions are E ⊆ {Q ≤ q/(1−κ)} ∪ B and {Q ≤ q/(1+κ)} ⊆ E ∪ B. Both hold for q of either sign. The algebra is checked: (1−κ)Q ≤ plug-in ≤ q, and Q ≤ q/(1+κ) ⇒ plug-in ≤ (1+κ)Q ≤ q.
3. Singular or junk event: PASS. When Ā_T is singular, lambdaHat = 0. Then |0 − Λ_ss| = Λ_ss > 0, so the outcome lies in B_T once δ < min Λ_ss. B_T is controlled by eq_defn_hat_Lambda_corrected for every δ > 0; that result is critic-accepted and is invoked here with `0 < η₀ ≤ 1`. The junk value 0⁻¹ = 0 never enters the good-event algebra.
4. Order of limits: PASS. Given η > 0, the proof first fixes κ ∈ (0, 1/2) so that |F(q/(1±κ)) − F(q)| < η/3 (continuity of F). It then fixes δ(κ) and only after that takes T large: P(B_T) < η/3 and K₀T^{-1/3}log(2T) < η/3. κ is not a function of T, so the argument is a sound ε-argument. The limit is pointwise in q, as disclosed.
5. q ≤ 0 and q = 0: PASS. Nothing in the proof assumes the sign of q. For q < 0 the limit is F(q) = 0. For q = 0 continuity gives F(0) = 0; χ²(S) has no atom, by `continuous_cdf_chiSquared`, which uses S ≥ 1 from Nonempty State. So the limit is still 0, although on the singular event the junk form 0 ≤ 0 holds, and that event's mass tends to 0.
6. Docstrings: PASS. They say asymptotic only with no rate, the threshold is corrected (R, not R²), Γ_true ≻ 0 is an added hypothesis, the limit covariance is the corrected one (C43), and the junk value follows C47(4). They also say the plug-in ℓ∞ rectangle (C47(2)) and data-selected sets (C47(1)) are not covered.
7. (minor) The module docstring cites the source range 198–213 and the theorem docstrings cite 207–213. The plug-in Λ̂ range :180–182 is cited only in the module docstring. Adding :180–182 to the theorem docstring of `tendsto_coverage_ellipsoid_plugin` is optional.
8. (minor) The `_chiSquared` export takes α hypotheses that it does not use (`_hα0`, `_hα1`). This is harmless, and keeping them matches the printed quantifier.

## Statement entry
Add one. Bin: **corrected**, with two disclosed deviations from the print: threshold R instead of R², and a limit with no rate. Γ_true ≻ 0 is an added hypothesis and the limit covariance is the C43 Λ.

Draft for Formalization/Statements/Ch7.lean. It needs no new imports: lambdaHat, prAverage, pathWeight and trueGamma all come from TDInference711Defs, which is already allowed by g2.

```lean
open StatisticalRL StatisticalRL.Ch7Rest.TDInference MeasureTheory ProbabilityTheory Matrix in
/-- Corrected, plug-in-covariance ellipsoid confidence region at the printed `χ²(S)` quantile
(`chapters/inference.tex:207–213`, item (ii) of `eq:convex.Cdelta` :187–196; plug-in `Λ̂_T`
`eq:defn-hat-Lambda` :180–182). See `docs/SOURCE-ISSUES.md#C47` (items (3), (4)) and `#C43`.

Differs from the printed text: (1) the threshold is the `χ²(S)` `(1 − α)`-quantile `R` itself, not the
printed `R²` (C47(3)); `d = S = |State|`. (2) Asymptotic coverage only, pointwise in `q` and `R`; there is
no rate, because the plug-in consistency `Eq_defn_hat_Lambda_corrected` has no rate. (3) Added
non-degeneracy hypothesis `Γ_true ≻ 0`. The limit covariance of `Λ̂_T` is
`Λ = A⁻¹ diag(Γ_true) A⁻ᵀ` (C43), not the printed `Λ⋆`. (4) Junk value: when `Ā_T` is singular the
printed `Λ̂_T` is undefined (C47(4)). Lean's `Matrix.inv` gives `Λ̂_T = 0` and `Λ̂_T⁻¹ = 0`, and that event
has vanishing probability. Not covered: the plug-in `ℓ∞` rectangle (C47(2)) and data-selected sets
(C47(1)). Kept: i.i.d. sampling, full-support `μ`, `0 < η₀ < 1/4` (:133), every `V₀`.
`χ²(S)` is Mathlib's `gammaMeasure (S/2) (1/2)`.

Statement: (1) for every `q`, `P(T (V^π − V̄_T)ᵀ Λ̂_T⁻¹ (V^π − V̄_T) ≤ q) → F_{χ²(S)}(q)`; (2) for every
`α ∈ (0,1)` and every `R` with `F_{χ²(S)}(R) = 1 − α`, `P(T (V^π − V̄_T)ᵀ Λ̂_T⁻¹ (V^π − V̄_T) ≤ R) → 1 − α`. -/
def Eq_convex_Cdelta_ellipsoid_corrected_plugin : Prop :=
  ∀ (State Action : Type) [Fintype State] [DecidableEq State] [Nonempty State]
    [Fintype Action] [Nonempty Action]
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (μ : FiniteDistribution State) (η₀ : ℝ) (V₀ : State → ℝ),
    (∀ s, 0 < μ.prob s) → 0 < η₀ → η₀ < 1 / 4 → (∀ s, 0 < trueGamma M π μ s) →
    (∀ q : ℝ,
      Filter.Tendsto (fun T : ℕ ↦ ∑ ω : Fin T → Tuple State Action, pathWeight M π μ ω *
          {ω' : Fin T → Tuple State Action | (T : ℝ) * ∑ s, ∑ s',
            (M.valueFixedPoint π s - prAverage M η₀ V₀ ω' s) *
              (M.valueFixedPoint π s' - prAverage M η₀ V₀ ω' s') *
                (lambdaHat M η₀ V₀ ω')⁻¹ s s' ≤ q}.indicator 1 ω) Filter.atTop
        (nhds (cdf (gammaMeasure ((Fintype.card State : ℝ) / 2) (1 / 2)) q))) ∧
    (∀ α : ℝ, 0 < α → α < 1 → ∀ R : ℝ,
      cdf (gammaMeasure ((Fintype.card State : ℝ) / 2) (1 / 2)) R = 1 - α →
      Filter.Tendsto (fun T : ℕ ↦ ∑ ω : Fin T → Tuple State Action, pathWeight M π μ ω *
          {ω' : Fin T → Tuple State Action | (T : ℝ) * ∑ s, ∑ s',
            (M.valueFixedPoint π s - prAverage M η₀ V₀ ω' s) *
              (M.valueFixedPoint π s' - prAverage M η₀ V₀ ω' s') *
                (lambdaHat M η₀ V₀ ω')⁻¹ s s' ≤ R}.indicator 1 ω) Filter.atTop
        (nhds (1 - α)))
```

Proof sketch for Ch7Proofs.lean:

```lean
theorem Eq_convex_Cdelta_ellipsoid_corrected_plugin_holds :
    Eq_convex_Cdelta_ellipsoid_corrected_plugin := by
  intro State Action _ _ _ _ _ M π μ η₀ V₀ hμ h0 h1 hΓ
  have h1' : η₀ ≤ 1 := by linarith
  exact ⟨fun q ↦ tendsto_coverage_ellipsoid_plugin M π μ h0 h1' V₀ hμ hΓ q,
    fun α hα0 hα1 R hR ↦ tendsto_coverage_ellipsoid_plugin_chiSquared M π μ h0 h1' V₀ hμ hΓ hα0 hα1 hR⟩
```

`chiSquared k` unfolds by definition to `gammaMeasure (k/2) (1/2)`. If `exact` does not unify them, insert `show`/`unfold StatisticalRL.Probability.chiSquared`. The instance order in the binder must match the existing Ch7 entries.

## Proposed wording
COVERAGE (eq:convex.Cdelta ellipsoid row): "Corrected, plug-in Λ̂_T: asymptotic χ²(S) coverage (threshold R, not R²; no rate; Γ_true ≻ 0) — `Eq_convex_Cdelta_ellipsoid_corrected_plugin`, TDInferencePluginRegion711.lean. The oracle-Λ version with rate T^{-1/3}log(2T) is `..._oracle_chiSquared`. The plug-in ℓ∞ rectangle (C47(2)) remains open."

SOURCE-ISSUES C47(3) addendum: "**Lean evidence for the corrected ellipsoid with the printed plug-in Λ̂_T (2026-11-10, `Formalization/Ch7Rest/TDInferencePluginRegion711.lean`).** For full-support μ, 0 < η₀ ≤ 1, every V₀ and Γ_true ≻ 0: P(T(V^π − V̄_T)ᵀΛ̂_T⁻¹(V^π − V̄_T) ≤ R) → 1 − α for every χ²(S) (1 − α)-quantile R (`tendsto_coverage_ellipsoid_plugin_chiSquared`; for general q, → F_{χ²(S)}(q)). This is asymptotic only, with no rate. The singular-Ā_T junk value (C47(4)) lies in a vanishing-probability event. Independently critic-reviewed ([review](CRITIC-pluginregion)). Not author-approved. The plug-in ℓ∞ rectangle with a random level (C47(2)) is still open."
