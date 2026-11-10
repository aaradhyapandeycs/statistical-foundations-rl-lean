# Critic report: plug-in rate stages 3-5 (interval, ellipsoid, rectangle) (2026-11-10)

Public copy, scrubbed (local paths, probe files and agent identifiers removed). Independent review of `Formalization/Ch7Rest/TDInferencePluginIntervalRate711.lean`, `TDInferencePluginEllipsoidRate711.lean` and `TDInferencePluginRectRate711.lean` (finite-T rate T^(-1/3) for the plug-in rule `eq:convex.Cdelta`), with drafted strengthened statement entries.

Integration note: verdict ACCEPT for all three modules; PASS-DISCLOSED for the three entries. The recommendation was applied: `Eq_convex_Cdelta_corrected_plugin`, `Eq_convex_Cdelta_ellipsoid_corrected_plugin` and `Eq_convex_Cdelta_rectangle_corrected_plugin` were strengthened in place (same names) to the drafted rate forms, with wrappers in `Statements/Ch7Proofs.lean` from `plugin_coverage_rate`, `exists_coverage_ellipsoid_plugin_rate` and `exists_coverage_rect_plugin_rate`; the three modules are imported from `Ch7Proofs.lean` and `Formalization.lean`; the stale "with a rate remains open" docstring text and the COVERAGE and SOURCE-ISSUES C47 text were updated, with a new C47 paragraph. The optional rename of the Bonferroni export and the rpow-helper tidy-up were not applied (cosmetic). The stage-2 concentration bound has no separate statement entry (library export only). Not author-approved.


Built none of this. Read: AGENTS.md, five-bin/BRIEF.md, DESIGN-plugin-rate.md, CRITIC-pluginrate12.md,
source `source/upstream/tex/chapters/inference.tex:156–213` (estimators :165–177, `eq:defn-hat-Lambda`
:180–182, rule `eq:convex.Cdelta` :187–196, rectangles :198–205, ellipsoids :207–213), SOURCE-ISSUES C43/C47,
existing entries `Statements/Ch7.lean` (:936–988, :1180–1272) and wrappers `Ch7Proofs.lean:477–586`.

Files (sha256):
- `Formalization/Ch7Rest/TDInferencePluginIntervalRate711.lean` dc29e9fd…
- `Formalization/Ch7Rest/TDInferencePluginEllipsoidRate711.lean` 009cf568…
- `Formalization/Ch7Rest/TDInferencePluginRectRate711.lean` afbd4a1d…

## Commands and evidence
- `bash scripts/lean-local.sh <file>` on each (guarded by the 2-Lean loop): all EXIT 0, no `error:`/`warning:`.
  Interval prints one stderr line `Error in Linarith.normalizeDenominatorsLHS: Expr.rewrite may not produce
  subgoals.` — a caught linarith-preprocessing trace, non-fatal (exit 0); cosmetic. Logs are local scratch files.
- No `sorry`/`admit`/`axiom`/`set_option`/`native_decide` in the three files.
- a local scratch axiom file: `#print axioms` on all 13 exports/helpers
  (`exists_abs_pathProb_le_mul_sqrt_quadForm_lambdaHat_sub_le`, `exists_abs_coverage_oneSided_plugin_sub_le`,
  `exists_abs_coverage_twoSided_plugin_sub_le`, `exists_coverage_rect_plugin_ge_sub`, `plugin_coverage_rate`,
  `map_smul_mulVec_real_quadForm_le`, `abs_map_mulVec_real_quadForm_div_sub_le`,
  `exists_abs_cdf_chiSquared_div_sub_le`, `exists_coverage_ellipsoid_plugin_rate`,
  `exists_coverage_ellipsoid_plugin_chiSquared_rate`, `abs_supBoxProb_sub_map_le`,
  `exists_coverage_rect_plugin_rate`, `exists_coverage_rect_plugin_rate_quantile`) → all
  `[propext, Classical.choice, Quot.sound]` (local scratch log). The three files import together without name clashes.
- Draft statement entries compiled: a local scratch draft (imports only
  `TDInference711Defs`, `Mathlib.Probability.Distributions.Gamma`, `Mathlib.Probability.CDF` — all already on the G2
  list for Ch7.lean) and a local scratch wrapper draft (wrappers): clean; wrapper axioms = the standard three.

## Stage 3 — Interval / two-sided / Bonferroni: ACCEPT
1. Quantifiers: `∃ K, 0 < K ∧ ∀ T ≥ 1, ∀ u ≠ 0, ∀ z` (two-sided/box: `z ≥ 0`); K built from K₀ (oracle half-space),
   C (stage 2), c = min Γ_true/(S(∑|A|)²+1) — none depends on T, u, z. Combined `plugin_coverage_rate` uses K₁+K₂+K₃.
2. ε = r = T^{-1/3} ∈ (0,1] (`hr0`, `hr1`); stage-2 bound called only with 0 < r ≤ 1; C/(r²T) = C·r via r³T = 1. ✓
3. Sandwich: off B = {∃ s s', r < |Λ̂−Λ|}, |q̂−q| ≤ (∑|u|)² r ≤ (r/c)·q = κq, then
   |√q̂ − √q| ≤ |q̂−q|/√q ≤ κ√q; thresholds z√q̂ lie between min/max of z(1∓κ)√q for either sign of z
   (`mul_mem_min_max`). Oracle half-space at both deterministic levels; |Φ(z(1±κ)) − Φ(z)| ≤ κ uniformly in z for
   κ ≤ 1/2 (checked: derived from `abs_stdCDF_div_sub_le_of_le`). Trivial regime κ > 1/2 ⇒ 1 ≤ (2/c)·r. ✓
4. Junk inverse: singular Ā_T ⇒ Λ̂ = 0, whose diagonal is r-far from diag Λ > 0 only for small r — but no claim
   needs this: the bound uses only "ω ∉ B ⇒ closeness", so any value of Λ̂ on B is charged. ✓
5. Two-sided from one-sided at ±u via the existing event identity; box via union bound with `Pi.single s 1`. Box is
   a lower bound only (as in the oracle/asymptotic versions).
6. Fidelity: fixed-shape (C47(1)) and C43 target disclosed; Γ_true ≻ 0 disclosed; η₀ ≤ 1 contains printed (0,1/4).
Minor (non-blocking): `exists_coverage_rect_plugin_ge_sub` is the *Bonferroni box*, easily confused with the ℓ∞
rectangle `exists_coverage_rect_plugin_rate`; suggest a rename (`…_bonferroni_plugin_ge_sub`) before integration.
Three near-duplicate rpow helpers across the files (`rpow_neg_third_pow_three_mul`, `rpow_neg_third_facts`,
`rpow_neg_third_pow_three_mul_self`) and generic lemmas (`mul_mem_min_max`, `entryMax_smul_le`) living in the
TDInference namespace — tidy-up only.

## Stage 4 — Ellipsoid: ACCEPT
1. `∃ K, 0 < K ∧ ∀ T ≥ 1, ∀ q : ℝ` — uniform in q (all real q, including q < 0); K = K₀ + C + K_g·C_e + 2C_e,
   independent of T, q; the χ² corollary takes the same K for every α, R. ✓
2. Uses stage-2 inverse bound `exists_pathProb_lambdaHat_inv_sub_gt_le` with t = T^{-1/3} ∈ (0,1]. ✓
3. Sandwich checked: off B, |Q̂(x) − Q(x)| ≤ κQ(x) (C_e from (∑|x|)² ≤ C_e Q(x)); then
   E ⊆ {Q ≤ q/(1−κ)} ∪ B and {Q ≤ q/(1+κ)} ⊆ E ∪ B, algebraically valid for every sign of q. ✓
4. Gaussian side by scaling: N(0,Λ){Q ≤ q/c} = law of (√c F)Z on {Q ≤ q} (`map_smul_mulVec_real_quadForm_le`,
   checked), then `abs_real_convex_gaussian_sub_le` with ellipticity v₀/2 for c ≥ 1/2 ⇒ ≤ K_g|c−1|; convexity of
   {xᵀΛ⁻¹x ≤ q} from the existing `convex_trueLambda_ellipsoid` (all q). No χ² density used. Trivial regime κ > 1/2. ✓
5. Junk: Λ̂_T⁻¹ = 0 outcomes are only charged through B. ✓ Threshold R (not R²) and √T once: C47(3) disclosed.

## Stage 5 — ℓ∞ rectangle: ACCEPT
1. `∀ α ∈ (0,1), ∃ K, 0 < K ∧ ∀ rhat (quantile for every T, ω), ∀ T ≥ 1` — K depends on α only through
   m = min(α, 1−α) (K = 2c + K₀ + C + 1/θ, θ = min(m/(2c), v/(2S²))), and NOT on T or the quantile choice;
   α-dependence disclosed in header and docstring. ✓
2. ε = T^{-1/3} ≤ 1 for the stage-2 call. On the good event with S²ε ≤ v/2, Λ̂ elliptic with v/2, so
   |N(0,Λ̂)(box_r) − N(0,Λ)(box_r)| ≤ (2·gaussCmpConst/v)ε ≤ ρ = cε uniformly in r. Levels r∓ with exact oracle
   mass 1 − α ∓ 2ρ (exist since 2ρ < m); quantile property gives rm ≤ r̂ ≤ rp (checked strictness: plug-in mass at
   rm ≤ 1−α−ρ < 1−α; at rp ≥ 1−α+ρ > 1−α). Oracle rectangle bound uniform in r. Trivial regime when 2cε ≥ m or
   S²ε > v/2 ⇒ ε/θ ≥ 1. ✓
3. `IsSupBoxQuantile` / `supBoxProb` / `gaussOfCov` expanded: gaussOfCov uses a chosen PSD factor (Λ̂ is always PSD,
   `posSemidef_lambdaHat`), so no junk branch; the entry's ∃Q-form is bridged by `gaussOfCov_eq_map` (compiled).
4. Corrected scaling (C47(2)) and C43 disclosed; uniformity as α → 0 or 1 is not claimed (correctly).

## Statement entries: recommendation
Strengthen the three existing entries **in place** (same names), not new `_rate` entries: each rate Prop implies
the current asymptotic Prop (|P_T − L| ≤ K·T^{-1/3} → 0; the Bonferroni "eventually ≥ … − η" follows; the rectangle
keeps its existence conjunct), and also upgrades pointwise-in-(u,z)/q to uniform. Keeping both would be redundant;
in-place keeps COVERAGE/site/named-result links stable. The asymptotic library exports remain untouched.
The exact drafts (compiled) were local scratch files. Shapes:
- `Eq_convex_Cdelta_corrected_plugin`: hyps as now (η₀ < 1/4 printed) ⇒ `∃ K > 0, ∀ T ≥ 1,` (one-sided ∀u≠0 ∀z) ∧
  (two-sided ∀u≠0 ∀z≥0) ∧ (box ∀z≥0, ≥ 1 − 2S(1−Φ(z)) − K·T^{-1/3}). Wrapper:
  `exact plugin_coverage_rate M π μ h0 (by linarith) V₀ hμ hΓ`.
- `Eq_convex_Cdelta_ellipsoid_corrected_plugin`: `∃ K > 0,` (∀T≥1 ∀q, |P − cdf(gammaMeasure (S/2) (1/2)) q| ≤ K T^{-1/3})
  ∧ (∀α∈(0,1) ∀R, cdf … R = 1−α → ∀T≥1, |P − (1−α)| ≤ K T^{-1/3}). Wrapper: obtain K from
  `exists_coverage_ellipsoid_plugin_rate`; second conjunct by `rw [← hR]` (chiSquared unfolds definitionally).
- `Eq_convex_Cdelta_rectangle_corrected_plugin`: `∀ α ∈ (0,1),` (∃ rhat quantile, as now) ∧ `∃ K > 0, ∀ rhat`
  quantile (∃Q-form) `→ ∀ T ≥ 1, |P − (1−α)| ≤ K T^{-1/3}`. K after α (disclosed). Wrapper bridges as the current one.
Ch7Proofs.lean must import the three new modules; Formalization.lean must import them too.

## Five-bin (all three drafts)
| binder | bin | citation |
|---|---|---|
| State, Action, Fintype, DecidableEq, Nonempty ×2 | TYPING | finite MDP :49–64 |
| M, π, μ, η₀, V₀ | SOURCE/STANDING | :49–64, :133 |
| ∀ s, 0 < μ s | STANDING | λ₀ > 0, :67 |
| 0 < η₀, η₀ < 1/4 | STANDING | :133 |
| ∀ s, 0 < Γ_true s | DISCLOSED | C47 plug-in paragraph, C43 |
| u ≠ 0, z (z ≥ 0) | DISCLOSED | fixed shape, C47(1) |
| α ∈ (0,1) | SOURCE | :189 |
| R with χ²(S) cdf = 1 − α; threshold R | SOURCE + DISCLOSED | :213; C47(3) |
| rhat per-outcome ℓ∞ quantile under Λ̂_T, half-width r̂/√T | SOURCE + DISCLOSED | :205; C47(2) |
| K after α (rectangle) | DISCLOSED | to state in C47 entry |
| target Λ = A⁻¹diag(Γ_true)A⁻ᵀ (implicit, via limits) | DISCLOSED | C43 |
EXCESS: 0. Junk: Matrix.inv junk only on bad events; `Real.sqrt` of q̂/T and `/ √T` harmless (T ≥ 1).
Verdict for all three drafts: PASS-DISCLOSED, conditional on the C47 text below being added (the docstrings must
point to a SOURCE-ISSUES paragraph that states the rate and the α-dependence).

## Proposed COVERAGE / C47 wording
C47 new paragraph: "**Plug-in Λ̂_T with a finite-T rate (2026-11-10; TDInferencePluginIntervalRate711.lean,
TDInferencePluginEllipsoidRate711.lean, TDInferencePluginRectRate711.lean; via TDInferencePluginRate711.lean,
P(∃ s s', ε < |Λ̂_T − Λ|) ≤ C/(ε²T) for 0 < ε ≤ 1).** For full-support μ, 0 < η₀ ≤ 1 (containing the printed
(0, 1/4)), every V₀ and Γ_true ≻ 0, with ε = T^(-1/3): one instance constant K (independent of T, u, z) bounds by
K·T^(-1/3) the coverage error of the plug-in one-sided and two-sided intervals for every u ≠ 0 and z, and the
Bonferroni box loses at most K·T^(-1/3); the corrected plug-in ellipsoid (threshold q, all real q; χ²(S) quantile R,
not R²) is within K·T^(-1/3) of F_χ²(S)(q), resp. 1 − α, with K independent of T, q, α, R; the corrected plug-in
ℓ∞ rectangle (half-width r̂_T/√T, any per-outcome (1−α)-quantile r̂_T under Λ̂_T) is within K_α·T^(-1/3) of 1 − α,
where K_α depends on α through min(α, 1−α) and on the instance, not on T or the quantile choice. The junk value on
the singular event lies inside the charged bad event. Instance constants, not printed coefficients. Not
author-approved." Replace "Still open: … plug-in Λ̂_T versions with a rate" and "a rate remains open" sentences
(SOURCE-ISSUES C47 plug-in, ellipsoid and rectangle paragraphs) by a pointer to this paragraph.
COVERAGE row `eq:convex.Cdelta`: headline → "…plug-in covariance with rate T^(-1/3) (instance constant; rectangle
constant depends on α)"; replace "Open: any finite-T rate with the plug-in Λ̂_T" by the remaining open items:
(a) arbitrary/data-selected C_α (C47(1), refuted in general; no positive result beyond fixed shapes);
(b) the printed rectangle scaling R̂/√T (refuted) and the formal identification R̂ = r̂_T/√T (Gaussian scaling,
not formalized); (c) ℓ∞-quantile identification of the oracle level r_α; (d) a finite-T definition of the printed
procedure on the singular event (C47(4); only charged/convention-independent); (e) printed coefficients / explicit
dependence of K on the instance; K_α uniform as α → 0 or 1; any rate better than T^(-1/3); (f) the printed Λ⋆
under action-dependent rewards (C43). Also update stale "with a rate they remain open" text at Ch7.lean :953,
:1060, :1095, :1131 and the ConfRegion711/Plugin*711 headers; record stage-2 entry `Eq_defn_hat_Lambda_corrected_rate`
(0 < ε ≤ 1 only) if not yet added.

## Verdicts
| file | verdict |
|---|---|
| TDInferencePluginIntervalRate711.lean | ACCEPT (optional rename of the Bonferroni export) |
| TDInferencePluginEllipsoidRate711.lean | ACCEPT |
| TDInferencePluginRectRate711.lean | ACCEPT |
