# Critic report: oracle confidence regions (eq:convex.Cdelta, C47(2)/(3)) — 2026-11-10

Public copy, scrubbed (local paths, probe files and agent identifiers removed). Independent review and five-bin audit of the oracle-covariance confidence regions (`Formalization/Ch7Rest/TDInferenceConfRegion711.lean`) and the statement entries `Eq_convex_Cdelta_fixedShape_corrected_oracle`, `Eq_convex_Cdelta_ellipsoid_corrected_oracle`, `Eq_convex_Cdelta_rectangle_corrected_oracle`. Probes are local scratch files (`<local probe>`).

Integration note: verdict ACCEPT WITH FIXES; F1–F4 (docstrings) applied; F5 (ledger wording) applied in COVERAGE and SOURCE-ISSUES C47.

Independent critic; did not build. Read-only on Formalization/, docs/, Formalization.lean.

## Verdict: ACCEPT-WITH-FIXES (docstring and ledger wording only; no Lean statement change needed)

## Evidence (commands actually run)
- `bash scripts/lean-local.sh Formalization/Ch7Rest/TDInferenceConfRegion711.lean`: clean, no output.
- `bash scripts/lean-local.sh Formalization/Statements/Ch7.lean`: clean.
- `bash scripts/lean-local.sh Formalization/Statements/Ch7Proofs.lean`: clean.
- <local probe>: `exists_confRegion_oracle_bounds` and the three
  `_holds` depend only on [propext, Classical.choice, Quot.sound]; plus `example : trueLambda M π μ =
  (tdA)⁻¹ * diagonal (trueGamma) * (tdA)⁻¹ᵀ := rfl` succeeds (Λ written out in the entry is literally trueLambda).
- <local probe> (copy of builder probe): non-vacuity on instance G
  (S = 2, η₀ = 1/8 < 1/4, Γ_true = (25/128, 1/128) ≻ 0, full-support μ) compiles; same three axioms.
- olean mtimes newer than sources for the library file, Ch7, Ch7Proofs. Max 2 Lean processes at a time.
  No lake, no git.

## 1. Library mathematics (TDInferenceConfRegion711.lean)
- Event identity (:84–108): `scaledError = √T • (V̄_T − V^π)` (TDInference711Defs.lean:92). `V^π ∈ V̄ +ᵥ T^{-1/2}•K
  ⟺ √T(V^π − V̄) ∈ K ⟺ scaledError ∈ −K`. The proof uses `mem_vadd_set_iff_neg_vadd_mem` and
  `mem_smul_set_iff_inv_smul_mem₀` with √T ≠ 0 from T ≥ 1. Signs correct.
- Symmetry (:46–79): `gaussCov = map (z ↦ A⁻¹(√Γ⊙z)) (std Gaussian)`; linearity of gaussMap and the coordinatewise
  `gaussianReal_map_neg` give `map neg gaussCov = gaussCov`; `MeasurableEquiv.map_apply` holds for every set,
  so `N(−K) = N(K)` for arbitrary K (outer measure). Correct.
- Rectangle (:143–177): `V̄ − r/t ≤ V ≤ V̄ + r/t ⟺ |t(V̄ − V)| ≤ r` for t > 0. Correct; box convex (:133).
- Ellipsoid (:181–305): `trueLambda_left_inv` uses `tdA_isUnit` (full support) and Γ_true ≻ 0, then
  `Matrix.inv_eq_left_inv`: Λ⁻¹ = AᵀD⁻¹A is the genuine inverse, not the junk 0 (`trueLambda_inv_mul`).
  Quadratic form equals Σ_r (Ax)_r²/Γ_r, so the sublevel set is convex (`convex_sumSq_le`, correct convexity
  identity a(1−a)(·)² ≥ 0). `T·xᵀLx = (√Tx)ᵀL(√Tx)` via `√T·√T = T`. Correct for every q (q < 0 included).
- Quantifier order (:325): `∃ K₀ > 0, ∀ T ≥ 1, (∀ K convex …) ∧ (∀ q …) ∧ (∀ r …)`; K₀ after instance data
  (M, π, μ, η₀, V₀), before T, K, q, r. One constant from `abs_lawProb_convex_sub_gaussCov_le_third_log`.
- No hidden hypotheses beyond the base theorem's (full-support μ, 0 < η₀ ≤ 1, Γ_true ≻ 0).

## 2. Five-bin audits

Source reconstructed from `chapters/inference.tex:187–213` (pinned source under source/upstream/tex):
the rule says that any convex 𝒞_α with mass ≥ 1−α under N(V̄_T, Λ̂_T/T) is an approximate confidence region by
Theorem 7.11 (:189–196). Item (i) (:198–205) is the rectangle ∏[V̄(s) ± R̂/√T] with R̂ the ℓ∞ quantile under Λ̂_T/T.
Item (ii) (:207–213) is the ellipsoid T(V−V̄)ᵀΛ̂_T⁻¹(V−V̄) ≤ R², R the χ²(d) (1−α) quantile. Implicit setting:
i.i.d. sampling (:49–64), η_t = η₀t^{-2/3}, 0 < η₀ < 1/4 (:133), Γ ≻ 0 (definedness of Thm 7.11's ‖Γ⁻¹‖).
Printed approximation: no explicit rate in the rule; it inherits Theorem 7.11's T^{-1/3}.

Common binders (all three entries, Ch7.lean:803/831/863):

| binder | Lean | bin | citation |
|---|---|---|---|
| State, Action, Fintype, DecidableEq, Nonempty | instances | TYPING | finite MDP |
| M, π, μ | DiscountedMDP, StationaryPolicy, FiniteDistribution | SOURCE | :49–64 |
| η₀, V₀ (∀) | ℝ, State → ℝ | SOURCE (schedule family, every init) | :133, :72 |
| ∀ s, 0 < μ.prob s | full support | STANDING | :51–67 |
| 0 < η₀, η₀ < 1/4 | | STANDING | :133 |
| ∀ s, 0 < trueGamma s | Γ_true ≻ 0 | DISCLOSED (C43/C47; Thm 7.11 definedness) | see F1 |
| ∃ K₀ > 0 before T | instance constant | DISCLOSED (rate form) | docstrings (3) |
| ∀ T ≥ 1 | | SOURCE | |
| gaussCov (tdA) (trueGamma) | N(0, A⁻¹Γ_trueA⁻ᵀ) | DISCLOSED (oracle Λ, C43) | Defs:137–145 |
| rate K₀T^{-1/3}log(2T) | | DISCLOSED (extra log) | docstrings |

Entry-specific:
- fixedShape (:803): `∀ K, Convex ℝ K` fixed before data, region V̄ +ᵥ T^{-1/2}•K: DISCLOSED (C47 proposed
  correction, (1)). With oracle Λ, N(V̄, Λ/T)(V̄ + T^{-1/2}K) = N(0,Λ)(K), so this is exactly the corrected rule
  (Λ^{1/2}K of the C47 proposal is another fixed convex set). Bins: TYPING 5, SOURCE 4, STANDING 3, DISCLOSED 5,
  EXCESS 0. **PASS-DISCLOSED.**
- ellipsoid (:831): `∀ q ≥ 0` (export: all q; wrapper restricts, fine), threshold q not R²: DISCLOSED C47(3);
  Λ⁻¹ written out as `((tdA)⁻¹ * diagonal Γ_true * (tdA)⁻¹ᵀ)⁻¹`, genuine inverse under hypotheses (proved). χ²
  identification and 1−α quantile explicitly not claimed. Bins: TYPING 5, SOURCE 4, STANDING 3, DISCLOSED 5,
  EXCESS 0. **PASS-DISCLOSED** (F1, F3 wording).
- rectangle (:863): `∀ r ≥ 0`, half-width r/√T with r an ℓ∞ level under Λ (not Λ/T): DISCLOSED C47(2); equivalent
  to the C47 correction "half-width R̂, not R̂/√T" since the Λ/T quantile is r/√T. 1−α level not claimed. Bins:
  same counts. **PASS-DISCLOSED** (F1).

All three: self-contained (Λ inline in the ellipsoid; the others reference Λ only through the shared project
definition gaussCov, as in earlier accepted entries); `_holds` wrappers (Ch7Proofs.lean:442–469) only project
the export and weaken η₀ < 1/4 to η₀ ≤ 1 and q, r ≥ 0. None claims the printed plug-in procedure, data-selected
sets or 1−α calibration.

## 3. Suffix
`_corrected` is right: the printed shapes are changed (C47(2) rectangle scaling, C47(3) threshold) and data-selected
sets are replaced by fixed shapes. The `_oracle` qualifier discloses the covariance restriction, as in the existing
`Eq_convex_Cdelta_corrected_oracle`. `_restricted` would wrongly suggest the printed rectangle and ellipsoid formulas
hold on a subclass.

## Findings
- F1 (Low, docstring): Ch7.lean ~:816–829 (ellipsoid) and ~:847–862 (rectangle) do not say
  "`Γ_true ≻ 0` is assumed" explicitly (fixedShape :801 does; ellipsoid only says "under the hypotheses Λ is
  invertible"). Add that sentence to both.
- F2 (Low, stale cross-reference): Ch7.lean:696–697 (`Eq_convex_Cdelta_corrected_oracle`, point (3)): "the printed
  ℓ∞-quantile rectangle (C47(2)) and the ellipsoid (C47(3)) are not addressed". Proposed: "the printed ℓ∞-quantile
  rectangle (C47(2)) and ellipsoid (C47(3)) are not covered here; their corrected oracle forms are
  `Eq_convex_Cdelta_rectangle_corrected_oracle` and `Eq_convex_Cdelta_ellipsoid_corrected_oracle` (rate
  T^{-1/3}log(2T))". Optionally add the same pointer to Ch7.lean:753 (plug-in "Not covered" list, still true for
  the plug-in).
- F3 (Info, wording): the ellipsoid docstring says R² "squares the threshold twice"; C47(3) says the χ² quantile
  R is squared once more. Suggest "compares the χ² statistic with R², squaring a quantile that is already on the
  χ² scale".
- F4 (Info): the ellipsoid and rectangle docstrings say "printed T^{-1/3}"; the rule prints no rate. Say "Theorem
  7.11's printed T^{-1/3}" as in the fixedShape docstring.
- F5 (Ledger): COVERAGE row eq:convex.Cdelta still lists "the ellipsoid (C47(3))" as open, and C47's plug-in
  addendum lists "(3)" as open. Both need updating (below), plus link TDInferenceConfRegion711.lean.

## Proposed ledger wording
COVERAGE, row eq:convex.Cdelta (insert after the plug-in sentence; drop "the ellipsoid (C47(3))" from Open and
add the file link):
> Corrected fixed shapes, corrected rectangle and corrected ellipsoid with oracle covariance
> (`Eq_convex_Cdelta_fixedShape_corrected_oracle`, `_ellipsoid_corrected_oracle`, `_rectangle_corrected_oracle`;
> export `exists_confRegion_oracle_bounds`, TDInferenceConfRegion711.lean): one instance constant K₀ such that for
> all T ≥ 1, (a) every convex K fixed before the data: |P(V^π ∈ V̄_T + T^(-1/2)K) − N(0,Λ)(K)| ≤ K₀T^(-1/3)log(2T);
> (b) the ellipsoid with threshold q (not R², C47(3)): |P(T(V^π−V̄_T)ᵀΛ⁻¹(V^π−V̄_T) ≤ q) − N(0,Λ){xᵀΛ⁻¹x ≤ q}| ≤ same;
> (c) the rectangle with half-width r/√T, r an ℓ∞ level under Λ (√T once, C47(2)): |P(∀s, |V̄_T(s)−V^π(s)| ≤ r/√T) −
> N(0,Λ){‖x‖∞ ≤ r}| ≤ same. Λ = A⁻¹Γ_trueA⁻ᵀ is the oracle (unknown in practice); the rate carries an extra
> log(2T) relative to Theorem 7.11's printed T^(-1/3). Corollaries of the all-convex partial result
> `abs_lawProb_convex_sub_gaussCov_le_third_log`. Not proved: the χ²(S) law of xᵀΛ⁻¹x, existence of exact 1−α
> levels q, r, the plug-in Λ̂_T versions with a rate, and the printed rectangle and ellipsoid formulas.
> [Review](critic-confregion.md). Not author-approved.

Open list: "a finite-T rate for the plug-in rule; the plug-in rectangle and ellipsoid; exact 1−α calibration
(χ² identification, ℓ∞ quantile); the rate without log(2T); the C47(1) refutation with Λ̂_T; C47(4) finite-T."

C47 addendum:
> **Corrected rectangle and ellipsoid, oracle covariance (2026-11-10, `TDInferenceConfRegion711.lean`, entries
> `Eq_convex_Cdelta_{fixedShape,ellipsoid,rectangle}_corrected_oracle`).** The proposed corrections of (2) (√T applied
> once: half-width r/√T with r an ℓ∞ level under Λ) and (3) (threshold q, not R²) and the fixed-shape rule
> V̄_T + T^(-1/2)K are machine-checked with the oracle Λ = A⁻¹Γ_trueA⁻ᵀ (Γ_true ≻ 0): coverage within
> K₀T^(-1/3)log(2T) of the Gaussian mass, one instance constant. Still open: the plug-in Λ̂_T versions with a rate,
> exact 1−α calibration (χ²(S) identification, ℓ∞ quantile), and the printed rate without log(2T).
> Independently critic-reviewed. Not author-approved.
