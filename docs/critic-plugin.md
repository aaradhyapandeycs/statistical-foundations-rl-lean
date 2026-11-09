# CRITIC: item C (plug-in Λ̂_T, `eq:defn-hat-Lambda`) and E3 (C47(4))

Public copy of the independent critic report; local paths removed. Probe and scratch files named below (`reviewer-probes/`, `builder-probes/`) were kept in private folders and are not published.

Post-review note (added to this public copy, 2026-11-09): all round-1 fixes were verified in round 2 ([round-2 review](critic-plugin-r2.md)); the scope statements below that say consistency for the corrected target is open, or that the state-only reading is neither proved nor refuted, are superseded by `eq_defn_hat_Lambda_corrected` and `eq_defn_hat_Lambda_restricted`. The review text below is otherwise unchanged.

Critic, independent of the builder. Date 2026-11-09. Source `chapters/inference.tex`, SHA-256
`82707713adb6c9296d9ee41faa84b2d0a12eaf1b34864a6d294de02132e648f2` (matches `source/provenance.json`).
Files reviewed: `Formalization/Ch7Rest/TDInferencePlugin711.lean`, `TDInferencePluginSingular711.lean`,
`TDInferencePluginRefute711.lean`, `TDInferencePluginConsistency711.lean`, and the builder notes in `builder-probes/`.

## Verdict: ACCEPT WITH FIXES

The mathematics is correct and the definitions match the printed objects. There is one **blocking integration defect** (F0,
a name collision that breaks `import Formalization`) and one **statement-fidelity fix** (F1, the η₀ range of the refuted
Prop). Neither changes any proof idea. Both were checked with a compile (see Evidence).

## Evidence (commands actually run)

- `bash scripts/lean-local.sh reviewer-probes/ProbePlugin.lean`. It imports Refute711 and
  Consistency711. Result: exit 0. 19 `#print axioms` over the main exports (refutation, C2 iff, singular bounds ≥/≤/>0,
  junk lemma, Z witnesses, C3(a), C3(b), weights, `gammaHat_apply`, `aBar_apply`) all give `[propext, Classical.choice,
  Quot.sound]`. The probe also has two extra checks, and both compile:
  - The refuted Prop with **`η₀ < 1/4`** in place of `η₀ ≤ 1` is also refuted by the same proof (instance Z, η₀ = 1/8).
  - A hand computation: `aBar zMDP ω 0 1 = −1/4` for the path ((0,1,1),(1,0,0)). Checked by hand:
    T⁻¹(−γ·m₀₁) = ½·(−½·1).
- `bash scripts/lean-local.sh reviewer-probes/ProbeFull.lean`, which is `import Formalization` plus
  the 4 modules. **Fails**:
  `import Formalization.Ch7Rest.TDInferencePlugin711 failed, environment already contains
  'StatisticalRL.Ch7Rest.TDInference.sampleA' from Formalization.Ch7Rest.TDInferenceOperator711`.
- grep over the 4 files finds no `sorry`, `admit` or `axiom`. The `.olean`s are newer than the sources.
- Same-namespace name collisions with existing library declarations (grep of every def/theorem name in the 4 files
  against `Formalization/`): `sampleA`, `sampleA_apply`, `sum_tupleProb_mul_sampleA`, all in
  `TDInferenceOperator711.lean`, which `Formalization.lean:709` imports. No other collisions were found.
- No lake or LSP use. At most one Lean process ran at a time, started only when `pgrep -x lean | wc -l` < 2.

## Required fixes

**F0 (blocking, integration).** Rename the plug-in matrix objects so they do not clash with `TDInferenceOperator711`.
Proposed names: `sampleA → sampleAMat`, `sampleA_apply → sampleAMat_apply`,
`sum_tupleProb_mul_sampleA → sum_tupleProb_mul_sampleAMat`. Or put the plug-in API in a sub-namespace `Plugin`.
Also add the bridge `(sampleAMat M x).mulVec v = sampleA M x v`, which links to the Operator711 operator form; C3(c)
needs it anyway. After the rename, rerun `ProbeFull.lean` (import Formalization + the 4 modules) before integrating.
The builder's own AxiomProbe did not import `Formalization`, which is why this was missed.

**F1 (statement fidelity).** `Eq_defn_hat_Lambda_printed_consistent` assumes `0 < η₀ → η₀ ≤ 1`. The section's printed
range (Theorem 7.11, `inference.tex:134`) is `0 < η₀ < 1/4`. In a refuted ∀-Prop a wider hypothesis range makes the
claim **stronger**, so refuting it is weaker. The docstring line "Every hypothesis only weakens the claim" is therefore
false for this hypothesis. Change it to `η₀ < 1/4`. The proof is unchanged, since it uses η₀ = 1/8, and the critic
probe compiles that variant.

**F2 (citations).** The line numbers are off by 2 in `TDInferencePlugin711.lean`:
- `A_t`/`sampleA` and `Ā_T`/`aBar` are at `:166` (cited as `:168`).
- `Γ̂_T`/`gammaHat` and `b_t`/`sampleB` are at `:168` (cited as `:170`).
- The module header's range ":166–171" should be `:165–169` (align* block) or `:166–168`.
- The weights `:175–177`, the display `:180–182`, "final estimator of Λ⋆" `:184` and "online" `:185` are correct.

The existing C47 entry in `docs/SOURCE-ISSUES.md` cites `eq:defn-hat-Lambda` as `:179–181` and the estimators as
`:160–181`. The correct ranges are `:180–182` and `:165–182`. Fix these in the C47(4) addendum edit.

**F3 (disclosure, docstrings).**
- (a) Add the C43 reading caveat to the docstrings of `Eq_defn_hat_Lambda_printed_consistent` and
  `not_eq_defn_hat_Lambda_printed_consistent`. The refutation depends on action-dependent rewards with r(s) = r_π(s).
  With state-only rewards, or deterministic π, `printedGamma = trueGamma`
  (`trueGamma_eq_printedGamma_of_reward_const_on_support`), so `printedLambda = trueLambda` and that reading is
  neither proved nor refuted here.
- (b) Add the required junk-value sentence (plan check §5) to the Prop docstring.

## Recommendations (non-blocking)

- **R1 (junk independence of the refutation).** The Lean proof gets `pathProb = 1` by counting singular paths as "far"
  with the junk value 0. Mathematically this does not depend on the junk value. On the nonsingular event,
  Λ̂_T = Ā⁻¹·0·Ā⁻ᵀ = 0 is the genuine printed value, and `P(singular) ≤ 2·2^{-T} → 0`. A short lemma would make this
  machine-checked: `P({det Ā ≠ 0} ∩ far) ≥ 1 − ∑_s(1−μ(s))^T`, using `pathProb_aBar_singular_le` (about 20–40 lines).
  Either add it or state the point in the docstring.
- **R2 (V₀ scope).** Only the every-V₀ reading is refuted, through V₀ = V^π. This is honestly disclosed. The some-V₀
  reading can be refuted in the same instance Z without the corrected-consistency theorem:
  - The residual at V̄ is `e(s_t) − γe(s'_t)` with `e = V̄_T − V^π`, so `Γ̂ ≤ (1+γ)²‖e‖∞²`.
  - `TDInferenceAnyInit711` already gives `E‖V_t − V^π‖² → 0` in Z.
  - On the nonsingular event, `|Λ̂(0,0)| ≤ ‖Ā⁻¹‖² · max Γ̂`.
  - `‖Ā⁻¹‖_∞ ≤ T/((1−γ) min_s n_s)` follows from the diagonal-dominance margin already computed in
    `aBar_det_ne_zero_of_sampled`.
  - With `n_s/T ≥ 1/4` w.h.p. (C3(a)-style Chebyshev), `P(|Λ̂(0,0) − 5/64| > 1/64) → 1` from any V₀.

  Optional, about 200–300 lines. It would let C43 say "every reading of V₀", matching its Theorem 7.11 wording.
- **R3 (link C3(b) to Λ̂).** `oracleGammaHat` is defined separately, and no lemma states that it is the diagonal of the
  printed Γ̂ formula evaluated at V^π. Define `gammaHatAt M V ω` (residuals at an arbitrary V). Then prove
  `gammaHat M η₀ V₀ ω = gammaHatAt M (prAverage M η₀ V₀ ω) ω` and
  `gammaHatAt M (M.valueFixedPoint π) ω s s = oracleGammaHat M π ω s`.
  Without these, C3(b) is about a different object from Λ̂. This is the entry point of C3(c).

## Point-by-point review

**(1) Definitions.** Each was reconstructed from `:161–184`.
- `sampleA = vecMulVec e_s (e_s − γe_{s'})` = e_s(e_s − γe_{s'})ᵀ. ✓
- `sampleB = r(s,a)e_s` with `r_t = r(s_t,a_t)` per `:62`. ✓
- `aBar = T⁻¹∑A_t` (0 at T = 0, irrelevant). ✓
- `pluginWeight T t = (t+1)/∑_{u<T}(u+1)` is `w_{t+1,T}`. The 0-based shift is consistent with `tdIter`, where
  `ω ⟨t⟩` produces `V_{t+1}`, so sample `ω t` is the printed (t+1)-st tuple. ✓
- `pluginWeight_eq` is the printed closed form `2t/(T(T+1))` at t+1. ✓
- `gammaHat` evaluates every residual at the final `V̄_T = prAverage` = T⁻¹∑_{t=1}^T V_t, as printed (`:168`), not at
  the running averages. ✓
- `gammaHat_apply` proves that Γ̂ is diagonal with the expected entry. ✓
- `lambdaHat = Ā⁻¹ Γ̂ (Ā⁻¹)ᵀ`. ✓
- The junk `Matrix.inv = 0` is disclosed in the module doc and the def docstring, with
  `lambdaHat_eq_zero_of_det_eq_zero`. ✓
- `printedLambda` uses `tdA = diag(μ)(I − γP_π)` and `printedGamma` (r_π reading). `trueLambda` uses `trueGamma`. ✓

**(2) C2 / E3.**
- `aBar_det_ne_zero_iff`:
  - (→) An unsampled s gives a zero row (`aBar_apply`: n_s = m_{sj} = 0).
  - (←) Gershgorin: diag − ∑_{j≠k}|Ā_kj| = T⁻¹((n_k − γm_kk) − γ(n_k − m_kk)) = T⁻¹(1−γ)n_k > 0. This uses
    `∑_j m_kj = n_k` and does not need γ > 0.
  - T = 0 is consistent in both directions. Ā = 0, so det = 0 iff State is nonempty iff some state is unsampled.
  - ✓
- `pathProb_unsampled = (1−μ(s))^T`, from the product structure through `Fintype.piFinset`. ✓
- The lower bound `(1−μ(s))^T ≤ P(singular)` holds for every s with no hypothesis. ✓
- The upper bound `≤ ∑_s(1−μ(s))^T` is a union bound. ✓
- The positivity lemma needs `s ≠ s'` with `μ(s') > 0`. This is exactly "S ≥ 2 with some other state reachable", and
  it holds under the printed λ₀ > 0 when S ≥ 2. ✓
- Concrete witness `zAbar_singular_ge`: `2^{-T}`, matching the C47(4) text. ✓

**(3) Refutation.**
- Instance Z values were recomputed by hand:
  - γ = 1/2, s' = a, uniform μ and π, V^π = (1, 1/2).
  - P_π rows are uniform, so A = [[3/8, −1/8], [−1/8, 3/8]], det = 1/8, and A⁻¹ = [[3, 1], [1, 3]]. ✓
  - printed Γ_ss = μ(s)·γ²((V₀+V₁)/2 − V(s'))² averaged = ½·(1/4)(1/16) = 1/128. ✓
  - Λ⋆(0,0) = (3² + 1²)/128 = 5/64. ✓
  - Γ_true = 0, since r + γV^π(s') = V^π(s) on every sample. ✓
- From V₀ = V^π every positive-weight path has V_t ≡ V^π, every residual 0, Γ̂ = 0 and Λ̂ = 0, for every η₀ and T ≥ 1. ✓
- The Prop encodes entrywise convergence in probability, with the quantifier order ∀ instance, ∀ η₀, ∀ V₀, ∀ ε, then
  the limit in T. This is the standard meaning of "estimator of Λ⋆" read as consistency, and in finite dimension it is
  equivalent to convergence in any norm.
- Added hypotheses (full support, `printedGamma ≻ 0`) only weaken the claim. ✓ The η₀ range does not (F1).
- The scope "every-V₀ reading only" is honestly disclosed in the Refute module doc (R2 would remove the restriction).
- The source never states consistency in words. The Prop is an interpretation of `:184`, and the docstrings call it a
  reading. ✓

**(4) C3(a)/(b).**
- `E[A_t] = A` entrywise (`sum_tupleProb_mul_sampleA`, the off-diagonal mass μ(s)P_π(j|s)). ✓
- |A_t(s,j)| ≤ 1, so Var ≤ E[A_t²] ≤ 1 and E(Ā − A)² ≤ 1/T, through the existing martingale identity with an f that
  ignores the iterate. ✓
- Chebyshev gives 1/(ε²T), and the union bound gives S²/(ε²T). ✓
- `oracleGammaHat`'s summand mean is `Γ_true(s)` (`sum_tupleProb_mul_oracleTerm` via `trueGamma_eq`). Since
  ∑w = 1, E Γ̂^{or} = Γ_true, the C43-corrected target, not Γ_printed. ✓
- Summands lie in [0, B²] with Γ_true ∈ [0, B²], so (g − m)² ≤ B⁴.
- ∑w² ≤ max w · ∑w = 2/(T+1) ≤ 2/T, so E(…)² ≤ 2B⁴/T. ✓
- See R3 for the missing link to Λ̂.

**(5) Draft entries and G2.**
- `scripts/gates/g2_statement_imports.txt` says "May only shrink", so importing `TDInferencePlugin711` into
  `Statements/Ch7.lean` **would fail G2**. That module is also not a pure definitions module: it contains the
  refuted Prop and ~15 theorems.
- `Eq_plugin_weights`: the draft already inlines the bodies and needs no new import. It is acceptable. It states the
  printed identity `t/∑t = 2t/(T(T+1))` (`:175`) plus `∑w = 1`, which concludes more and is allowed. The proof in
  `Ch7Proofs.lean` unfolds `pluginWeight`. Making it an entry is the lead's call. It is a display identity, not a
  numbered result, so a COVERAGE prose note is equally adequate.
- `C47_4_aBar_singular`: **do not add it to `Statements/Ch7.lean`.** AGENTS.md reserves the index for source results
  recorded as proved, and this is SOURCE-ISSUES evidence. Cite the library theorem names in the C47(4) addendum. If
  the lead nonetheless wants a statement-style Prop, either inline `aBar` and `pathProb`, which are short, or move the
  pure defs into the already-allowed `TDInference711Defs.lean`. The latter does not grow the G2 list.
- No entry for `Eq_defn_hat_Lambda` itself. Any future consistency entry must be `Eq_defn_hat_Lambda_corrected` with
  target `trueLambda`, citing C43 and C47(4).

## Recommended text

**COVERAGE (`eq:defn-hat-Lambda`, `inference.tex:161–185`):**
> Definitions formalized: `aBar`, `gammaHat`, `lambdaHat` (`Formalization/Ch7Rest/TDInferencePlugin711.lean`), with the
> printed weights `w_{t,T} = 2t/(T(T+1))` and `∑w = 1` machine-checked (`pluginWeight_eq`, `sum_pluginWeight`). On the
> event that some state is unsampled, `Ā_T` is singular and the printed `Λ̂_T` is undefined (C47(4)); Lean's
> `Matrix.inv` returns 0 there. Consistency for the printed `Λ⋆` is false under the r(s) = r_π(s) reading
> (`not_eq_defn_hat_Lambda_printed_consistent`, every-V₀ reading, C43). Consistency for the corrected
> `Λ = A⁻¹Γ_trueA⁻ᵀ` is open. Proved inputs so far: `Ā_T → A` (`pathProb_exists_abs_aBar_sub_gt_le`, rate S²/(ε²T)) and
> oracle `Γ̂ → Γ_true` (`pathProb_abs_oracleGammaHat_sub_gt_le`). Online computability (`:185`) is not formalized.
> Status: partial / source issue. Not author-approved.

**SOURCE-ISSUES C47(4) addendum:**
> Machine-checked (2026-11-09, `Formalization/Ch7Rest/TDInferencePluginSingular711.lean`). `Ā_T` (`inference.tex:166`)
> is invertible iff every state is sampled (`aBar_det_ne_zero_iff`; the forward direction is a zero row, the converse
> is strict diagonal dominance with margin T⁻¹(1−γ)n_s). Under the i.i.d. law,
> `(1−μ(s))^T ≤ P(Ā_T singular) ≤ ∑_s(1−μ(s))^T` (`pathProb_aBar_singular_ge`, `pathProb_aBar_singular_le`), so the
> probability is positive for every T when S ≥ 2 (`pathProb_aBar_singular_pos`). In the two-state uniform instance it
> is ≥ 2^{−T} (`zAbar_singular_ge`). The printed `Λ̂_T` (`eq:defn-hat-Lambda`, `:180–182`) is undefined there. The
> probability tends to 0, so this does not by itself prevent consistency. Line references in this entry: estimators
> `:165–169`, display `:180–182`. Independently critic-reviewed. Not author-approved.

**SOURCE-ISSUES C43 addendum:**
> Plug-in estimator (2026-11-09, `Formalization/Ch7Rest/TDInferencePluginRefute711.lean`). Under the reading with
> rewards r(s,a) and r(s) = r_π(s), `Λ̂_T` (`eq:defn-hat-Lambda`, `inference.tex:180–182`) is not a consistent
> estimator of the printed Λ⋆ = A⁻¹ΓA⁻ᵀ (`:184`). The proof uses the C43 instance with V₀ = V^π:
> - Every positive-weight path has Γ̂_T = 0 and Λ̂_T = 0, for every T ≥ 1 and every η₀.
> - The printed Λ⋆(0,0) = 5/64.
> - So P(|Λ̂_T(0,0) − Λ⋆(0,0)| > 1/64) = 1 for every T ≥ 1 (`not_eq_defn_hat_Lambda_printed_consistent`, with η₀
>   in the printed range (0, 1/4)).
>
> The estimator itself targets the true noise covariance: its oracle diagonal has mean Γ_true
> (`sum_tupleProb_mul_oracleTerm`), and A⁻¹Γ_trueA⁻ᵀ = 0 in this instance. Scope:
> - Only the every-V₀ reading is refuted.
> - Under state-only rewards, or deterministic π, Γ_printed = Γ_true, and the statement is neither proved nor
>   refuted.
> - Consistency for the corrected target is open.
>
> Independently critic-reviewed. Not author-approved.

(Adjust the scope bullet if R2 lands.)

## Guidance for the remaining C3(c)–(e)

- **(c) Substitution.**
  - First do R3 (`gammaHatAt`).
  - Diagonal entry difference:
    `|Γ̂_ss(V̄) − Γ̂_ss(V^π)| ≤ ∑_t w_t 1[s_t=s] |ρ_t(V̄)² − ρ_t(V^π)²| ≤ (2B' )(1+γ)‖V̄ − V^π‖∞`.
    Here `ρ_t(V) = V(s_t) − γV(s'_t) − r_t`. B' bounds |ρ| at both points, using the deterministic `tdPathBound` /
    `abs_tdIter_sub_le` for V̄ and `tdNoiseBound` for V^π.
  - Then Markov on the first moment: P(… > ε) ≤ C ε⁻¹ E‖V̄ − V^π‖∞ ≤ C ε⁻¹ (E‖·‖²)^{1/2}.
  - Get E‖Δ̄_T‖² = O(1/T) from the existing exports (`weightedL2_scaledError_sub_prGaussPart_le_rpow` plus the
    prGaussPart second moment). Check whether these hold for every V₀ and η₀ ∈ (0,1] before stating hypotheses.
- **(d) Inverse perturbation.**
  - Use one explicit norm throughout: the ∞-row norm `max_s ∑_j |·|`, stated with explicit sums in the exported
    statements. Do not use a bare `‖·‖` on `Matrix`.
  - On the event E = {∀ s j, |Ā − A|_{sj} ≤ δ} with δ·S·‖A⁻¹‖∞ ≤ 1/2, Ā is invertible and ‖Ā⁻¹ − A⁻¹‖ ≤ 2‖A⁻¹‖²Sδ.
    So the junk event lies inside Eᶜ and needs no separate charge.
  - Alternatively, use the Gershgorin margin, which needs only n_s/T ≥ μ(s)/2.
- **(e) Assembly.** Write
  Λ̂ − Λ = (Ā⁻¹ − A⁻¹)Γ̂Ā⁻ᵀ + A⁻¹(Γ̂ − Γ_true)Ā⁻ᵀ + A⁻¹Γ_true(Ā⁻ᵀ − A⁻ᵀ).
  Bound the pieces entrywise on E ∩ {Γ̂ close} and union-bound the complements. The target statement is the
  plan-check-recommended self-contained form: `∃ C > 0, ∀ T ≥ 1, ∀ ε ∈ (0,1], pathProb … {ω | ∃ s s', ε < |lambdaHat … ω s s' −
  trueLambda … s s'|} ≤ C ε⁻² T^{−1/2}`. The hypotheses are full-support μ, 0 < η₀ ≤ 1 (or < 1/4 to match), and any V₀.
  Do **not** assume Γ_true ≻ 0, because consistency does not need it. Keep the entry name
  `Eq_defn_hat_Lambda_corrected`, and include the C43 and C47(4) disclosures and the junk sentence in its docstring.
- Run every new probe against `import Formalization` (see F0).
