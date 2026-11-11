# CRITIC round 2: item C (plug-in Λ̂_T, `eq:defn-hat-Lambda`)

Public copy of the independent critic report; local paths removed. Probe and scratch files named below (`reviewer-probes/`, `builder-probes/`) were kept in private folders and are not published.

Post-review note (added to this public copy, 2026-11-09): F4–F6 were applied to the module and declaration docs. R4 landed as `ZeroNoise.tendsto_pathProb_lambdaHat_far_printed_one` (generalized to every η₀ ∈ (0,1]) and `not_eq_defn_hat_Lambda_printed_consistent_someInit`, R5 as `eq_defn_hat_Lambda_restricted` (both in `TDInferencePluginRefute711.lean`). The preferred statement-index route was taken: the eleven pure definitions moved, with unchanged names, to `TDInference711Defs.lean`, and the entries `Eq_defn_hat_Lambda_corrected` and `Eq_defn_hat_Lambda_restricted` (printed range 0 < η₀ < 1/4, R6) were added to `Formalization/Statements/Ch7.lean` with wrappers in `Ch7Proofs.lean`. The review text below is otherwise unchanged.

Independent critic, not the builder. Date 2026-11-09. Source `chapters/inference.tex`, SHA-256
`82707713adb6c9296d9ee41faa84b2d0a12eaf1b34864a6d294de02132e648f2`. This matches `source/provenance.json`, and the
local copy was re-hashed.

Files reviewed:
- `Formalization/TDInference/PluginCovariance/Basic.lean`
- `TDInferencePluginSingular711.lean`
- `TDInferencePluginConsistency711.lean`
- `TDInferencePluginRefute711.lean`
- `TDInferencePluginCorrected711.lean` (new)
- `builder-probes/{status note, ProbeFull.lean, DRAFT-STATEMENT.lean}`

## Verdict: ACCEPT WITH FIXES

The new theorem `eq_defn_hat_Lambda_corrected` is correct. It states the right corrected reading, has no hidden
hypothesis, handles Lean's junk inverse soundly, and is non-vacuous. All round-1 fixes are in place.

The remaining required fixes are **documentation only** (F4–F6). Several docstrings became stale or overstated once
the corrected theorem landed. No proof or signature changes. Two cheap additions are recommended: R4 (the some-V₀
refutation) and R5 (the restricted variant). Both were compiled in the critic probes.

## Evidence (commands actually run)

- `bash scripts/lean-local.sh reviewer-probes/ProbeR2.lean`. It imports `Formalization` plus
  all 5 plugin modules (Plugin, Singular, Consistency, Refute, Corrected). Exit 0, no errors, wall time 1:22.
  - 15 `#print axioms` checks all give `[propext, Classical.choice, Quot.sound]`. The checks cover:
    - `eq_defn_hat_Lambda_corrected`, `tendsto_pathProb_lambdaHat_entry`, `exists_delta_lambda`;
    - both (c) moment lemmas, `abs_gammaHat_sub_oracle_le`, `sampleAMat_mulVec`;
    - `not_eq_defn_hat_Lambda_printed_consistent`, `ZeroNoise.pathProb_far_nonsingular_ge`;
    - `gammaHatAt_valueFixedPoint_diag`, `gammaHat_eq_gammaHatAt`;
    - `aBar_det_ne_zero_iff`, `pathProb_aBar_singular_pos`, and the C3(a)/(b) tail bounds.
  - `#print Eq_defn_hat_Lambda_corrected` shows the elaborated Prop. Its binders are as reviewed below.
  - Extra probe checks, all compiled:
    - (a) The printed-range form (`η₀ < 1/4`) follows from the export by `linarith`.
    - (b) `Eq_defn_hat_Lambda_corrected ∧ ¬ Eq_defn_hat_Lambda_printed_consistent`.
    - (c) **New:** `probe_far_tendsto_one`. In instance Z, for **every** V₀ (η₀ = 1/8),
      `P(∃ s s', 1/64 < |Λ̂_T(s,s') − Λ⋆(s,s')|) → 1`. This is a 45-line corollary of the corrected theorem
      (see R4). Its axioms are the standard three.
- `bash scripts/lean-local.sh reviewer-probes/ProbeRestricted.lean`. Exit 0.
  `probe_restricted` proves that `Λ̂_T → printed Λ⋆` in probability when r(s,·) is constant on the support of
  π(·|s) (see R5). Its axioms are the standard three.
- `grep -n "sorry\|admit\|axiom"` over the 5 plugin files finds nothing.
- Every `.olean` is newer than its source (Corrected 07:53 vs source 07:52; the others 07:45 vs ≤07:45).
- Process discipline: one Lean process at a time, each started only after `pgrep -x lean | wc -l` returned 0. No
  lake, LSP or git commands. No repo edits outside `reviewer-probes/` and this report.

## Round-1 fixes: verification

| Item | Status | Where |
|---|---|---|
| F0 rename | ✓ | `sampleAMat`, `sampleAMat_apply`, `sum_tupleProb_mul_sampleAMat`, `abs_sampleAMat_apply_le`. `ProbeR2` imports `Formalization` together with all 5 modules with no collision. |
| F0 bridge | ✓ | `sampleAMat_mulVec : (sampleAMat M x).mulVec v = sampleA M x v` (Corrected711:54) |
| F1 η₀ < 1/4 | ✓ | `Eq_defn_hat_Lambda_printed_consistent` assumes `0 < η₀ → η₀ < 1/4`. The docstring now says only full support and `Γ_printed ≻ 0` weaken the claim. |
| F2 citations | ✓ in Plugin711 | `:166` (A_t, Ā_T), `:168` (Γ̂, b_t), align* `:165–169`, weights `:175–177`, display `:180–182`, `:184`, `:185`. All checked against the pinned tex. **Residual:** Consistency711's header cites `:166–168` for "Ā_T as an estimator of A", but those words are at `:172` (F4). |
| F3(a) C43 caveat | ✓ but now stale | Present on both the Prop and the refutation. It says the state-only reading is "neither proved nor refuted". The corrected theorem now **proves** it (F5, R5). |
| F3(b) junk sentence | ✓ | Present on the Prop and on the refutation |
| R1 | ✓ | `ZeroNoise.pathProb_far_nonsingular_ge`: `1 − 2·2^{-T} ≤ P({det Ā ≠ 0} ∩ far)`. The proof is checked, and it is cited in the refutation docstring. |
| R3 | ✓ | `gammaHatAt`, `gammaHat_eq_gammaHatAt` (`rfl`), `gammaHatAt_apply`, `gammaHatAt_valueFixedPoint_diag`. `oracleGammaHat` is now the diagonal of the printed Γ̂ formula at V^π. |

## Review of `TDInferencePluginCorrected711.lean`

### Is the Prop the right corrected reading of `:184`?

- **The source.** It says "We take Λ̂_T = Ā_T⁻¹Γ̂_T(Ā_T⁻¹)ᵀ to be the final estimator of Λ⋆" (`:180–184`), and
  `:172` calls Ā_T and Γ̂_T "estimators of A and Γ". No mode of convergence or rate is given anywhere. The weakest
  standard meaning of "estimator of X" that is still non-trivial is **consistency**. In finite dimension, entrywise
  convergence in probability is equivalent to convergence in probability in any matrix norm.
- **The Prop.** It is `∀ instance, ∀ η₀ ∈ (0,1], ∀ V₀, ∀ ε > 0, P(∃ s s', ε < |Λ̂_T(s,s') − Λ(s,s')|) → 0`. This is
  exactly that. The quantifier order is identical to the refuted printed Prop, so the pair is a clean
  "corrected ∧ ¬printed" (compiled).
- **Disclosure.** The result is qualitative, with no rate. This is disclosed in the module doc ("Rate caveat") and
  the docstring. It must also appear in COVERAGE (text below).
- **Target.** The target is `trueLambda = A⁻¹ diag(Γ_true) A⁻ᵀ`, the C43 correction. This target is supported by
  the source itself:
  - The commented-out line `inference.tex:108` reads `Γ = E[(A_tθ⋆ − b_t)(A_tθ⋆ − b_t)ᵀ]`.
  - Evaluated at θ⋆ = V^π, that expression is exactly diag(`trueGamma`).
  - Because it is a comment, cite it as "author's commented-out definition", not as printed text.

### Is `trueLambda` the true limit?

- **Definition.** `trueLambda = (tdA)⁻¹ * diagonal(trueGamma) * ((tdA)⁻¹)ᵀ`, with `tdA = diag(μ)(I − γP_π)`
  (`:110`). Lean's `Matrix.inv` is the true inverse here: the proof derives `det tdA ≠ 0` from
  `tdA_isUnit M π μ hμmin0 hμmin`, using full support, which is the printed λ₀ > 0 at `:67`.
- **Γ_true.** `trueGamma(s) = μ(s)E_{a,s'}[(V^π(s) − r(s,a) − γV^π(s'))²]` is the per-sample noise covariance.
  The noise is centred because `A V^π = b`.
- **Library consistency.** `trueLambda` is the same object as the covariance of the corrected CLT limit.
  `exists_sum_pathWeight_mul_sq_prAverage_sub_le` rewrites the second moment of the Gaussian part through
  `sum_pathWeight_mul_prGaussPart_mul` as `trueLambda u u`. `Eq_classic_clt_corrected` uses
  `gaussCov (tdA) (trueGamma)`, which is N(0, A⁻¹ diag(Γ_true) A⁻ᵀ).

### Hidden hypotheses

There are none beyond the following:
- `[Nonempty State]` and `[Nonempty Action]`, which are benign. A policy cannot exist on an empty action type when
  State is nonempty.
- `DecidableEq`, which is universally quantified.
- Full support, which is the printed λ₀ > 0.
- `0 < η₀ ≤ 1`, which contains the printed `(0, 1/4)`.

No `Γ_true ≻ 0` is assumed, and a degenerate Λ is allowed (instance Z has Λ = 0). T = 0 is irrelevant to a limit.

### Proof steps

**(c) Substitution.** Checked line by line.
- **Step 1.** `E(V̄_T(u) − V^π(u))² ≤ C/T`. This follows from the L² remainder `K·T^{-1/6} ≤ |K|` plus
  `‖W_T(u)‖₂ = √Λ(u,u)`, giving `‖√TΔ̄_T(u)‖₂ ≤ |K| + √Λ(u,u)`.
- **Step 2.** The pathwise identity `residual = ξ + d` with `d = (V̄ − V)(i) − γ(V̄ − V)(s')`.
- **Step 3.** `(ξ+d)² − ξ² = d(2ξ+d)`, with |d| ≤ 2m and |d| ≤ 2D, gives `|Γ̂_ii − Γ̂^{or}_i| ≤ 4(B+D)m`. The
  weights sum to 1.
- **Step 4.** Cauchy–Schwarz gives `m² ≤ S∑(V̄−V)²`, hence `C'/T`.

All constants depend only on the instance, η₀ and V₀, which is allowed because ε and T come later.

**(d) Inverse perturbation and Lean's 0-inverse.** The proof is sound.
- δ comes from `ContinuousAt` of the map `(X, Y) ↦ (X⁻¹YX⁻ᵀ)(s,s')` at `(A, diag Γ_true)`. That map is built from
  **Lean's actual `Matrix.inv`**, via `continuousAt_matrix_inv` with `Ring.inverse` continuous at `det A ≠ 0`.
- So for every path with `|Ā − A| < δ` and `|Γ̂ − diag Γ_true| < δ` entrywise, `|lambdaHat − Λ| < ε` holds
  **whatever value `Matrix.inv` takes**. The junk value needs no separate treatment.
- The off-diagonal entries of Γ̂ are exactly 0 (`gammaHatAt_apply`), so the Y-closeness off the diagonal is
  trivial.
- **However, the prose overstates this (F6).** The module doc says "the junk-inverse (singular) event lies inside
  {∃ i j, δ/2 < |Ā_T − A|_{ij}}". The proof does not establish that, and for the continuity δ it can be false.
  - In instance Z, Λ = 0, so the junk value 0 is already within ε of Λ.
  - The continuity δ is therefore not forced below the det-nonvanishing radius.
  - Singular Ā can then lie within δ/2 of A. One example is the all-state-0 path, which has
    Ā = [[1/2, −1/4], [0, 0]] against A = [[3/8, −1/8], [−1/8, 3/8]].
  - What is true is that on those paths |Λ̂ − Λ| < ε already.

**(e) Assembly.**
- The inclusion `{far} ⊆ EA ∪ ⋃_i (ES_i ∪ EO_i)` is proved by contraposition, using the triangle inequality for the
  diagonal.
- The rates are S²/((δ/2)²T), Csub/((δ/4)²T) and 2B⁴/((δ/4)²T), followed by `squeeze_zero`.
- The step from an entry to all entries is a finite union over `State × State`. ✓

### Non-vacuity

- The builder's `ProbeFull` example applies the theorem to instance Z (full-support μ, η₀ = 1/8, V₀ = 0).
- The critic probe compiled `corrected ∧ ¬printed`.
- The hypotheses are jointly satisfiable, and the target differs from the printed one (Λ = 0 vs Λ⋆(0,0) = 5/64).

## Required fixes (documentation only; no signature or proof change)

**F4 (stale and overclaiming header, Consistency711).** The module doc's "Not yet done (remaining C3): … the
assembly into `P(∃ s s', |Λ̂_T(s,s') − Λ(s,s')| > ε) ≤ C ε⁻² T^{-1/2}`" is now stale, and it advertises a rate
that is **not** proved. Replace it with a pointer to `TDInferencePluginCorrected711.lean` that says "convergence in
probability, no rate". Also change the "as an estimator of A" locator from `:166–168` to `:172`, and the definition
locators to `:166`.

**F5 (stale scope statements, Plugin711 and Refute711).**
- (a) The C43 reading caveat on `Eq_defn_hat_Lambda_printed_consistent` and on
  `not_eq_defn_hat_Lambda_printed_consistent` says the state-only / deterministic-π reading "is neither proved nor
  refuted here". It is now proved by `eq_defn_hat_Lambda_corrected` together with
  `trueGamma_eq_printedGamma_of_reward_const_on_support` (critic probe `probe_restricted`). Change the wording to
  "is proved (`Eq_defn_hat_Lambda_restricted`)" if R5 is adopted, or else "follows from
  `eq_defn_hat_Lambda_corrected`, since then `printedLambda = trueLambda`".
- (b) The Refute711 module doc says "The some-`V₀` reading is not refuted here (it would need the consistency theorem
  for the corrected `Λ` …)". The theorem now exists. Either adopt R4 and say "refuted for every V₀", or say "not yet
  stated; follows from `eq_defn_hat_Lambda_corrected` since `trueLambda = 0 ≠ printedLambda` in Z".

**F6 (junk-value prose, Corrected711).**
- Replace the module-doc sentence "Near `A` Lean's `Matrix.inv` is the true inverse, so the junk-inverse (singular)
  event lies inside `{∃ i j, δ/2 < |Ā_T − A|_{ij}}` and is charged there" with an accurate one. Suggested wording:
  > `δ` comes from continuity, at `A`, of the map built from Lean's actual `Matrix.inv` (which agrees with the true
  > inverse near `A`). So the closeness implication holds pathwise whatever value `Matrix.inv` takes, and the
  > singular event needs no separate term.
- In the module doc's "Junk value" paragraph and the `Eq_defn_hat_Lambda_corrected` docstring, "whose probability
  is charged in the bound" may stay. Optionally add: "the conclusion does not depend on the junk convention, since
  `P(Ā_T singular) ≤ ∑_s(1−μ(s))^T → 0` (`pathProb_aBar_singular_le`)".

## Recommendations

**R4 (some-V₀ refutation; supersedes round-1 R2, now cheap).** Add the critic's `probe_far_tendsto_one` (45 lines,
compiled; text in `reviewer-probes/ProbeR2.lean`) to a module that imports Refute711 and Corrected711. It needs only
`zTrueLambda`, `zPrintedLambda_00`, `pathProb_union_le`, `pathProb_univ` and `pathProb_mono`. The proof:
- In instance Z, Λ = 0 and Λ⋆(0,0) = 5/64. If |Λ̂(0,0)| ≤ 1/64, then |Λ̂(0,0) − 5/64| > 1/64.
- So `P(far from Λ⋆) ≥ 1 − P(far from Λ) → 1`, for every V₀.

A ¬-Prop form is `¬ (∀ inst, ∃ V₀, consistent)`. It lets C43 and COVERAGE say "for every initialization V₀". It
can be generalized to every η₀ ∈ (0,1], since the proof does not use η₀ = 1/8 beyond the hypotheses.

**R5 (restricted variant).** Add `Eq_defn_hat_Lambda_restricted`, the printed Λ⋆ under
`∀ s a a', 0 < π(a|s) → 0 < π(a'|s) → r(s,a) = r(s,a')`. It mirrors `Eq_classic_clt_restricted`. The proof is
the critic's `probe_restricted`: four lines, compiled.

**R6 (statement-index form uses the printed range).** As with `Eq_classic_clt_corrected` (export η₀ ≤ 1, entry
η₀ < 1/4), the index entry should state `0 < η₀ → η₀ < 1/4`. The `Ch7Proofs` wrapper is
`fun … h1 … ↦ eq_defn_hat_Lambda_corrected … (by linarith) …` (compiled as probe (a)). This is an export that
assumes less, so it is not a SOURCE-ISSUES matter.

**R7 (rate).** The only obstacle to an explicit rate is the non-explicit δ. A rate of order `C(ε)/T` per entry is
implied but not quantified. Leave this open, and do not claim `T^{-1/2}` anywhere (F4).

## Statement-index route

`Statements/Ch7.lean` may import only the G2-frozen modules. `TDInference711Defs` is on that list.
`TDInferencePlugin711` is not, and the list "may only shrink" (`scripts/gates/g2_statement_imports.txt`,
`scripts/static_gates.py` gate_g2).

The entry needs `pathProb`, `aBar`, `sampleAMat`, `sampleB`, `pluginWeight`, `pluginResidual`, `gammaHat`,
`lambdaHat` and `trueLambda`. The last also needs `printedLambda` for R5. `prAverage`, `tdA`, `trueGamma` and
`printedGamma` are already in Defs.

- **Preferred: move the pure definitions into `TDInference711Defs.lean`.**
  - Move the 11 defs listed above, with their docstrings. Keep all lemmas and the refuted Prop
    `Eq_defn_hat_Lambda_printed_consistent` in `Plugin711`. Moving the Prop as well is acceptable but not needed.
  - The G2 list does not grow, the names stay the same, the reader sees the library objects, and the wrapper is a
    direct application.
  - `ProbeR2` (import Formalization + all plugin modules) already shows that the names collide with nothing. Defs
    already imports `Mathlib.LinearAlgebra.Matrix.NonsingularInverse`. It needs `open scoped Matrix` for `ᵀ`.
  - Cost: Defs is upstream of the whole TDInference chain, so there is one rebuild of roughly 30 modules. Schedule
    it when no other Lean job is running.
- **Alternative: inline.** Copy the bodies verbatim into `Ch7.lean` as `noncomputable def`s in the
  `StatisticalRL.Statements.Ch7` namespace. The wrapper is then `eq_defn_hat_Lambda_corrected` up to definitional
  unfolding, by `exact` or `simpa only [...]`. There is no rebuild, but it duplicates about 40 lines that can drift.
  Use it only if the rebuild is unaffordable now.
- **Not allowed:** a new `TDInferencePluginDefs711` module or `Statements/Ch7Definitions`. Either one grows G2.

Remember G3: the entry, `docs/named-result-status.json`, the COVERAGE row and SOURCE-ISSUES must be consistent and
must land in the same change.

### Recommended entry text (`Formalization/Statements/Ch7.lean`)

```lean
/-- Corrected `eq:defn-hat-Lambda` (`chapters/inference.tex:180–182`; "the final estimator of
`Λ⋆`" :184; `Ā_T`, `Γ̂_T` :165–169, weights :175–177), read as consistency. Differs from the printed
claim: the target is `Λ = A⁻¹ diag(Γ_true) A⁻ᵀ` (true TD-noise covariance), not the printed
`Λ⋆ = A⁻¹ΓA⁻ᵀ`; under action-dependent rewards with `r(s) = r_π(s)` the printed reading is false
(SOURCE-ISSUES C43). For every finite instance with full-support i.i.d. sampling (`λ₀ > 0`, :67),
every `0 < η₀ < 1/4` and every `V₀`, `Λ̂_T → Λ` entrywise in probability. No `Γ_true ≻ 0` is assumed.
Qualitative: no rate. Junk value: on the event that some state is unsampled, `Ā_T` is singular and the
printed `Λ̂_T` is undefined (C47(4)); Lean's `Matrix.inv` returns 0 there, so `lambdaHat = 0` on that
event, whose probability `≤ ∑_s (1 − μ(s))^T` tends to 0. -/
def Eq_defn_hat_Lambda_corrected : Prop :=
  ∀ (State Action : Type) [Fintype State] [DecidableEq State] [Nonempty State]
    [Fintype Action] [Nonempty Action]
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (μ : FiniteDistribution State) (η₀ : ℝ) (V₀ : State → ℝ),
    (∀ s, 0 < μ.prob s) → 0 < η₀ → η₀ < 1 / 4 →
    ∀ ε : ℝ, 0 < ε →
      Filter.Tendsto (fun T : ℕ ↦ pathProb M π μ T
        {ω | ∃ s s', ε < |lambdaHat M η₀ V₀ ω s s' - trueLambda M π μ s s'|})
        Filter.atTop (nhds 0)
```

The optional `Eq_defn_hat_Lambda_restricted` has the same shape, with the reward-constancy hypothesis first and
`printedLambda` as the target. Its docstring says: "the printed Λ⋆ under state-only rewards or deterministic π, where
Γ_printed = Γ_true (C43 scope)".

The wrappers in `Ch7Proofs.lean`:
- corrected: `fun S A _ _ _ _ _ M π μ η₀ V₀ hμ h0 h1 ε hε ↦ eq_defn_hat_Lambda_corrected S A M π μ η₀ V₀ hμ h0 (by linarith) ε hε`;
- restricted: as in `ProbeRestricted.lean`.

## Recommended COVERAGE text (`eq:defn-hat-Lambda`, inference chapter lines 156–185)

> **Printed reading refuted under C43; corrected (and restricted) variants proved; qualitative only.**
>
> Definitions formalized: `aBar`, `gammaHat`, `lambdaHat` (`TDInferencePlugin711.lean`). The printed weights
> w_{t,T} = 2t/(T(T+1)) with ∑w = 1 are machine-checked (`pluginWeight_eq`, `sum_pluginWeight`).
>
> Corrected (`Eq_defn_hat_Lambda_corrected`, export `eq_defn_hat_Lambda_corrected`, `TDInferencePluginCorrected711.lean`).
> For every finite instance with full-support i.i.d. sampling, 0 < η₀ < 1/4 (export: 0 < η₀ ≤ 1) and every V₀,
> Λ̂_T → Λ = A⁻¹Γ_trueA⁻ᵀ entrywise in probability.
> - No Γ_true ≻ 0 is assumed. The convergence is in probability only, and **no rate** is established (the
>   inverse-perturbation δ comes from continuity).
> - The proof steps are: Ā_T → A at rate S²/(ε²T); the oracle Γ̂ → Γ_true at rate 2B⁴/(ε²T); the substitution
>   V̄_T → V^π via E(V̄_T − V^π)² ≤ C/T; then continuity of (X, Y) ↦ X⁻¹YX⁻ᵀ at (A, diag Γ_true).
>
> [If R5 is adopted:] Restricted (`Eq_defn_hat_Lambda_restricted`): the printed Λ⋆ when r(s,·) is constant on the
> support of π(·|s).
>
> Refuted (`not_eq_defn_hat_Lambda_printed_consistent`, with η₀ in the printed range): with action-dependent rewards
> and r(s) = r_π(s), Λ̂_T is not consistent for the printed Λ⋆ ([C43](SOURCE-ISSUES.md#C43)). In the two-state
> zero-noise instance from V₀ = V^π, Λ̂_T = 0 surely while Λ⋆(0,0) = 5/64. The refutation does not depend on the
> junk value (`pathProb_far_nonsingular_ge`). [With R4: … and from every V₀, P(|Λ̂_T(0,0) − Λ⋆(0,0)| > 1/64) → 1.]
>
> On the event that some state is unsampled, Ā_T is singular and the printed Λ̂_T is undefined
> ([C47](SOURCE-ISSUES.md#C47)(4); `aBar_det_ne_zero_iff`, positive probability for S ≥ 2). Lean's `Matrix.inv`
> returns 0 there. That event has probability ≤ ∑_s(1−μ(s))^T → 0, so consistency is unaffected.
>
> Not formalized: the online-computability claim (`:185`), any rate for Λ̂_T, and the plug-in confidence rule (C47).
> [Review](critic-plugin-r2.md). Not author-approved.

Also update the `eq:convex.Cdelta` row: "Open: the plug-in Λ̂_T rule" becomes "Open: the plug-in Λ̂_T rule
(consistency of Λ̂_T is now proved, qualitatively; a covariance-perturbation coverage bound is still missing)".

## Recommended SOURCE-ISSUES addenda

**C43 addendum** (replaces the round-1 draft):

> **Plug-in estimator (2026-11-09; `TDInferencePluginRefute711.lean`, `TDInferencePluginCorrected711.lean`).**
>
> Under the reading with rewards r(s,a) and r(s) = r_π(s), Λ̂_T (`eq:defn-hat-Lambda`, `inference.tex:180–182`) is
> not a consistent estimator of the printed Λ⋆ = A⁻¹ΓA⁻ᵀ (`:184`; also `:172`, "estimator of Γ").
> - In the C43 two-state instance from V₀ = V^π: Γ̂_T = 0 and Λ̂_T = 0 surely, for every T ≥ 1 and every η₀,
>   while Λ⋆(0,0) = 5/64 (`not_eq_defn_hat_Lambda_printed_consistent`, with η₀ in the printed range (0, 1/4)).
> - The refutation is independent of the junk inverse (`pathProb_far_nonsingular_ge`).
> - [R4: from every V₀ the far-event probability tends to 1.]
>
> Proposed correction, machine-checked: Λ̂_T is consistent for Λ = A⁻¹Γ_trueA⁻ᵀ, entrywise in probability, for
> full-support sampling, every η₀ ∈ (0,1] and every V₀, without Γ_true ≻ 0 (`eq_defn_hat_Lambda_corrected`).
> - The convergence is qualitative, with no rate.
> - The source's own commented-out definition (`:108`, not printed), Γ = E[(A_tθ⋆ − b_t)(A_tθ⋆ − b_t)ᵀ], equals
>   diag(Γ_true) at θ⋆ = V^π.
> - With state-only rewards or deterministic π, Γ_true = Γ_printed, and the printed reading holds
>   ([R5: `Eq_defn_hat_Lambda_restricted`]).
>
> Independently critic-reviewed (critic-plugin.md, critic-plugin-r2.md). Not author-approved.

**C47(4) addendum.** Use the round-1 text, with two changes:
- The line references `:165–169` and `:180–182` are already correct in the current C47 entry (`:156–185` is also
  fine).
- Add a final sentence:
  > Consistency is not prevented: P(Ā_T singular) ≤ ∑_s(1−μ(s))^T → 0, and the corrected consistency theorem
  > (`eq_defn_hat_Lambda_corrected`) holds with Lean's junk value 0. The procedure is still undefined on that event
  > for finite T, so any confidence rule must define it there and charge that event's probability.

Also update the C47 "Still open" line: "consistency of Λ̂_T" is done, and "a covariance-perturbation coverage bound"
remains open.

## Scope reminder for the lead

- `Eq_defn_hat_Lambda_corrected` is a corrected variant of a display claim. It is not the printed result and not a
  numbered theorem.
- Whole-chapter and whole-paper completion are unaffected.
- Online computability (`:185`) and any rate remain open.
