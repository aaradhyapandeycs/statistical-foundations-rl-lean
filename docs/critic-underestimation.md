# CRITIC: `Thm4_6_underestimation` and the F2 re-witness of Theorem 4.6 at c₁ = c₂ = 1

Public copy of the independent critic report; local paths removed.

Post-review note (added to this public copy, 2026-11-09): this critic reviewed the pre-integration snapshot; integrated into the library on 2026-11-09 with the Theorem 4.6 re-witness in the same change. Snapshot files map to the integrated locations as follows: `Coupling.lean` → `Formalization/ModelFree/QLearningUnderestimationCoupling.lean`; `Lift.lean` → `Formalization/ModelFree/QLearningUnderestimationLift.lean`; `Law.lean` → `Formalization/ModelFree/QLearningUnderestimationLaw.lean`; `Value.lean` → `Formalization/ModelFree/QLearningUnderestimationValue.lean`; `LogCube.lean` → `Formalization/ModelFree/TDLogCubeUnitConstants.lean`; `Main.lean` → `Formalization/ModelFree/QLearningUnderestimation.lean`; `Definitions.lean` → definitions appended to `Formalization/ModelFree/QLearningSamplingDefinitions.lean`; `Statement.lean` → the `Thm4_6_underestimation` entry in `Formalization/Statements/Ch4.lean`; `StatementProof.lean` → the `Thm4_6_underestimation_holds` wrapper in `Formalization/Statements/Ch4Proofs.lean`; `Thm46Unit.lean` → the proof body of `qLearning_exists_universal_constants_source_accuracy` in `Formalization/ModelFree/QLearningSourceTheoremClosure.lean` (the reviewed `…source_accuracy_unitWitness` body became the export's body, signature unchanged; the former 1/4 body is retained as `qLearning_exists_universal_constants_source_accuracy_quarter`). Short file names below refer to the reviewed snapshot files, and the file hashes are those of the snapshot. The review text below is otherwise unchanged.

Independent critic. Date 2026-11-08. I did not build this work. I edited no builder file and nothing under
`Formalization/`.

## Verdict: ACCEPT WITH DISCLOSURES

- No R-item (refutation) was found.
- The Prop is faithful to the printed under-estimation display at `generative_model_model_free.tex:1873–1879`,
  read in the context of Theorem 4.6. It is stronger than printed in disclosed ways: no budget, no `A ≥ 2`,
  and it holds for every optimal deterministic `f`.
- The proof compiles independently and its axioms are clean.
- The F2 re-witness has a type that is syntactically identical to the library export.
- Integration must address F-items F1–F3. F4 and F5 are optional.

## Source read first (sha256 `7f4eb058…2b22`)

- `:841–870` `alg:q-infinite` (begin `:841`, label `:869`, end `:870`). The synchronous update is
  `Q_t = (1−η_t)Q_{t−1} + η_t(r + γ max_{a'} Q_{t−1}(s_t(s,a), a'))`.
- `:881–886` `eq:thm:infinite-horizaon-eta`. This is the log³T schedule over `0 ≤ t ≤ T`, with
  "universal constants c₁ ≥ c₂ > 0". **c₂ ≤ c₁ is printed.**
- `:891–912` Theorem 4.6. It requires "small enough universal constants c₁ ≥ c₂ > 0", `A ≥ 2`, the budget,
  and `0 ≤ Q₀ ≤ 1/(1−γ)`. `:1277` of the proof itself says "taking c₁ ≤ 1", so c₁ = 1 is admissible.
- `:1869–1881` is the paragraph.
  - `:1871` describes the auxiliary iteration: "same initialization and transition samples", following "a
    deterministic optimal policy π⋆ instead of maximizing over actions". It also says "Q̃_t ≤ Q_t".
  - `:1873–1879` is the display `Q_T−Q⋆ ≥ Q̃_T−Q⋆ ≥ −Õ(√(1/((1−γ)³T)))1_{SA}`.
  - `:1882–1886` are blank and `:1887` is the next section. The F1 citation is correct.

## (1) Prop fidelity, checked against the source

| Item | Finding |
|---|---|
| ∃ c₁ c₂ C, `0 < c₂ ≤ c₁`, `0 < C` | c₁ ≥ c₂ > 0 is printed (`:886`). C is the Õ constant, made explicit. |
| Schedule | Character-identical to the `Thm4_6` entry (`Ch4.lean`) and to `qSourceRateSchedule`: `∀ k ≤ T`, lower bound `1/(1+c₁(1−γ)T/log³T)`, cap `1/(1+c₂(1−γ)k/log³T)`. Same indexing (0 ≤ k ≤ T, as at `:885`). |
| Q₀ | `0 ≤ Q₀ ≤ effectiveHorizon = 1/(1−γ)`, as at `:902`. |
| γ, T, δ | `1/2 ≤ γ`, `T ≥ 2` and `δ ∈ (0,1)` come from Theorem 4.6's context. |
| Auxiliary sequence | `qPolicyEvaluationIterate` is the `qLearningIterate` recursion (`QLearningIterateBounds.lean:18–25`) with `max_{a'} Q(s',a')` replaced by `Q̃(s', f s')`. It uses the same `η (t+1)`, the same `samples (t+1) s a`, and the same Q₀. `qPolicySampledIterate` uses the same `qSamplesExtend M T data` as `qSampledIterate`. This is exactly the source's auxiliary sequence at `:1871`. |
| Optimal f | `∀ s, V^{pointMass ∘ f}(s) = V^{optimalGreedyPolicy}(s)`, which is "deterministic optimal policy". It is quantified universally over every such f, which is stronger. It is non-vacuous: probe (D) shows `f = optimalGreedyAction` satisfies it by `rfl`. |
| Clause 1 | Pathwise, for every data array. This is the first display inequality. |
| Clause 2 | `1−δ ≤ P{∀ s a, −C√(log⁴T·log(SAT/δ)/((1−γ)³T)) ≤ Q̃_T − Q⋆}` under the actual product law. With clause 1 it yields `Q_T − Q⋆ ≥ …` on the same event, which is the full printed chain. The (1−γ)⁻³ and T⁻¹ powers are explicit. The Õ hides only `log⁴T·log(SAT/δ)`, disclosed in the docstring with C = 91. |
| Stronger than printed | No budget premise and no `A ≥ 2`. Both are disclosed. |
| Weaker than printed | Nothing beyond the project-wide existential encoding of "small enough" constants. This is disclosed: c₂ < 1 is not covered, and it is a proof-infrastructure limit, not a source error. |
| Non-vacuity | Probe (E): the rescaled linear rate `η_k = 1/(1+(1−γ)k/log³T)` satisfies the (1,1) schedule. Clause 2 is not trivially true for a fixed C: it binds once `91√X < 1/(1−γ)`, which happens for all large T. |
| Prop vs export | `Thm4_6_underestimation`'s body vs `qLearning_underestimation_exists_universal_constants`'s type has one structural difference: an auxiliary `OfNat`/`AtLeastTwo` proof term (`Thm4_6_underestimation._proof_1` vs `Nat.instAtLeastTwoHAddOfNat 1`). They are defeq at reducible transparency (probe (B)). This is benign. |

## (2) Junk values

- `log T`: T ≥ 2, so log T > 0 and log³T > 0.
- `log(SAT/δ)`: SAT/δ > SAT ≥ 2, so the log is positive (proved: `hℓ`).
- Division by `(1−γ)³T`: positive, because γ < 1 and T ≥ 2.
- `Real.sqrt` argument: positive (`hX`).
- The probability event: every set is measurable. The σ-algebras are `⊤` on finite types, so the
  coordinate maps and events are measurable via `measurable_of_countable` and `Set.to_countable`.
  `.real` is therefore the genuine probability.
- `qSamplingLaw` is a probability measure; `probReal_univ` is used in the trivial case.
- `η 0` is constrained by the schedule but never used. This is harmless and matches `Thm4_6`.

## (3) F2 re-witness

- **Signature.** `qLearning_exists_universal_constants_source_accuracy_unitWitness` has level params
  `[u, v]` and a type `Expr.eqv`-identical to `qLearning_exists_universal_constants_source_accuracy`
  (probe (A): `true`).
- **Witnesses.** (1, 1, c₃ from `qFinal_exists_universal_budget_constant 1`). The body mirrors the existing
  export, with `qLearning_conditional_source_accuracy` called directly at (1,1). That lemma needs only
  `0 < c₁ ≤ 1` and `0 < c₂`, consistent with source `:1277`.
- **Downstream.** Only two consumers exist: `MeanError.lean:200` (Remark 4.2) and `Ch4Proofs.lean:88`
  (`Thm4_6_holds`). Both consume an ∃-Prop and cannot observe the witness, so their statements are
  unchanged. Probe (C) (`CriticProbe2.lean`) derives the current `Thm4_6` entry from the unit witness, with
  axioms `[propext, Classical.choice, Quot.sound]`.
- **Honesty.** Moving the witness 1/4 → 1 is an honest change: the entry states ∃ constants and the Prop
  is unchanged. The (1,1) class contains both rate examples from `:887`/`:945–953`.
- **Side effect (must be disclosed).** The index no longer certifies Theorem 4.6 at (1/4,1/4) through a
  named unconditional export.
- **Text that claims 1/4 for Theorem 4.6:**
  - `Formalization/Statements/Ch4.lean:140–142`, the `Thm4_6` docstring. Covered by DRAFTS-FOR-LEAD.
  - **`docs/ERRATA-AND-DEVIATIONS.md:52`**: "for Theorem 4.6, the first two constants are `1/4` … See …
    QLearningConditionalUniversalConstants.lean". DRAFTS-FOR-LEAD does **not** cover this; its statement
    "No docs/COVERAGE or named-result-status text cites 1/4 for Theorem 4.6 (grep checked)" is wrong for
    the ERRATA file. → F1.
  - `docs/critic-q-learning-conditional-final-independent.md:63` is a historical review and should stay
    unchanged.
  - `QLearningConditionalUniversalConstants.lean:51–54` is the conditional wrapper, not a Theorem 4.6
    claim.
  - `named-result-status.json` and `COVERAGE.md` do not cite 1/4.
  - `site/` has no hits.

## (4) Math spot checks

- **Coupling** (`Coupling.lean`). The induction gives
  `Q_{t+1} − Q̃_{t+1} = (1−η)(Q_t−Q̃_t) + ηγ(max Q_t(s',·) − Q̃_t(s',f s'))`. Each term is ≥ 0 when
  η ∈ [0,1] and γ ≥ 0, using `le_actionMaximum` and `ih` at s'. Rates in [0,1] follow from the (1,1)
  schedule (`qLogCubeUnitSchedule_unit`). Nonnegativity of Q̃ is proved the same way. Correct.
- **Lift** (`Lift.lean`). The lifted model has states S×A, action Unit, reward r(s,a), the same γ, and
  transition `bind P(·|s,a) (s' ↦ δ_{(s', f s')})`. `policyReward` under `pointMass ()` equals r(s,a).
  `tdIterate` on the lifted model equals `qPolicyEvaluationIterate` by induction. The exact-T extension
  agrees on 1..T (`tdIterate_congr_samples`). Indices: TD reads `data(x, k−1)` for `1 ≤ k ≤ T`, and Q reads
  `data((s,a), t−1)` for `0 < t ≤ T`, the same coordinates. Correct.
- **Law** (`Law.lean`). `Measure.pi_map_pi` applies the coordinatewise map, and
  `rowMeasure.map (s' ↦ (s', f s'))` equals the lifted row via `PMF.toMeasure_map` and a finite sum. The
  single-action mixture row is shown to equal the lifted transition. The padded→exact `Fin.succ` marginal is
  handled by `tdUsedSampleProjection_map_law` in `LogCube.lean`. F5 is satisfied.
- **Value identity** (`Value.lean`). The forced-action Q-function `Q^f` is a fixed point of the lifted
  policy Bellman operator, so by uniqueness the lifted V equals `Q^f`. Since `V^f = V⋆`,
  `Q^f = r + γPV^f = r + γPV⋆ = Q⋆`, via `policyFixedPoint_eq_reward_add_value` twice. Correct.
- **Log-cube transport** (`LogCube.lean`). It uses c' = 1/L and c₃' = 8192L.
  - `(1/L)(1−γ)i/L² = (1−γ)i/L³` (`field_simp`).
  - `htime`: `T/(c'L) = T ≤ T`.
  - c'c₃' = 8192.
  - c₃' ≥ 3168 because L ≥ log 2 ≥ 1/2.
  - c'² ≤ 1/8 because L ≥ 4. This comes from 8192L⁵ ≤ T ⇒ T ≥ 256 ⇒ L ≥ 8 log 2.
  - The budget `c₃'L³ℓ = 8192L⁴ℓ` matches.

  All TD layers consume c₁', c₂', c₃' as ordinary reals with explicit side conditions, and every condition
  is discharged. No hidden premise.
- **ε case split** (`Main.lean`). Let ε = √(8192X).
  - If ε ≤ 1/(1−γ), the budget holds with equality. The TD event pulls back by preimage, and the lower
    half of `|·| ≤ ε` gives `−91√X ≤ −ε ≤ Q̃ − Q⋆`.
  - Otherwise, `Q̃ ≥ 0` and `Q⋆ ≤ 1/(1−γ) < ε ≤ 91√X`, so the event is the whole space.

  Here `card(S×A) = S·A` (`Fintype.card_prod`).
- **C = 91.** 91² = 8281 ≥ 8192, so √(8192X) ≤ 91√X. Correct.

## (5) Axioms and forbidden tokens

- **Independent rebuild.** Snapshot SHA256s match the builder's snapshot hash list, and the builder's live working files
  are byte-identical to the snapshot. I copied the snapshot to the reviewer's private probe folder; only
  the import lines differ (builder's working module prefix → reviewer's private prefix; diff-checked). I compiled the copies
  with `bash scripts/lean-local.sh -o <reviewer olean folder>/<X>.olean …`, foreground, one at a
  time:

  | Module | Exit | Time |
  |---|---|---|
  | Definitions | 0 | 17s |
  | Statement | 0 | 3s |
  | Coupling | 0 | 2s |
  | Lift | 0 | 2s |
  | Law | 0 | 2s |
  | Value | 0 | 1s |
  | LogCube | 0 | 54s |
  | Main | 0 | 52s |
  | StatementProof | 0 | 34s |
  | Thm46Unit | 0 | 6s |

  All diagnostics output was empty.
- **Axiom re-probe** (`CriticProbe.lean` and `CriticProbe2.lean` in the reviewer's private probe folder, both exit 0). The following all
  depend on `[propext, Classical.choice, Quot.sound]` only:
  - `Thm4_6_underestimation_holds`
  - `qLearning_underestimation_exists_universal_constants`
  - `…source_accuracy_unitWitness`
  - `tdSource_logCube_unitConstants_exactSamples_accuracy`
  - `qSamplingLaw_map_qPolicyLiftData`
  - `qPolicyLift_trajectoryExpectedValue_optimal`
  - `critic_Thm4_6_from_unit`
- **Forbidden-token scan** of the snapshot: no hits for `sorry`, `admit`, `axiom`, `native_decide`,
  `implemented_by`, `extern`, `unsafe`, `opaque`, `maxHeartbeats`/`debug` options, `ofReduceBool` or
  `trustCompiler`.
- **Not checked.** The integrated library build and `Audit.lean`, because integration has not happened. The
  probes assume the current `Formalization*` oleans match their sources.

## R-items (refutations)

None.

## F-items (integration requirements)

- **F1 (required).** In the same change, update `docs/ERRATA-AND-DEVIATIONS.md:52`. Theorem 4.6's
  witnesses become c₁ = c₂ = 1, with c₃ from `qFinal_exists_universal_budget_constant 1`, in
  `QLearningSourceTheoremClosure.lean`. Optionally also fix that item's locator "model-based lines 891–912"
  to model-free. Correct the DRAFTS-FOR-LEAD "grep checked" sentence in the lead's notes.
- **F2 (required).** Land the change atomically.
  - Include the `Thm46Unit` proof-body replacement, the `Thm4_6` docstring (DRAFTS), the `Remark4_2`
    docstring (DRAFTS) and the new entry together. The entry docstring's "the same witnesses as `Thm4_6`"
    is false otherwise.
  - Add the `COVERAGE.md` row and the `named-result-status.json` entry for `Thm4_6_underestimation` in the
    same change (AGENTS.md statement-index rule).
- **F3 (required).** Theorem 4.6's evidence link (`COVERAGE.md:106`, `named-result-status.json`
  `"evidence"`) points to a review of the old (1/4) proof body. Add this critic report as evidence for the
  (1,1) body.
- **F4 (optional).** Keep the (1/4,1/4) unconditional result as a separately named theorem, for example by
  moving the old body to `qLearning_source_accuracy_quarterWitness`. The index would then lose no
  certified instance. If not done, keep the "c₂ < 1 not covered" disclosure in the `Thm4_6` docstring as
  drafted.
- **F5 (after integration).** Run `python3 scripts/check.py` with the axiom audit. Rebuild downstream of
  `QLearningSamplingDefinitions` and `QLearningSourceTheoremClosure`. Confirm that the wrapper still closes
  by the defeq noted in (1); it is reducible-defeq, so this is expected.

## Ledger text (suggested)

> `Thm4_6_underestimation` (prose claim, `generative_model_model_free.tex:1869–1881`, display :1873–1879):
> proved for every T ≥ 2 without budget or A ≥ 2. Clause 1 Q̃_T ≤ Q_T is pathwise. Clause 2 gives, with
> probability ≥ 1−δ simultaneously for all (s,a), Q̃_T − Q⋆ ≥ −91·√(log⁴T·log(SAT/δ)/((1−γ)³T)). The
> schedule is Theorem 4.6's log³T class with witnesses c₁ = c₂ = 1, shared with `Thm4_6` and `Remark4_2`
> after the proof-body re-witness of `qLearning_exists_universal_constants_source_accuracy` (signature
> unchanged). Schedules with c₂ < 1 are not covered; this is a proof-infrastructure limit, not a source
> error. Independently reviewed: `docs/critic-underestimation.md` (ACCEPT WITH
> DISCLOSURES).

## Hashes (sha256)

| File | sha256 |
|---|---|
| source `generative_model_model_free.tex` | `7f4eb058e00480bc0694cac93ac41e22f4cfe48aa58a00c4ccf909f805e60b22` |
| builder's snapshot hash list | `acb324b5b1a9b9332ba579031baf077521c183ef459d72f9ecd50e659d966b6b` |
| builder's drafts for the lead | `f29290d756baed23b9f35acb3cc0e13e6c365ddee1b019ea1776a162875dfebc` |
| builder's status note | `7981a470c349a727fe3fb2b6d7668e8bd3a334d2be404faddaf675b1b6d88569` |
| builder's axiom-probe output | `7926aa0e0e4deee834d2c15f862dc741c00994f8654ecedddea8cd8a5a036aa9` |
| plan check (public copy: `critic-underestimation-plan-check.md`) | `4411df389dd7eef16227372bc6bd25e42bbec6c7542bf023b9173a5fcdccc9da` |
| `Formalization/Statements/Ch4.lean` | `12013d346edda00401ee0f701dca2b1b31e86da3dead61b86a4041fc591eec63` |
| `QLearningSourceTheoremClosure.lean` | `e622c6d175e3ed4e86df8938b450d60d6d44c9de6cbba89793803395f898c72a` |
| `docs/ERRATA-AND-DEVIATIONS.md` | `c9dbddb60f28d9e734f9281d8617cee3b81ecf1fef547fc4a5d1e4823e01a281` |
| reviewer `CriticProbe.lean` | `13a3d5417fa40ea9796e13b5d55f429a0f36413b50821de3f55b63c884074cec` |
| reviewer `CriticProbe2.lean` | `ae4592fb493c4e140f1e311771fff66a518964359278e78fe8339dde80d36cc8` |
| reviewer `CriticProbe.out` | `6664cab29b3a07daf5e84762f0c89518ade59ff4041e4236d4347d9452455fe9` |
| reviewer `CriticProbe2.out` | `3f9ac55bdd1e035eb35de6296c3f7e2581f24b2bf37547b336d27c801fbbd200` |

Snapshot module hashes are as listed in the builder's snapshot hash list; all ten were verified equal.
