# CRITIC P2 (Chapters 3–5): independent review

Public copy of the independent critic report; local paths removed.

Post-review note (added to this public copy, 2026-11-09): this critic reviewed the pre-integration drafts. They were integrated on 2026-11-09: the Chapter 3 entries into `Formalization/Statements/Ch3.lean` and `Ch3Proofs.lean`, the Chapter 4 entry into `Ch4.lean` and `Ch4Proofs.lean`, and the Chapter 5 entries into `Ch5.lean` and `Ch5Proofs.lean`. F1–F6 were applied before landing; the U11 scope disclosure is [C49](SOURCE-ISSUES.md#C49). F1 is docstring-only, so the `RegretDecompositionDisplay.lean` hash differs from the one quoted below. Two line citations in the F4 text were corrected on integration (Step 6's premise `N ≥ 64β₁/(1−γ)` is at `:622`, and `m = ⌈log(e/(1−γ))⌉` is at `:624`). The draft-file hash suffix in the hash list was mistyped in the private report and is given here as in the build log. Labels U10–U12 and O4 number the rows of the builder's draft; F-P2-n refers to the independent completion check. The review text below is otherwise unchanged.

Reviewer: independent critic (not the builder). Date 2026-11-09.
Brief: the completion plan, batch P2, as amended by the independent completion check (§2.3, §4, §5, findings F-P2-1…8, and its brief for P2).

## Overall verdict: **ACCEPT WITH FIXES**

All seven entries match their printed sources, as restricted or corrected where disclosed. All wrappers only apply library exports, with short algebraic bridging where the export is stronger. Everything compiles, and the axiom closure is exactly `propext, Classical.choice, Quot.sound`. No G2 statement-import edge is needed. The required fixes are citation, disclosure and integration items. None changes a Prop or a library signature.

## Files and hashes reviewed (sha256)

- `Formalization/Online/SourceOptimism/MonotoneBonusFunction.lean`: ec217fa4…354db3
- `Formalization/Generative/BurnInNecessity.lean`: 40e2a761…436597
- `Formalization/Online/Bandit/RegretDecompositionDisplay.lean`: c8d7c82f…2df23b
- `Formalization/ModelFree/QLearningSingleActionTD.lean`: 69648d1d…ce388
- the builder's pre-integration statement draft: b5de5954…1a1196c

These match the builder's build log. The `.olean` mtimes equal the source mtimes.

## Compile evidence (one Lean process at a time; `pgrep -x lean` < 2 checked before each run)

All runs used `bash scripts/lean-local.sh <file>`. The probe files are the critic's working files and are not published.

| Probe | Context | Result |
|---|---|---|
| each of the 4 new library modules (elaboration only, no `-o`) | own imports | no errors |
| `ProbeCh3Defs.lean` | **exactly** the 3 imports of `Statements/Ch3.lean`, its local instances (`statementFinMeasurable`, `statementStateMeasurable`, `statementStateDecidable`), and `open scoped Matrix in` on the U10 entry | exit 0 |
| `ProbeCh4Defs.lean` | **exactly** the 10 imports of `Statements/Ch4.lean` and its local measurable instances, `universe u v` | exit 0 |
| `ProbeCh5Defs.lean` | **exactly** the 26 imports of `Statements/Ch5.lean`, its local instances (measurable, Classical `DecidableEq`), `universe u v` then `universe w` | exit 0 |
| `ProbeAll.lean` (`ProbeAll.out`) | `import Formalization` plus the 4 new modules; all 7 entries and wrappers, with the ChN local instances replicated | exit 0; all 7 `_holds` and all 7 new library exports print `[propext, Classical.choice, Quot.sound]` |
| `ProbeO4Compose.lean` (`ProbeO4Compose.out`) | `Formalization` plus `QLearningSingleActionTD` | exit 0, same three axioms. Derives the A = 1 Q-learning `(1−γ)⁻³` guarantee from `Thm4_1_holds` + `qSampled_singleAction_event_eq` + `optimalQ_singleAction_eq_value` (see O4). |

`grep -nE 'sorry|admit|^\s*axiom|implemented_by|unsafe|native_decide'` over the 4 modules and the draft returns nothing.

Matrix inverse (U10): `Statements/Ch3.lean` already reaches `Matrix.inv` (Lemma3_6 uses `(1 - γ • P)⁻¹ *ᵥ`). `FiniteDistribution.variance` (Remark 5.9) is reachable from the Ch5 imports. The Ch4 objects (`qLearningIterate`, `tdIterate`, `qSampledIterate`, `tdSourceSampledIterate`, `trajectoryExpectedQ`, `optimalGreedyPolicy`) are all reachable from the Ch4 imports.

**G2 edges needed: none.**

## Per-entry verdicts

### `Ch3.Eqn_ice_cream`: ACCEPT
- Source MB:619–634. The label `eqn:ice-cream` is on the last line of the display (:626–630). The display's own premise `N ≥ β₁/(1−γ)` is at :633, `m = ⌈log(e/(1−γ))⌉` at :624/:634, and `β₁ = C₀ log(Sm/δ)` at :478/:634. "Exceeding 1−δ" is encoded as strict `1 − δ <`, and `0 < δ < 1` matches.
- "Large enough C₀" is encoded as `∃ C̄ > 0, ∀ C₀ ≥ C̄`, and the universal C̄ is chosen before the types and the MDP. Correct. `m` is inline, so it needs no G2 edge. The `valueEstimator`/`samplingLaw` are the `Ch3Definitions` ones: the wrapper is a bare `exact` of `policyEvaluation_source_radius_all_states_positive_samples` (C̄ = 8), so the objects are definitionally the same.
- **Stating only the final bound is acceptable. No `_restricted` is needed.** The label is attached to the final line. The middle expression `2√(8β₁/((1−γ)³N)) + 2β₁/((1−γ)²N)` is a proof step that the source derives under Step 6's stronger working premise `N ≥ 64β₁/(1−γ)` (:621). Under the printed premise `N ≥ β₁/(1−γ)` alone, the text justifies only the last inequality (2β₁/((1−γ)²N) ≤ √(8β₁/((1−γ)³N)) iff N ≥ β₁/(2(1−γ))). Stating the middle under :633 would therefore not be the printed claim either. See F4 for a recommended docstring sentence.

### `Ch3.Eq_lemma_VarP_V_bound`: ACCEPT (integration fix F3)
- Source MB:300–352: `eq:I-gamma-P-Var-bound` at :335–341 and `eq:lemma-VarP-V-bound` at :348–352. The final bounds of both chains are stated, with the standard matrix inverse and entrywise `0 ≤ …`.
- U10's domain condition `0 < γ` is justified. The book has γ ∈ [0,1) (prelim.tex:45), but the printed bounds divide by γ and are undefined at γ = 0. With Lean's `x/0 = 0`, the γ = 0 instance would be false, since R = I and Var ≠ 0 in general. So this is a domain condition, not a source issue.
- The wrapper derives the result from `evaluationPolicyResolvent_variance_bound` and `_sqrtVariance_bound`. Both exports are stronger (no factor 2 and no √2). The bridging is ≤ 20 lines of algebra and does not reprove the result. An arbitrary `DecidableEq` instance is handled by `Subsingleton.elim`, and this was tested with Ch3's Classical local instance active.

### `Ch3.Thm3_2_burnInNecessary_restricted`: ACCEPT (fix F2)
- Source MB:930–940; the claim is at :939. "Strictly better than a random guess" is undefined, so `_restricted` is correct (completion-check correction 3, R-U11).
- R-U11 items:
  1. Name: correct.
  2. Metric: the book's `‖V⋆ − V^{π̂}‖∞`. The Q→V transfer `‖Q^π − Q^{π'}‖ ≤ γ‖V^π − V^{π'}‖ ≤ ‖V^π − V^{π'}‖` is in the library (`trajectoryExpectedQ_sub_norm_le`, `lt_value_gap_of_lt_Q_gap`).
  3. Deterministic estimators, S ≥ 2, A ≥ 2, SA ≥ 16, γ ≥ 2/3: disclosed in the docstring.
  4. ε = 1/(64(1−γ)) < 1/(32(1−γ)): yes.
  5. SOURCE-ISSUES pointer: **missing** in the draft ("to be added by the lead"); see F2. (Applied: [C49](SOURCE-ISSUES.md#C49).)
- Quantifiers: the universal c (= 1/8) comes first. Then S, A, N, γ, then the estimator, then the witness MDP. The estimator is given the true reward and discount, which only strengthens the lower bound. Failure probability ≥ 1/4 means success ≤ 3/4. The non-vacuity example compiles.
- **V⋆ via `optimalGreedyPolicy` is tie-independent.** `trajectoryValue_le_optimalGreedy` shows that the greedy value dominates every stationary randomized policy pointwise. So any other optimal deterministic f (any tie rule) has value ≤ the greedy value and ≥ it (by f's optimality), hence equal. This is machine-checked in `ProbeAll.lean` (critic example: if f dominates every π, then V^f = V^{greedy}). V⋆ therefore equals the unique optimal value function.

### `Eqn_regret_decomposition_ucb` (Ch5): ACCEPT (fix F1)
- Source BD:58–82: regret `eq:regret_bandit` at :66–69, the non-negativity sentence at **:72**, and the decomposition at :78–82. Pathwise for any arm sequence, with `0 ≤ Regret(T)` included (F-P2-5). This is correct: the book itself says Regret is a random variable, a function of the realized `a_t`. `r⋆ = ⨆ r` is the max over a finite type. The `r ∈ [0,1]` setting is correctly noted as unused.
- The wrapper is a bare application of `Bandit.regret_decomposition`.

### `Remark5_9` (Ch5): ACCEPT (coverage wording F5)
- Source ON:1330–1332 (remark), cited first as required by F-P2-1, then :3299–3311 (definition of f and `eq:nondecreasing-f-property`) and the proof at :3392–3433. Domain: p a probability vector, 0 ≤ v ≤ H, positive integer n, δ′ ∈ (0,1]. Including δ′ = 1 is a harmless generalization. The second conjunct is the printed "non-decreasing in each entry" on the box; the first conjunct is the stronger vector order.
- **Monotonicity for every real c₁, re-derived.** Write L = log(1/δ′)/n ≥ 0.
  - *c₁ ≤ 0:* `c₁√(Var·L) ≤ 0 ≤ c₁²HL`. Here H ≥ 0 whenever the box is nonempty, and Ω is nonempty because p exists. So the max is the constant c₁²HL, and f = ⟨p,·⟩ + const is monotone.
  - *c₁ > 0:* with a = c₁√L and θ = c₁H√L, f(v) = ⟨p,v⟩ + a·max(√Var(v), θ). Lemma A gives Var(v) − Var(w) ≤ 2H⟨p, w − v⟩. If both √Var(v), √Var(w) ≥ θ, then a(√Var v − √Var w) ≤ a·2H⟨p,d⟩/(2θ) = ⟨p,d⟩. If Var(v) ≤ θ², monotonicity follows trivially from ⟨p,·⟩. In the mixed case, the IVT on the segment gives x* with √Var(x*) = θ.
  - This is the §2.3 route, and the library (`monotoneBonusFunction_mono`, `_update_mono`) implements it with hypotheses `0 ≤ ι` and `0 < n` only. No `0 < c₁` or `0 ≤ H` is assumed.
- The wrapper only discharges `0 ≤ log(1/δ′)` and the cast of n.

### `Remark5_13_corrected` (Ch5): ACCEPT
- Source ON:3512–3524, with the T₆ definitions at :879–893. **[C8](SOURCE-ISSUES.md#C8) identification confirmed against the definitions:**
  - `onlineActualT6UCB` = Σ_h Σ_k Var under the true row `(E h).transition` at the visited pair `(s_h^k, a_h^k)` (`onlineActualStageRowSequence`) of `onlineActualOptimisticContinuation` (the capped backward value at stage h+1 of the pre-episode planning stages = V^k_{h+1});
  - `onlineActualT6Policy` = the same row's variance of `onlineActualPolicyContinuation` (the trajectory value of π^k from stage h+1 = V^{π^k}_{h+1});
  - `onlineActualT6Difference` = ⟨P, (V^k_{h+1} − V^{π^k}_{h+1})²⟩.
- `_corrected` is appropriate because V^k is the zero-count completion ([C8](SOURCE-ISSUES.md#C8)). The inequalities are unchanged and deterministic.
- The √ conjunct is derived with `0 ≤ T6Policy` and `0 ≤ T6Difference` *proved* (sum of variances, sum of expectations of squares), as F-P2-7 requires.

### `Ch4.QLearning_singleAction_eq_TD` (O4): ACCEPT
- Synchronous Q-learning (`qLearningIterate`: Algorithm `alg:q-infinite`'s update with max over actions) at the single action equals `tdIterate` with the same samples:
  - (i) pathwise, by induction, using max over one action = value at a, `policyReward` = r(s,a), and `policyTransition` = P(·|s,a);
  - (ii) in law, for every set B, because dropping the action coordinate pushes the product sampling law `qSamplingLaw` onto `tdSourceSamplingLaw` (`measurePreserving_piCongrLeft` plus a row identity);
  - (iii) Q⋆(s,a) = V^π(s), with π the unique policy.
- These are the same objects used by `Thm4_1` (`tdSourceSamplingLaw`/`tdSourceSampledIterate`) and by `Thm4_6`/`Thm4_7` (`qSamplingLaw`/`qSampledIterate`/`trajectoryExpectedQ optimalGreedyPolicy`).
- **Remark 4.5 can now be closed as implied.**
  - Sentences 1–2 are already proved (`Remark4_5`).
  - Sentence 3 ("This distinction gives rise to a fundamental difference in sample complexity between the cases A=1 and A≥2, leading respectively to the horizon dependency (1−γ)⁻³ and (1−γ)⁻⁴", MF:3456): the A = 1 side is `QLearning_singleAction_eq_TD` + `Thm4_1`. The critic machine-checked this composition (`CriticP2.singleAction_qLearning_TDrate`: with one action, Q-learning reaches sup error ε w.p. ≥ 1−δ once T ≳ log³T·log(ST/δ)/((1−γ)³ε²)). The A ≥ 2 side is `Thm4_6` (upper, (1−γ)⁻⁴) and `Thm4_7`/`Thm4_7_case_i` (lower, (1−γ)⁻⁴).
  - The two sides are comparable on a common schedule. A constant rate η ≡ 1/(1 + c(1−γ)T/log²T) with c ∈ [c₂, c₁] lies in Thm4_1's window, and Thm4_7 covers every constant η₀ ∈ (0,1).
  - Disclosures for the node text:
    - the A = 1 rate is an upper bound (the sentence needs no A = 1 lower bound);
    - the metrics differ: a high-probability sup error (Thm4_1/4_6) versus a mean-square lower bound on V_T (Thm4_7);
    - "gives rise to" is causal and explanatory.

## Required fixes

- **F1 (U12 citation).** In the draft docstring of `Eqn_regret_decomposition_ucb`, replace `"ensures non-negativity of regret" \`:70\`` with `` `:72` ``. Also replace `regret \`:66–68\`` with `` `:66–69` ``. In the library module docstring of `RegretDecompositionDisplay.lean`, replace `` `Regret(T) ≥ 0` (`:66–67`, `` with `` `Regret(T) ≥ 0` (`:72`, ``. Line facts: `\label{eq:regret_bandit}` is at bandits.tex:67 and the "ensures non-negativity" sentence is at :72.
- **F2 (U11 disclosure anchor).** Before landing:
  1. Add the SOURCE-ISSUES scope-disclosure entry at the next free C-id with an `id="C49"` anchor.
  2. Replace "See `docs/SOURCE-ISSUES.md` (scope disclosure for this entry, to be added by the lead)" in the docstring with "See `docs/SOURCE-ISSUES.md#C49`", so that G3's C-id check covers it.
  3. Use this disclosure text, which extends the DRAFT-docs text: "`Thm3_2_burnInNecessary_restricted`: the book's 'strictly better than a random guess' (MB:939) is undefined. The entry reads it as failure probability ≥ 1/4 of value gap ‖V⋆ − V^{π̂}‖∞ > 1/(64(1−γ)) when N ≤ log(SA)/(8(1−γ)); accuracies between 1/(64(1−γ)) and 1/(1−γ) are not covered. Restrictions inherited from Thm3_7_corrected: S ≥ 2, A ≥ 2, SA ≥ 16, γ ∈ [2/3,1), deterministic (non-randomized) learners returning deterministic policies (the learner is also given the true rewards and discount, which only strengthens the bound). V⋆ is the optimal value (greedy-policy value; tie-independent). Q-to-V transfer: ‖Q^π − Q^{π'}‖ ≤ γ‖V^π − V^{π'}‖."
- **F3 (integration; the Props are unchanged).**
  1. In `Statements/Ch3.lean`, put `open scoped Matrix in` on the line **before the docstring** of `Eq_lemma_VarP_V_bound` (`*ᵥ` is scoped notation; the draft opened it globally). Put the same before `theorem Eq_lemma_VarP_V_bound_holds` in `Ch3Proofs.lean`, which opens only `MeasureTheory`.
  2. Do not redeclare `universe u v` in `Ch4.lean`, `Ch4Proofs.lean` or `Ch5.lean` (they already declare them). Add only `universe w` in `Ch5.lean` before `Remark5_13_corrected`. `Ch5Proofs.lean` declares no universes; add `universe u v w` there if auto-bound universes are off.
  3. Imports to add: in `Formalization.lean`, the 4 new modules. In `Ch3Proofs`, `Generative.BurnInNecessity`, `Generative.PolicyEvaluationGapRepairAllStates` and `Generative.PolicyEvaluationVarianceResolvent` (if not already transitive). In `Ch5Proofs`, `Online.SourceOptimism.MonotoneBonusFunction`, `Online.Bandit.RegretDecompositionDisplay` and `Online.Regret.T3.OnlineRegretT3SourceBound`. In `Ch4Proofs`, `ModelFree.QLearningSingleActionTD`.
  4. No G2 statement-import edge is needed (verified by the exact-import probes).
- **F4 (ice-cream docstring; recommended, not blocking).** Replace "The printed display is a chain whose middle expression … is a proof step; this entry states the final bound." with "The printed display is a chain; its middle expression `2√(8β₁/((1−γ)³N)) + 2β₁/((1−γ)²N)` is a proof step derived under Step 6's working premise `N ≥ 64β₁/(1−γ)` (`:621`), and this entry states the labelled final bound under the display's own premise."
- **F5 (Remark 5.9 COVERAGE wording).** Replace "Attribution sentences: explanatory" with: "Sentence 1 (name coined by zhang2020) is attribution. Sentence 3 (the property is built into Algorithm `alg:main-ucbvi`'s bonus `eq:bh-defn-Bernstein-ucbvi`, unlike azar2017) is a design remark: the property is consumed in the proof of `lemma:opt` (`:3353`), and the comparison with azar2017 is cited (see Remark `remark:different-bonus-than-Azar`)."
- **F6 (Remark 4.5 node).** Close it only with the text given under "COVERAGE text approval" below. Do not describe sentence 3 as a single formal theorem.

## COVERAGE text approval

Approved as drafted in the builder's draft coverage text, with these edits:

- **ice-cream:** approved.
- **U10:** approved. Rephrase "Export is stronger (no sqrt 2)" as "export is stronger by a factor 2 (variance) and √2 (√-variance)".
- **U11:** approved as **restricted**, with the F2 anchor and text.
- **U12:** approved with the F1 line fix (non-negativity :72).
- **Remark 5.13:** approved (corrected, [C8](SOURCE-ISSUES.md#C8)).
- **Remark 5.9:** approved with the F5 wording.
- **Remark 4.5 (replace the current partial row headline):** "**Proved/implied.** Sentences 1–2 proved (`Remark4_5`). Sentence 3 is implied:
  - A = 1: single-action synchronous Q-learning equals TD pathwise and in law, with Q⋆ = V^π (`QLearning_singleAction_eq_TD`), so `Thm4_1` gives the (1−γ)⁻³ upper rate.
  - A ≥ 2: `Thm4_6` (upper) and `Thm4_7` (lower) give (1−γ)⁻⁴.
  - Constant rates in Thm 4.1's window are covered by Thm 4.7's constant-rate family.
  - The A = 1 rate is an upper bound, and the metrics differ (high-probability sup error vs mean-square lower bound). The causal phrasing is explanatory."
- **O4 row:** approved.
- **#26 `eq:Vk-Itrue`:** not built (optional, completion-check correction 6); its status is unchanged.
