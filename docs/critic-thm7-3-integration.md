# CRITIC (integration): corrected Theorem 7.3 (`thm:l1-lower-bound`, `robust_RL.tex:377–391`, C38)

Public copy of the independent critic report; local paths removed.

Post-review note (added to this public copy, 2026-11-07): required edits E1–E4 of this review were applied on 2026-11-07. The review text below is unchanged.

Critic: independent (did not build). Date 2026-11-07. Scope: the library integration of the
critic-accepted WIP (`docs/critic-thm7-3-corrected.md`, `docs/critic-thm7-3-corrected-delta.md`) and the
new known-reward entry.

## Verdicts

| entry | verdict |
|---|---|
| `Statements.Ch7.Thm7_3_corrected` / `Thm7_3_corrected_holds` | **ACCEPT** (disclosures are already in place) |
| `Statements.Ch7.Thm7_3_corrected_knownReward` / `Thm7_3_corrected_knownReward_holds` | **ACCEPT WITH MINOR EDITS** (wording only, non-blocking) |
| Library move `Thm73Wip.*` → `Formalization/RobustRL/Ch7/LowerBound73*.lean` | **ACCEPT** (no semantic change) |
| `Ch7PrintedStatements.lean` additions, `Formalization.lean` imports | **ACCEPT** |

## Inputs (sha256)

| file | sha256 |
|---|---|
| Formalization/RobustRL/Ch7/Ch7PrintedStatements.lean | 9657afc4d12ced2d58c5463f9530cfe53336fb7c325f9fec1ded67a7ef155581 |
| Formalization/RobustRL/Ch7/LowerBound73Values.lean | e7477af8afe15d8f67a73525a14bb03518330ae24c31e334bf424d6b512a868b |
| Formalization/RobustRL/Ch7/LowerBound73Testing.lean | 2c8a032b082d7f057d8fd35ca03e2d6c930630fb793d2a74b0043b6296a46116 |
| Formalization/RobustRL/Ch7/LowerBound73SingleState.lean | d7598c0d44a6205bd089bcc7a26bc2321962e5e4b9c7d1d82ae134227fb38e40 |
| Formalization/RobustRL/Ch7/LowerBound73.lean | 96bfdc6c85ad341457edc410005c72716fc4279f3f548a3b513134402989c23d |
| Formalization/Statements/Ch7.lean | 3f83eebd862844cfe652ee75ca0c3e2543dfb67235586534f0cb7843d7f244fb |
| Formalization/Statements/Ch7Proofs.lean | f82e7299a8d95efe57c40c072f34f1ffda967ff8650672d921b83b27f80bb00e |
| <builder working folder>/IntegrationProbe.lean | 07475f93124a782493aa99af411f878831fe6162f1a5573e60642d438ec047f3 |
| <builder working folder>/integration-probe.out | 80179bab21496202ea6e91175389759f815df4abc0b83e7312de8d047da9eb49 |
| WIP Values / Testing / SingleState / LowerBound | 1192c530… / 18b33d9c… / 9675a761… / 0cdbeff8… (all match the delta review) |
| <reviewer probe folder>/CriticIntegrationProbe.lean (critic) | 08d57157dbdd92eb4b4c333ed068cbd60691bf343e653b2d27bbfe7651a50dc5 |
| <reviewer probe folder>/critic-probe.out (critic) | d131ae1d0d071cf3a2c1f912ea589fa419e68cf09d974879067c7cf7cc755200 |

## Checks performed (repo root, foreground, one at a time, no `-o`, no lake, no lean-lsp)

1. **Olean freshness.** For each of the 7 integrated sources, the `.lake/build` olean mtime
   (09:23–09:25) is later than the source mtime (09:19–09:20). `Formalization.olean` is at 09:26.
2. **Builder probe re-run.** `bash scripts/lean-local.sh <builder working folder>/IntegrationProbe.lean`
   exited 0 in 53s. Its output (`<reviewer probe folder>/integration-probe.rerun.out`) is byte-identical
   to `integration-probe.out`. All 8 `#print axioms` lines show `[propext, Classical.choice, Quot.sound]`.
3. **Mechanical statement diff (critic).** `awk` extracted the body of `Thm7_3_printed_at` into
   `B_printed.txt`. The expected bodies were then generated mechanically:
   * known-reward: insert `2 ≤ Fintype.card State → 2 ≤ Fintype.card Action →` as line 3, and
     replace `M₀.discount = γ ∧ M₁.discount = γ ∧` by `… ∧ M₀.reward = M₁.reward ∧`;
   * corrected: insert `2 ≤ Fintype.card Action →` as line 3;
   * index forms: prepend `∀ c₀ : ℝ, 0 < c₀ → c₀ ≤ 1 / 8 →`.

   `diff B_printed B_kr_expected` shows exactly those two hunks. The generated bodies are
   **textually identical** to the four actual bodies: library `_at` defs in
   `Ch7PrintedStatements.lean`, and both entries in `Statements/Ch7.lean`.
4. **Critic probe** (`bash scripts/lean-local.sh <reviewer probe folder>/CriticIntegrationProbe.lean`,
   exit 0, 70s). The probe's right-hand sides are pasted verbatim from the generated files. It contains:
   * `rfl` probes for `Thm7_3_printed_at`, `Thm7_3_corrected_at`, `Thm7_3_corrected_knownReward_at`,
     `Statements.Ch7.Thm7_3_corrected` and `Statements.Ch7.Thm7_3_corrected_knownReward` against
     the generated text. This closes the gap between the textual diff and the elaborated terms.
   * `rfl` checks that `Thm7_3_corrected_holds = LowerBound73.thm7_3_corrected` and
     `Thm7_3_corrected_knownReward_holds = LowerBound73.thm7_3_corrected_knownReward`.
   * `critic2_rewardAware`: from the index entry, every reward-aware estimator
     `est' : (State → Action → ℝ) → Samples → Policy`, evaluated at the true model's reward
     (`est' M_i.reward data`), satisfies the same `1/8` bound (see Finding 1).
   * `critic2_kr_instance`: non-vacuity of the known-reward entry at `Fin 2 × Fin 2`,
     `c₀ = 1/8`, `γ = σ = 1/2`, `ε = 1/1024` (the upper endpoint), `N = 0`.
   * `#print axioms` for 12 declarations, including `lb_two_states_knownReward`,
     `lb_two_states`, `lb_one_state` and both wrappers. Every one shows
     `[propext, Classical.choice, Quot.sound]`.
5. **WIP → library diff.**
   * `Values`, `Testing`, `SingleState`: the only changes are the namespace
     (`Thm73Wip` → `StatisticalRL.RobustRL.Ch7.LowerBound73`), import paths, and dropping "(WIP)"
     from headers.
   * `LowerBound`:
     * `lb_two_states` is renamed `lb_two_states_knownReward`, and its conclusion `LBConclusion`
       becomes `LBConclusionKR`, which adds `M₀.reward = M₁.reward`.
     * The only proof change is one extra `rfl` in the anonymous constructor. The hardMDP reward
       `if s = s₀ then 0 else 1` does not depend on `g`.
     * A new `lb_two_states` (same signature as the WIP version) projects away the reward conjunct.
     * A new `thm7_3_corrected_knownReward` applies `lb_two_states_knownReward` directly.
     * `thm7_3_corrected` is unchanged.
   * `Statement.lean` is folded into `Ch7PrintedStatements.lean`. Its body is unchanged (Check 3),
     and the docstrings are improved.
6. **Forbidden tokens and paths.** `grep` for
   `sorry|admit|axiom|native_decide|implemented_by|extern|unsafe|set_option|Thm73Wip|WIP` together with the local path patterns (home-directory prefix, project folder name, private working folder)
   over the 7 integrated files finds no hits.
7. **Source line citations** were checked against `source/upstream/tex/chapters`:
   * `robust_RL.tex:377–391` is exactly `\begin{theorem}…\end{theorem}`, and `:379` is the c₀ clause.
   * `:135–147` is the sampling mechanism. `:19–157` covers the RMDP, robust value and sampling paragraphs.
   * `:25` is the reward clause of the RMDP tuple (the tuple itself is at `:23`).
   * `generative_model_model_based.tex:31` is "we assume throughout that the reward function is
     fully known".
   * `:206–212` is the empirical-kernel paragraph. The empirical RMDP that reuses `r` is at
     `:213–215` (Finding 3).

## Question (1): is the shared-reward conjunct the faithful encoding of "the reward is known"?

**Yes, and it is at least as strong as the faithful reading.**

* **Quantifier order.** In `∃ M₀ M₁ μ, … ∀ est, …`, `est` is chosen after the pair. An estimator
  may therefore hard-code anything common to both models. This is the usual two-point minimax
  convention: the learner knows the hypothesis pair but not which member generated the data.
  With `M₀.reward = M₁.reward`, the common reward is part of that shared knowledge. Every
  "knows-the-reward" estimator, i.e. `est' r` with `r` the true reward, is an instance of `est`.
  `critic2_rewardAware` checks this in Lean.
* **Shared reward versus differing rewards.** Under the known-reward convention, two models with
  different rewards would let a reward-aware estimator identify the model with no data. The
  faithful known-reward minimax claim is therefore
  `∃ M₀ M₁ μ, ∀ est' : Reward → Samples → Policy, bound with est' (M_i.reward)`.
  The entry implies this claim (`critic2_rewardAware`) and is formally stronger, because it also
  forces equal rewards. Concluding more than the printed reading is allowed (AGENTS.md
  "Statement index").
* **Nothing else is needed.**
  * The data are generated from the nominal kernel only (`samplingLaw` = product of the nominal
    rows over `(S×A)×Fin N`, `:135–147`). Samples carry no reward information, matching the book.
  * `S`, `A`, `γ`, `σ` are fixed before `est`.
  * The rewards lie in `[0,1]` by the `DiscountedMDP` structure.
  * The uncertainty set is the `(s,a)`-rectangular TV ball around the nominal kernel, as before.
  * The remaining gap is unchanged from the first review (Finding 3 there): estimators are
    deterministic maps to stationary policies. External randomization extends by averaging,
    which is a paper remark only.
* **The proof is genuine.** `lb_two_states_knownReward` is the reviewed `S ≥ 2` construction,
  plus a `rfl` for the reward conjunct. `hardMDP`'s reward does not depend on the good action, so
  both models share it, and they differ only in the nominal rows at `(s₀,a₀)` and `(s₀,a₁)`.
  The wrapper is a direct application, and the axioms are clean.
* **Necessity of the added hypotheses under the known-reward reading.**
  * `A = 1`: `SingletonAction73` refutes the printed statement at `S = 2, A = 1`. The known-reward
    conclusion implies the printed conclusion, so the refutation transfers. The transfer is a
    one-line implication, not stated in Lean.
  * `S = 1`: a reward-aware estimator plays `argmax r`. On one state every kernel is the point
    mass, so the gap is 0 in both models and the probability is `0 < 1/8`. This is a paper
    argument and is **not Lean-checked**.

## Findings

1. **Info.** The known-reward entry is faithful, and in fact stronger than the reward-aware reading
   (Question 1). The docstrings call it "the faithful reading". Recommended addition: "it implies
   the bound for estimators that are given the true reward".
2. **Low (unchecked claim in docstrings).** Three places claim that `S ≥ 2` is needed, or that
   the printed claim is false at `S = 1`, under known rewards:
   * the `Statements/Ch7.lean` known-reward docstring ("`S = 1` is degenerate under known rewards"),
   * the `Ch7PrintedStatements.lean` known-reward docstring ("`S = 1` is degenerate, C38"),
   * C38 ("the printed claim is false at S = 1").

   This rests on the paper argument above and has no Lean evidence. Add "(paper argument; not
   machine-checked)". The delta review also asked to say "false" rather than "degenerate", and
   the two known-reward docstrings still say "degenerate". Similarly, "`A = 1` is refuted in Lean"
   refers to the printed Prop. Say "refuted for the printed statement, which the known-reward
   conclusion implies".
3. **Low (citation precision).** Both entries cite `robust_RL.tex:206–212` for the empirical RMDP
   that reuses the true `r`, but that display is at `:213–215`. Use `:206–215`. Optionally cite
   `:23–25` instead of `:25` for the RMDP tuple.
4. **Low (instance hygiene).** `Statements/Ch7.lean:128` adds
   `local instance ch7StatementStateMeasurable (State : Type*) : MeasurableSpace State := ⊤`
   at file scope. It is harmless today, because only the two new entries follow it before `end`.
   But any later entry appended to this file would see a ⊤ σ-algebra on *every* type, including
   `ℝ`, which creates an instance diamond with Borel. Wrap the two entries and the instance in a
   `section … end`.
5. **Info (C38 text).** `docs/SOURCE-ISSUES.md:1060–1061` still says the proposed correction
   "does not prove the cited bound", and line 1066 then reports the proof. Mark the earlier
   sentence as historical, or reword it. "Both passed independent reviews" at `:1069` is accurate
   once this review is recorded. "Not author-approved" is retained (good).
6. **Info.** The builder's `IntegrationProbe` right-hand sides were typed by hand. Their
   agreement with the source text is now confirmed mechanically by Checks 3–4.

## Required edits

None blocking. Recommended (wording only; no Lean semantics change):
* E1 (Finding 2): add "(paper argument; not machine-checked)" to the `S = 1` necessity/falsity
  claims in both known-reward docstrings and C38. Replace "degenerate" with "false (the gap is 0
  for `argmax r`)".
* E2 (Finding 3): change the `robust_RL.tex:206–212` citations to `:206–215`.
* E3 (Finding 4): scope the `ch7StatementStateMeasurable` local instance with `section … end`
  in `Statements/Ch7.lean`.
* E4 (Finding 5): reword the stale C38 sentence.

After E1–E3, rerun `bash scripts/lean-local.sh` on `Formalization/Statements/Ch7.lean`,
`Formalization/Statements/Ch7Proofs.lean` and the critic probe, or run `python3 scripts/check.py`.
