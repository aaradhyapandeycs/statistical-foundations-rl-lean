# CHECK: small batch 2 plan (items a, b, d1, d2; c commented only)

Public copy of the independent plan check; local paths removed. The plan checked here is the builder's private plan; it is not published.

Post-review note (added to this public copy, 2026-11-08): item (a) was then built and independently reviewed in `critic-thm3-9-any-tie.md`, and items (b), (d1) and (d2) in `critic-small-batch-2a.md`; both reviews covered the pre-integration snapshot. Items (b), (d1) and (d2) were integrated into the library on 2026-11-08 (imports-only changes plus the critic's F1–F3 docstring fixes); item (a) was integrated into the library on 2026-11-08 (imports-only changes plus the F2/F3 docstring fixes). Item (c) remains planned, not built. `TRIAGE` refers to the lead's private work list, which is not published. The check text below is otherwise unchanged.

Date: 2026-11-08. Independent plan check, critic stance. No Lean or lake was run, nothing under
`Formalization/` was edited, and no paper was fetched. Only repository files were read, by grep and sed.

- Plan checked: the builder's private plan (not published),
  sha256 `c582baf33d69c997dee4c2bec22cb4a421a34f78d43f8a2474bf46271c82cfb9`. Verified, matches the brief.
- Source hashes recomputed. They match the plan and `source/provenance.json`: MB `b7e7abfb…4ac4d`,
  ON `393a4d26…c8c53`, P `2d27bb72…031a5`, MF `7f4eb058…60b22`.
- Anchors confirmed: `Thm:sample-compl-finite` label at MB:2552 (statement 2551–2570).
  `eq:N-UB-test-lower-Q-generative-overall` at MB:1546. `eq:P-Mi-Q-inaccurate-lower-generative` at
  MB:1555. Trigger `line:trigger-set-mvp` at ON:1280. `lem:sum-inv-Nhk-mvp` at ON:1571.
  `alg:main-fixed-profile` begins at ON:4419. `eq:X-I-ours` at ON:4449. `eq:Vk-Itrue` at ON:4472.
  Optimal deterministic policy at P:738–739.

## Verdicts

| Item | Verdict |
|---|---|
| (a) Thm 3.9 for any empirical-optimal policy | **GO WITH FIXES** |
| (b) `Eq_P_Mi_Q_inaccurate_lower_generative` | **GO WITH FIXES** (docs only) |
| (d1) C13 literal-trigger witness | **GO** (docstring notes) |
| (d2) C17 terminal-H witness | **GO WITH FIXES** (generality of the auxiliary lemma) |
| (c) | Deferral is reasonable; brief comment at the end |

---

## (a) Theorem 3.9, any tie rule

### Reading (open question 1)

I agree with "optimal at every stage and every state". P:738 says some deterministic policy maximizes
V and Q at every (s,a,h) simultaneously. P:739 then fixes π⋆ as "an optimal deterministic policy" in
that sense. The theorem's own conclusion is quantified ∀(s,h), and MB:2549 says the planner is
computed by backward induction from h=H, which gives optimality at every suffix.

I independently confirmed that the "optimal from stage 1 only" reading makes the printed claim false.
Take a stage-2 state s′ with P₁(s′|s,a)=0 for all (s,a). It is then empirically unreachable almost
surely. Let s′ have one action with reward 1 and another with reward 0, and take ε<1≤H. A policy that
is optimal only from stage 1 may pick the bad action at s′. Then V₂⋆(s′) − V₂^f(s′) = 1 > ε with
probability 1.

### Worst-tie reduction: checked

1. **Causality (W4).** `worstActions pairs` at index h+1+k depends only on `pairs.drop (h+1)`, by
   (W1). The true stages in `pairs` are data-free. `pairedEmpiricalStages_drop_eq_of_future_eq` exists
   (FiniteHorizonAuxiliaryVariance.lean:189) and has exactly the needed shape.
   - The existing `fittedTrueAuxiliaryContinuation_factors_future` (FittedAuxiliaryContinuation.lean:67)
     uses only `backwardGreedyActions_drop` and `empiricalStages_drop_eq_of_future_eq`. The planner
     swap is therefore mechanical.
   - The planner reads the true model E, which the algorithm cannot. This is legitimate: it is an
     analysis device, not the algorithm. The docstring and COVERAGE text must say so.
2. **Empirical optimality at every suffix (W2).** By induction, V̂^w(s) = F.qBackup(V̂^w_tail)(s,w₀s).
   This equals F.qBackup(V̂⋆_tail)(s,w₀s) by the induction hypothesis, and that equals V̂⋆(s) because
   w₀s ∈ Â(s). Â(s) is nonempty because `greedyAction` belongs to it. Correct.
3. **Domination (W3), checked for all h and s.** Let f′ be SuffixOptimal on the empirical stages.
   - Suffix optimality at n and n+1 gives V̂^{f′}(s) = F.qBackup(V̂⋆_tail)(s,f′₀s) = V̂⋆(s), so f′₀s ∈ Â(s).
   - Then V^{f′}(s) = E.qBackup(V^{f′}_tail)(s,f′₀s). This is ≥ E.qBackup(V^w_tail)(s,f′₀s) by the
     induction hypothesis and monotonicity of the expectation.
   - That is ≥ min_{a∈Â(s)} E.qBackup(V^w_tail)(s,a) = V^w(s).
   - Applying this to `pairs.drop h` with `f′(h+·)` gives V⋆_h − V^{f′}_h ≤ V⋆_h − V^w_h for every
     h and s. **The claim is genuinely true.**
   - Q follows from the V bounds at every h through `policyTrajectoryQSuffix_loss_le_of_values`
     (PolicyPerformanceConsumption.lean:31). It needs the V bound for all h, which domination
     supplies at every suffix.
4. **Pipeline reuse.** `allLevelBernsteinEvent_policyEvaluation` (PolicyEvaluationConsumption.lean:37)
   uses the planner only through `sourceAuxiliaryPolicy` (BernsteinResidualBridge.lean:87–91). It
   consumes the event through `allLevelBernsteinEvent_implies_residual`, which works for any
   data-selected current action.
   - The only planner-specific facts are factors-future (Bernstein independence) and, in
     `allLevelBernsteinEvent_policyPerformance`, the identity `backwardGreedyActions_policyTrajectorySuffix`
     (empirical value = empirical optimum). The `optimal` field replaces that identity.
   - So the statistical pipeline applies unchanged to w once it is parametrized by a `SuffixPlanner`.
   - Assembly: on the w-event, V⋆ − V^w ≤ 2r, and domination gives V⋆ − V^{f′} ≤ 2r for every
     empirically optimal f′. No union over tie rules is needed. The event does not depend on f′, so
     placing `∀ f` inside the set is sound.
5. **H=1 branch.** For every f, the true value equals the empirical value
   (`oneStage_policyTrajectorySuffix_eq`, FiniteHorizonOneStage.lean:26, arbitrary f). That equals
   V̂⋆, which is ≥ V̂^{fixed} = V^{fixed} = V⋆. So the loss is ≤ 0. Correct.

### Required fixes

- **F-a1 (ledger honesty).** Repointing only `lean_statement` is not enough. In
  `docs/named-result-status.json`, the record "Theorem 3.9" (lines 143–153) must also change:
  - `lean_export`: from `exists_universal_causalFinitePolicy_sample_constant` to the new any-tie export.
  - `lean_statement_proof`: to `Thm3_9_positiveN_holds`.
  - `evidence`: to the new critic report. The old `critic-finite-horizon-source-theorem.md` does not
    review the domination argument.
  - `statement_scope`: still "restricted" because of N>0, with the tie-rule clause removed. Follow the
    style of the Lemma 3.6 record ("every empirically optimal deterministic policy (no tie rule fixed)").
- **F-a2 (old entry).** Keep `Thm3_9_causal_positiveN` (answer to open question 3). Its docstring
  should name `Thm3_9_positiveN` as the general result, and COVERAGE must still mention it, so G3 sees
  it referenced. The COVERAGE row text "not arbitrary globally selected data-dependent optimal ties"
  must be rewritten. The SOURCE-ISSUES scope paragraph (around line 471) must keep the N>0 disclosure
  and record the retained causal special case.
- **F-a3 (docstring).** State that the proof route differs from the source. The source decouples via
  causality of its planner (MB:2549). The Lean proof covers non-causal or data-dependent ties through
  domination by a causal worst-tie planner. This is a proof-route note, not a SOURCE-ISSUES entry.
  - Optional: say that N>0 loses no content. For N=0 the printed threshold forces log(HSA/δ) ≤ 0, so
    δ ≥ HSA ≥ 1, where the claim is trivial; for an empty State every event is the whole space. Here
    `hN` is a typing necessity of `empiricalStages`.
- **F-a4 (proof detail).**
  - The `[]` case of `worstActions` needs an action. Use `[Nonempty Action]` or a fallback argument,
    and derive it in the export from `(E ⟨0,_⟩).action_nonempty`, since H ≥ 1 from 0<ε≤H.
  - Do not add `hH` or a fallback binder to the Prop.
  - The conversion from the Prop's `∀ h : Fin H` optimality to `SuffixOptimal` for all n needs an
    explicit lemma: for n ≥ H, `drop` gives `[]` and both `trajectoryValue []` and `optimalValue []`
    are 0.
- **F-a5 (citation nit).** `allLevelBernsteinEvent_policyPerformance` is at
  PolicyPerformanceConsumption.lean:70, not :68.
- **F-a6 (process).** AGENTS.md forbids Astra models. Builder and critic briefs must name Sol, Terra
  or Luna. The worker brief must include the validation command and the stop condition, as the
  ownership table already does.

### Other answers

- **Open question 2 (randomized policies).** Not required, since P:739 fixes deterministic optimal
  policies. A later extension to policies randomized over Â_h(s) would be a strengthening by
  convexity, not a correction.
- **Prop draft.** The names match existing ones: `policyTrajectorySuffix` takes
  `(es) (f : ℕ → State → Action) (h)` (Ch3Definitions.lean:265), and `empiricalStages` returns a
  `List` (:232). There is no new Ch3 import, so the G2 allowlist is respected. The new library modules
  reach `Ch3Definitions` only transitively, so `g2_library_to_statements` does not grow.
- **Name.** `Thm3_9_positiveN` is consistent with `Thm3_2_positiveN` and `Lemma3_5_positiveN`.

---

## (b) Two-state, one-action Q lower bound

### Faithfulness

- **Statement shape.** The quantifier order is "∀γ,ε ∃M₀,M₁ ∀N ≤ budget ∀Q̂ …". It matches MB:1541–1556:
  "Consider any ε, γ … one can construct two MDPs … such that if N ≤ … then any estimator".
  - The domain is 0<ε<1/(32(1−γ)) with γ∈[2/3,1), as printed.
  - The strict "> 0.1" is preserved.
  - N=0 is included.
  - Data are the full N-per-pair array for both states (`samplingLaw`), as in "for each state-action
    pair".
- **Deterministic estimators (open question 1).** Acceptable as the printed meaning. The proof
  (MB:1803–1835) builds ψ pointwise from Q̂. The monograph's tests are maps ψ: X → {0,…,M} (P, Fano
  section, around 1113–1119), so the framework is deterministic.
  - This differs from Thm 3.7(ii), where a qualifier is printed for (i) only. Here there is no
    qualifier and no randomization anywhere in the argument.
  - The randomized version is a genuine strengthening. It does not follow from the deterministic "or"
    conclusion, only from the underlying sum bound.
  - So the plain name is fine, provided the docstring says "estimator = function of the sample array".
- **Equal rewards.** `hardMDP` has reward `if s then 1 else 0` independent of p
  (GenerativeLowerBoundTwoStateDefinitions.lean:24), so `M₀.reward = M₁.reward` holds by
  unfolding. The conjunct only strengthens the existential, and it prevents the trivial identification
  the plan describes. Keep it, together with both discounts equal to γ.
- **Constant.** 0.003 < 9/2560 = 0.003515625, so the library export (ObservationLaw.lean:138) assumes
  less and implies the printed statement. Per AGENTS.md this is not a discrepancy: no suffix and no
  SOURCE-ISSUES entry. The existential is nontrivial, because M₀ = M₁ would fail via the constant
  estimator Q⋆.
- **Name.** `Eq_P_Mi_Q_inaccurate_lower_generative` follows the existing `Eq_<label>` convention
  (`Eq_mdp_value_Q`, `Eq_QV_pi_perturbation_r_inf`).

### Required fixes

- **F-b1.** The SOURCE-ISSUES C4 paragraph currently says that "an arbitrary randomized-Q extension of
  the standalone two-state, one-action testing example … remain[s] separate". Update it in the same
  change. The deterministic-estimator standalone example is now covered by the new entry. The
  randomized extension (via `finiteSeed_test_error_gt_one_tenth`) remains an optional strengthening.
- **F-b2.** COVERAGE should say "A displayed claim: no numbered-ledger entry", following the
  `Eq_mdp_value_Q` and `Eq_QV_*` precedent. Also mention that the export's budget 9/2560 is looser than
  the printed 0.003. Close TRIAGE 3.r.
- **F-b3.** Keep the `0.003` literal for reading fidelity, but the builder must confirm that `norm_num`
  closes the budget comparison. Fall back to `3 / 1000` and state the change in the docstring.
- **Open question 2.** Keep the printed ∃ form. An explicit-witness variant is optional.

---

## (d1) C13 literal trigger, recomputed

- **Printed rule.** ON:1280 triggers when N^all ∈ {1,2,⋯,2^{log₂K}}. Read literally, this is every
  integer from 1 to 2^{log₂K}. The count is reset to the epoch count (ON:1282–1287).
- **Instance S=A=H=1, K=32.** There is one row, visited once per episode, so the trace is forced.
  2^{log₂32} = 32 under both the real and the floor reading, and also under "{1..K}".
  - Every visit n ∈ {1..32} triggers, and each trigger stores the epoch count, which is 1.
  - With the Lean indexing of `Lemma5_12_powerOfTwo_corrected` (stored count after k·H steps, k=0..31):
    k=0 gives max{0,1}=1, and k=1..31 each give 1. **LHS = 32.**
  - If N_h^k is instead read as the end-of-episode count, all 32 terms are 1. The LHS is 32 either way.
- **RHS.** 4·S·A·H·log₂K = 4·1·1·1·5 = **20**. Since 32 > 20, the literal claim fails. Confirmed.
- **Lean modelling.** `onlineMVPCountTablesStep` (MVPCountDefinitions.lean:39–51) stores
  Σ pendingAfter, the epoch count, so the "verbatim copy with trigger replaced" yields stored = 1
  after every visit, as claimed.
- **Placement.** The precedent for a `_printed : Prop` defined in a library file plus `not_…` exists
  (`Ch7Rest/*Printed*.lean`, `RobustRL/Ch7/Ch7PrintedStatements.lean`). No statement entry and no
  `_holds`. Correct.

Docstring notes (not blocking):

- The Prop quantifies over arbitrary traces, but for S=A=H=1 the only trace is the algorithm's own.
  Say so, so that the refutation is visibly about the literal algorithm.
- The refutation concerns the consecutive-integer reading only. The dyadic reading is proved
  (`Lemma5_12_powerOfTwo_corrected`). The pointwise factor-two diagnostic
  `onlineMVP_factor_two_pointwise_fails` stays a separate sub-claim.
- **Open question 2.** `1 ≤ n ∧ n ≤ 2^{Nat.log 2 K}` is an acceptable formal reading, and K=32 makes
  the witness reading-independent.

---

## (d2) C17 terminal value H, recomputed

- **Auxiliary.** The auxiliary sets V_{H+1}^{k,I} = H (ON:4422). At stage H, Q = min{r + ⟨P̂^{(j)}, H·1⟩
  + b, H}. Here ⟨P̂, H·1⟩ = H for any probability vector, and r, b ≥ 0. The latter needs c₁, c₂ ≥ 0
  and L = log(1/δ′) ≥ 0. So V_H^{k,I} = H·1 for every k and I, and X_{H,I} = {H·1, 0}.
- **Learner.** S=A=1, H=K=2, zero rewards. After episode 1, both stage rows have N^all = 1. The
  trigger fires at 1 under both the literal and the dyadic rule, N_h = 1, P̂ is the Dirac row, and the
  variance is 0.
  - Stage 2 (terminal 0, ON:1267) gives V₂² = min{0 + 0 + 0 + c₂·2·L/1, 2} = min{2c₂L, 2}.
  - For 0 < c₂L < 1 this lies in (0,2), so it is not in {0,2}.
  - So eq:Vk-Itrue fails at h=H=2, k=2, for every profile I. Confirmed.
  - If V_h^k is read as the post-episode-k value, the failure is at k=1 instead. The refutation is
    robust to the indexing.
- **Parameters.** These are consistent with C17. The printed allocation δ′ = 100δ/(S²A²H²K²) = 6.25δ
  gives δ = 4δ′/25 ∈ (0,1). With q = min{1/(2c₂), 1/(80000 log 6)}, 0 < 2c₂q ≤ 1. C16 is not involved,
  because L is a free parameter tied to δ′ only by the parameter lemma.
- **Inactive corrections.** In the Lean learner, `onlineZeroCountSafeQUpdate`
  (ZeroCountUpdateDefinitions.lean:6) takes its `N=0` branch only at zero counts, and here both queried
  rows have N=1, so C8 is inactive. `onlineMVPSourceBatchStart/End` give the whole 1-element list for
  n<2, so the batch is the sole sample. The bonus uses `c₂*H*L/N` with H = cap = 2, as printed
  (eq:bh-defn-Bernstein-ucbvi, ON:406–411; ON:1300–1308). The trigger fires at count 1, so C13 is
  inactive.

**Open question 1.** Using the corrected Lean learner is acceptable, provided the docstring states
that on this instance it computes the same number as the printed update. The theorem
"learner value = min(2c₂L, 2)" is that statement. A literal learner encoding is not needed.

### Required fixes

- **F-d2a.** Make `printedFixedProfile_lastStage_eq` genuinely general. Printed n = 2^{j−2} is 1/2 at
  j=1, so a `kernel … → FiniteDistribution State × ℕ` does not literally cover n. State the lemma
  with an arbitrary **nonnegative bonus** b (or n : ℝ with max{n,1}), an arbitrary finite
  distribution P̂, and r ≥ 0. Only b ≥ 0 and the fact that P̂ is a probability vector are used. Take
  hypotheses c₁, c₂, L ≥ 0, or simply b ≥ 0.
- **F-d2b.** The docstring must state the V_h^k indexing used (pre-episode, k=2) and note that the
  post-episode reading fails at k=1.
- **F-d2c.** In the SOURCE-ISSUES C17 text, replace the sentence "A complete Lean execution witness …
  has not been added". Keep "no refutation of the final MVP regret or decoupling conclusion is
  claimed". Add a COVERAGE pointer. No statement entry and no `_holds`.

**Refutation placement.** I agree that both refutations belong in SOURCE-ISSUES (C13 and C17) plus
COVERAGE pointers, as library theorems with axioms ⊆ {propext, Classical.choice, Quot.sound}, and not
in `Statements/ChN.lean`.

---

## Layering (frozen gates)

- **(a)** The three new Generative modules import FiniteHorizon* library modules only. They never
  import `Formalization.Statements.*` directly, so `g2_library_to_statements.txt`, which only shrinks,
  is untouched. `Ch3.lean` gets no new import. `Ch3Proofs.lean` adds the any-tie export module.
- **(b)** `Ch3.lean` gets no new import: `DiscountedMDP` and
  `StatisticalRL.ModelBasedPolicyLearning.Samples/samplingLaw` are already used at Ch3.lean:80 and
  :234–241. `Ch3Proofs.lean` adds `GenerativeLowerBoundObservationLaw`.
- **(d1, d2)** New Online/Regret/MVP files import definition modules only, in the
  `StatisticalRL.OnlineRL` namespace (G6). The lead adds them to `Formalization.lean` so that the axiom
  audit covers them.

## (c), brief

The deferral and the L classification are reasonable. The claim that TD under the log² schedule does
not transport to the log³ schedule is plausible from the cited window and terminal constraints, but it
has not been verified here. The probe should confirm it before any compiler time is spent.

The w.h.p. reading with δ inside the log is the natural meaning of "the TD-learning analysis gives
−Õ(…)". An explicit polylog is an acceptable concretization of Õ only if the docstring discloses the
exponents. Otherwise use `_restricted`.

The pathwise clause Q̃ ≤ Q and the lift to S×A are sound at the paper level. Quantifying over every
deterministic optimal f matches "a deterministic optimal policy π⋆".
