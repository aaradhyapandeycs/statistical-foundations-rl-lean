# CRITIC: small batch 2, part A (items b, d1, d2)

Public copy of the independent critic report; local paths removed.

Post-review note (added to this public copy, 2026-11-08): this critic reviewed the pre-integration snapshot; integrated into the library on 2026-11-08 (imports-only changes plus the critic's F1–F3 docstring fixes). Snapshot files map to the intended integrated locations as follows: `EqPMiQStatement.lean` → the `Eq_P_Mi_Q_inaccurate_lower_generative` entry in `Formalization/Statements/Ch3.lean`; `EqPMiQProof.lean` → its `_holds` wrapper in `Formalization/Statements/Ch3Proofs.lean`; `OnlineMVPLiteralTriggerCounterexample.lean` → `Formalization/Online/Regret/MVP/OnlineMVPLiteralTriggerCounterexample.lean`; `OnlineMVPPrintedTerminalCounterexample.lean` → `Formalization/Online/Regret/MVP/Decoupling/OnlineMVPPrintedTerminalCounterexample.lean`. Short file names below refer to the reviewed snapshot files, and the file hashes are those of the snapshot. The review text below is otherwise unchanged.

Date: 2026-11-08. Independent critic; I did not build these. No paper fetched; no builder file,
`Formalization/`, `docs/` or the project's `Formalization*` build outputs touched. Lean runs: only
`bash scripts/lean-local.sh`, foreground, one at a time.

## Integrity

- The builder's reviewed snapshot (4 files) matches the builder's snapshot hash list;
  the builder's live working files are byte-identical (`cmp`).
  - EqPMiQProof.lean `0817da97eb80bd04f521edf30adbc98eddd1466e0e2b2a50ba10e344c055e55b`
  - EqPMiQStatement.lean `61d28606c0c6d6b2e92eeb74f2a9e1ebf6c7b297591e8d3646a2d0d118c4a06d`
  - OnlineMVPLiteralTriggerCounterexample.lean `0033e6ec83fea69d136803193f057900a2b66c4681cb3085d48bb307b79a876b`
  - OnlineMVPPrintedTerminalCounterexample.lean `11c9e0dfd143115bce2f787781a8191b22f41cfebbe85c71f4870185c64cc340`
- Source hashes recomputed: MB `b7e7abfb…214ac4d`, ON `393a4d26…ccb8c53` (match provenance).
- Independent recompile: snapshot copied to the reviewer's private probe folder (only change: the
  `EqPMiQStatement` import line, builder's working prefix → reviewer's private prefix, proof file sha `ce0ba73f…`), compiled to
  the reviewer's private olean folder, all four exit 0, no errors (6s, 2s, 2s, 7s).
- Probe `CriticProbe.lean` in the reviewer's private probe folder (sha `732971f1…0890f73`), exit 0, 9s: all eight
  exported theorems depend only on `[propext, Classical.choice, Quot.sound]`.
- Forbidden-token grep (sorry, admit, axiom, opaque, implemented_by, native_decide, maxHeartbeats,
  unsafe, extern): no hits.

## (b) `Eq_P_Mi_Q_inaccurate_lower_generative` — ACCEPT WITH DISCLOSURES

Source MB:1541–1556 read first.
- Quantifier order: printed "for any ε, γ … construct M₀, M₁ such that if N ≤ … then any estimator"
  = Lean `∀ γ ε, hyps → ∃ M₀ M₁, … ∀ N ≤ budget, ∀ QHat`. Correct; MDPs chosen before N and Q̂.
- Domain `2/3 ≤ γ < 1`, `0 < ε < 1/(32(1−γ))`: exact. Budget literal `0.003` kept (norm_num
  closes `0.003 ≤ 9/2560`). Strict `> 0.1` and strict `> ε` preserved. `N = 0` included.
- Two states (`Bool`, `true` = s₁), one action (`Unit`). Data: full `N`-per-pair product law over
  both rows (`samplingLaw` = `Measure.pi` of the true rows), as printed.
- Equal rewards and equal discount `γ` conjuncts: these only strengthen the existential and block
  the trivial witness at N = 0 (two MDPs with different reward and far-apart Q⋆). With equal rewards
  and equal kernels Q⋆ coincide, so the existential is non-vacuous; at N ≥ 1 the content is the
  testing lower bound. Probe confirms the budget admits N = 810 at γ = 2/3, ε = 1/100.
- Deterministic estimator (function of the sample array): acceptable reading (source proof builds a
  deterministic test from Q̂); disclosed in docstring. Randomized version is a strengthening (C4).
- Wrapper applies `sourceHardMDP_full_Q_estimation_lower` (budget 9/2560, looser) with the witnesses
  `sourceHardMDP … false/true`; per AGENTS.md this is implication, not a discrepancy.
- Disclosure required (already drafted): deterministic estimators; C4 strictness via Pinsker.

## (d1) `not_Lemma5_12_literalTrigger_printed` (C13) — ACCEPT

Source ON:1264–1310 and 1570–1577 read first.
- Mechanical diff: `Lemma5_12_literalTrigger_printed` vs `Lemma5_12_powerOfTwo_corrected`
  (Ch5.lean:419–428) is identical after renaming the run function; `onlineMVPLiteralCountTablesStep`
  vs `onlineMVPCountTablesStep` differs only in the trigger (`onlineMVPLiteralRowTrigger K` vs
  `onlineMVPRowTrigger`) and a line break. Only the trigger rule is substituted.
- Trigger `1 ≤ n ∧ n ≤ 2^{Nat.log 2 K}` is the literal `{1,2,⋯,2^{log₂K}}` (ON:1280) under the floor
  reading; the probe proves that for K = 32 it is exactly `{1..32}`, so the real reading
  (`2^{log₂K} = K`) and the floor reading coincide on the witness.
- Computation: S = A = H = 1, K = 32. The trace is forced (one row, one successor), so the
  universally quantified trace is the algorithm's own. Each visit triggers and stores the epoch
  count 1 (pending reset after each trigger, ON:1282–1287); k = 0 term is 1/max{0,1} = 1. LHS = 32,
  RHS = 4·1·1·1·(log 32/log 2) = 20. 32 > 20. Indexing (N_h^k = stored count before episode k,
  stage-tagged rows) matches the corrected entry; the end-of-episode reading also gives 32.
- Not a strawman: the printed lemma is about the printed algorithm, and the only printed rule is
  the literal set; the dyadic reading remains proved separately.

## (d2) `not_eq_Vk_Itrue_printed` (+ `_sourceParameters`) (C17) — ACCEPT WITH DISCLOSURES

Source ON:4419–4472 (alg:main-fixed-profile, eq:X-I-ours, eq:Vk-Itrue), ON:1264–1308, 406–411,
1339–1352, 1389–1390 read first.
- Auxiliary model: `printedFixedProfileStageQ` = `min{r + ⟨P̂, V⟩ + c₁√(Var_P̂(V)·L/max{n,1}) +
  c₂·H·L/max{n,1}, H}`, terminal `V_{H+1}^{k,I} = H`, `V = max_a Q`. Matches ON:4423–4431. Rows are
  arbitrary finite distributions, counts arbitrary reals (covers n = 2^{j−2} = 1/2), rewards ≥ 0.
  Since every profile/expanded sample set yields some such data, the universal statement over
  `stagesOf` is at least as strong as needed. `X_{h,I}` = `{V_h^{k,I} | k ∈ Fin K} ∪ {0}`: exact.
- `printedFixedProfile_lastStage_eq`: stage-H aux value ≡ H, needing only r ≥ 0, c₁, c₂, L ≥ 0
  (L = log(1/δ′) ≥ 0 since δ′ < 1). F-d2a of the plan check is satisfied.
- Learner: the value is computed with `onlineCappedBackwardValueAt (H) L c₁ c₂
  (onlineMVPHistoryPlanningStages …)`, the same table that `onlineMVPCommittedGreedyPlanner` (used
  by `MVP_regret_corrected`, Ch5.lean:492, Ch5Proofs.lean:308–312) maximizes; index `1` with
  `history = first episode` is source stage 2, pre-episode 2, matching the export's
  `history.take (k*H)` / `h+1` convention. Corrections inactive: row count 1 so the C8 `N = 0`
  branch is not taken; `onlineMVPSourceBatch*` takes the whole length-1 list for n < 2 (dyadic
  trigger at 1 = literal trigger at 1). Bonus `c₂·H·L/N` with H = cap = 2, variance 0, Dirac row,
  terminal 0: value `min{2c₂L, 2}`. I also proved (probe) the pre-episode-1 value is 2 = printed
  initialization, so the learner model is consistent with ON:1267.
- Negation: printed eq:Vk-Itrue asserts, for each k, h: `V_h^k = V_h^{k,I_true} ∈ X_{h,I_true}`.
  Lean proves at h = H = 2, k = 2: V ≠ `V_2^{k',I}` for every k' and every profile data, and
  V ∉ `X_{2,I}`. This implies the negation for I_true (strictly stronger). Correct.
- Parameters: δ′ = 100δ/(S²A²H²K²) with S=A=1, H=K=2 (printed ON:1390 allocation), δ = (4/25)δ′ ∈
  (0,1), L = q, 0 < c₂L ≤ 1/2, ι = 40000(log₂K)³log(3SAH)L with the printed formula. Works for every
  c₂ > 0 and c₁ ≥ 0, so "suitably chosen constants" (thm-mvp-regret) cannot escape it. C16 not used.

## R-items (blocking)

None.

## F-items (non-blocking)

- F1 (d2). `onlineMVP_C17_sourceParameters` states `SAH·ι ≤ 2 = K`. The regret proof's nontrivial
  regime is `K > SAH·ι` (ON:1392–1394); in fact `SAH·ι = 2ι ≤ 1 < 2`, so strictness holds. Either
  strengthen the conjunct to `≤ 1` / `< 2` later, or say "K ≥ SAH·ι (indeed K > SAH·ι)" in docs.
  eq:Vk-Itrue is asserted unconditionally anyway, so this does not affect the refutation.
- F2 (d2). The Lean learner side has no K parameter (only one completed episode is used); the `K`
  in `not_eq_Vk_Itrue_printed` is the auxiliary's episode count. The source instance is K = 2.
  Docs should say "H = K = 2 instance; the auxiliary family is excluded for every K".
- F3 (d2). The auxiliary is encoded by per-episode stage data rather than by an explicit
  profile→batch-row map. This is a generalization (all data, not only data arising from some
  `D^expand`), harmless for the "for every profile" direction; keep the docstring sentence.
- F4 (b). COVERAGE row should keep "estimator = function of the full sample array" visible (it is
  in the draft).

## Recommended text

- SOURCE-ISSUES C4, C13, C17 and COVERAGE (b) row, Lemma 5.12 row, `eq:Vk-Itrue` row: adopt
  the builder's drafts for the lead as written. Optional additions:
  - C17: after "`onlineMVP_C17_sourceParameters`", add "(which also gives K = 2 > SAH·ι)".
  - C13: the draft already says "With one state and one action the trace is forced, so this is
    every run of the literal algorithm; for K=32 the floor, real and {1,…,K} readings agree" — keep.
- Status words: (d1)/(d2) are refutations of printed claims recorded in SOURCE-ISSUES with
  COVERAGE pointers; no statement entry, no `_holds`; C17 keeps "no refutation of the final MVP
  regret or decoupling conclusion is claimed".
- Integration: move files unchanged; add both to `Formalization.lean`; recompile Ch3, Ch3Proofs,
  Formalization.lean, Audit.lean.
