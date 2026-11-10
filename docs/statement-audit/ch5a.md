> Public copy of an independent five-bin statement audit (2026-11-09/10), scrubbed of local paths and agent identifiers. Auditors were independent of the builders. No result here is author-approved. Method and totals: [README](README.md).

# Five-bin statement audit — batch ch5a (2026-11-09)

Auditor: independent statement auditor (read-only; no Lean compiled, no files edited outside this report).
Targets: `Formalization/Statements/Ch5.lean` (defs) and `Formalization/Statements/Ch5Proofs.lean` (wrappers).
Source: `source/upstream/tex/chapters/onlineRL.tex` (5129 lines). Source issues: `docs/SOURCE-ISSUES.md`.

## Shared context

### Standing source material read

- Sampling protocol `onlineRL.tex:20–36`: s₁ᵏ iid ρ; πᵏ chosen from episodes 1..k−1.
- UCBVI algorithm `:286–345`. Initialize Q=H, P̂=1/S. Greedy policy at the start of each episode. Counts update after each step. Capped backup `Q ← min{r + ⟨P̂,V⟩ + b, H}`.
- Bernstein bonus `:407–417`: `b = c₁√(Var_P̂(V) log(1/δ′)/N) + c₂ H log(1/δ′)/N`, c₁,c₂>0, `δ′ = δ/(100S²A²H²K²)`. Line 395: δ>0 with "1−δ the target success probability".
- Theorem 5.2 `:472–482`. Notation `:555–575`. iota `:726–733`.
- Lemma 5.5 `:765–775` (c₁≥4, c₂≥c₁²). Line 777: "all subsequent analysis is carried out on the [optimism] high-probability event".
- Remark `:790–802`, Lemma 5.6 `:808–818`, T-terms `:836–893`, Lemma 5.7 `:925–957`, Lemma 5.8 `:988–1005`, T0 `:1027–1033`, Lemma 5.9 `:1055–1092`.
- MVP algorithm `:1256–1310` (trigger `:1280`) and doubling prose `:1213–1217`. Remark `:1330–1332`. MVP δ′/iota `:1385–1391` and regime `:1402–1407`.
- MVP expanded samples and batches `:1418–1470`. Optimism recap `:1480–1487`. Profile `:1506–1525`. Lemma 5.11 `:1540–1542`. Lemma 5.12 `:1570–1577`. Assumption X `:1670–1685`. Lemma 5.13 `:1696–1712`.
- Monotone f `:3296–3311`, Remark `:3510–3524`, Lemma 5.22 `:3612–3615`.

### Project definitions expanded (checked against the source)

- `EnvironmentStage` (`MDP/EnvironmentDefinitions.lean:9`) has the fields Nonempty S, Nonempty A, transition row, reward and 0≤r≤1. These are standard MDP typing and the source's reward range.
- `optimalValue`/`optimalQ` give the backward Bellman optimum with terminal 0. `greedyStages` gives the optimal-greedy policy, so `trajectoryValue (greedyStages ·)` is V⋆ and `trajectoryQ` is Q⋆.
- `onlineSequentialEpisodeLaw` (`SourceOptimism/SequentialEpisodeDefinitions.lean:51`) = iid reset vector ⊗ causal chronological successor law. Each step draws from the true row `(E h).transition s a` of the row chosen from revealed history. This is a faithful encoding of `:20–36`.
- `onlineEpisodicChoose` gives the stage clock `len % H`. At episode starts the state is reset to `initial k`. The planner sees only `history.take((len/H)·H)`, i.e. completed episodes. `fallback` is used only off the realized support.
- `onlineCappedStageQ` → `onlineZeroCountSafeQUpdate`: `N=0 ↦ H`, otherwise `min(r + ⟨P̂,V⟩ + c₁√(Var_P̂ V·L/N) + c₂HL/N, H)`. P̂ is the empirical row of the observed successor list, or uniform 1/S at N=0. This is the printed backup at N>0 plus the C8 zero-count completion.
- `onlineCappedGreedyPlanner` is one fixed deterministic maximizing tie rule, a function of the Q table (via `Classical.choose` on the table-determined proposition).
- `onlinePreEpisodePlanningStages E history k` uses `history.take(k·H)`, i.e. the tables before (0-based) episode k.
- `onlineRegretAnalysisCharge` is the printed bonus at N>0 and H at N=0 (C8).
- W/T quantities:
  - `onlineActualEpisodeW1/W2`, `onlineActualW3Point`, `onlineActualT5`, `onlineActualT6UCB/Policy/Difference` and `onlineActualEpisodeRegretTerms` (T1..T4) all evaluate along the realized (s_hᵏ,a_hᵏ).
  - Pre-episode-k tables are used for P̂ᵏ, Vᵏ_{h+1} (`onlineActualOptimisticContinuation`), V^{πᵏ}_{h+1} (`onlineActualPolicyContinuation`, the true value of the deployed policy) and V⋆_{h+1}.
  - Each matches `:836–893`/`:931`.
  - The T3 summand at the last stage uses the next episode's reset state rather than s_{H+1}. It is multiplied by V_{H+1}=0, so it is harmless.
- MVP:
  - `onlineMVPCountTablesRun` (power-of-two trigger after increment, per-row pending reset, stored = batch size) is a faithful encoding of the prose-dyadic algorithm (C13).
  - `onlineMVPSourceBatchList` takes the slice `[m,2m)` with m = stored count, or the whole list if the count <2. This is the latest completed batch, matching P̂^{(j)} at `:1462–1466`.
  - `onlineMVPCommittedGreedyPlanner` recomputes from current batches each episode. This equals the source's recompute-on-trigger, since batches only change at triggers.
  - `sourceMVPProfileIndex n = log2 n + 1` (n>0) equals `max{j: 2^{j−1} ≤ n}`, and the visit count is the pre-episode cumulative count.
  - `MVPUniformSource.batchRow j` = empirical row of 0-based positions `2^j..2^{j+1}−1` of the expanded data. This is source batch l=j+2 (`:1462`). `samplingLaw E K` is the product of the true rows (`def:filt2`).
- `FiniteDistribution.expectation`/`variance` are the finite sum and E[f²]−(Ef)², i.e. the population variance.

No fallback or junk-branch definition was found that changes source meaning on the source domain.

### Wrappers

Every `_holds` wrapper in scope applies one library export via `simpa`/`exact`. A few also derive small corollaries that the guide permits:

- weakening a strict confidence;
- the 6SAHK→12S²AHK budget comparison (Lemma 5.7 W1);
- projecting onto a sub-event (Lemma 5.9);
- `√(a+b) ≤ √a+√b` (Remark 5.13);
- a radius algebra rewrite (Lemma 5.13);
- averaging a pointwise bound over ρ (Lemma 5.4).

None restates or re-proves a result of substance.

---

## 1. Lemma5_5_corrected — Ch5.lean:40 (wrapper Ch5Proofs.lean:45)

Source: `lemma:opt`, onlineRL.tex:765–775, plus the algorithm and bonus (:286–345, :407–417).

**Reconstruction.** Assume c₁≥4 and c₂≥c₁², with δ′=δ/(100S²A²H²K²). Then with probability > 1−2SAHKδ′, for all (s,a,h,k): Qᵏ_h(s,a) ≥ Q⋆_h(s,a) and Vᵏ_h(s) ≥ V⋆_h(s). The probability is over UCBVI's actual run.

| binder | Lean type | bin | citation |
|---|---|---|---|
| State, Action, Fintype | Type, Fintype | TYPING | finite S, A |
| H, hH | ℕ, 0<H | TYPING | H≥1 |
| K, 0<K | ℕ | TYPING | K≥1 (:474) |
| E | Fin H → EnvironmentStage | TYPING | MDP (P_h, r_h ∈[0,1]) |
| ρ | FiniteDistribution | STANDING | :26–33 |
| δ, 0<δ | ℝ | SOURCE | :395 |
| δ≤1 | | STANDING | :395 ("1−δ success prob."), Thm 5.2 0<δ<1 |
| c₁, 4≤c₁ | | SOURCE | :766 |
| c₁²≤c₂ | | SOURCE | :766 |
| fallback (let) | Classical.choice | TYPING | off-support totalization only |
| zero-count completion / fixed tie (in planner) | — | DISCLOSED | C8 (+C6 noted) |

Bin counts: SOURCE 4, STANDING 2, TYPING 6, DISCLOSED 1, EXCESS 0.

**Other checks**
- The confidence is strict `<`, matching "exceeding".
- Quantifiers ∀k ∀h ∀s(,a) sit inside the event.
- V⋆/Q⋆ are taken via the greedyStages trajectory value/Q.
- No junk: δ′>0, and 1/δ′≥1.
- Universe: State and Action are fixed to `Type` (universe 0). This is a harmless typing specialization (any finite type is equivalent to one in Type 0), noted only.

**VERDICT: PASS-DISCLOSED.**

## 2. Lemma5_6_corrected — Ch5.lean:76 (wrapper :52)

Source: `lemma:decomdetail`, :808–818 (proof :820–842).

**Reconstruction.** Deterministic. For every k: V₁ᵏ(s₁ᵏ) ≤ Σ_h {⟨P̂ᵏ−P, Vᵏ_{h+1}⟩ + bᵏ_h + r_h + ⟨P − e_{s_{h+1}}, Vᵏ_{h+1}⟩}. Here a_hᵏ is the greedy action of the Qᵏ table, and the tables come from the algorithm.

| binder | type | bin | citation |
|---|---|---|---|
| State, Action, Fintype, Nonempty ×2 | | TYPING | |
| H, 0<H | | TYPING | |
| stage : Fin H → OnlineObservedPlanningStage | arbitrary observed tables | TYPING (generalization of P̂ᵏ data) | :555–575 |
| state, action : ℕ → · | arbitrary realized path | TYPING (generalization) | |
| δ′, 0<δ′≤1 | | STANDING | :410–414 (δ′<1) |
| c₁,c₂ ≥ 0 | | STANDING | :407 (c>0); weaker |
| greedy hypothesis (action h attains actionMaximum of the same Q table) | | SOURCE | algorithm greedy rule :303, proof step (i) :822 |
| bonus replaced by analysis charge (H at N=0) | | DISCLOSED | C8 (explicitly names Lemma5_6_corrected) |

Bin counts: SOURCE 1, STANDING 2, TYPING 7, DISCLOSED 1, EXCESS 0.

**Other checks**
- The terminal continuation is 0. The summand at n=H−1 multiplies a zero tail, so the arbitrary `state H` is harmless.
- Covers every greedy tie choice.

**VERDICT: PASS-DISCLOSED.**

## 3. Lemma5_7_W1_K2_corrected — Ch5.lean:116 (wrapper :64)

Source: `lem:bound-W1-W2-ucbvi-proof`, :925–957 (W₁ at :910–922, iota :726–733).

**Reconstruction.** With probability > 1−12S²AHKδ′: W₁ ≤ ⅛√(SAH·T6low·ι) + ⅛√(SAH·T6diff·ι) + ⅛SAH²ι. The lemma also bounds W₂ and W₃.

| binder | bin | citation |
|---|---|---|
| State/Action/Fintype, H/hH, E, fallback | TYPING | |
| ρ | STANDING | :26–33 |
| 2≤K | DISCLOSED | C12 (K=1 counterexample; docstring) |
| 0<δ≤1 | SOURCE/STANDING | :395, Thm 5.2 |
| 4≤c₁, c₁²≤c₂ | STANDING | :766 + :777 (analysis runs under Lemma 5.5's regime) |
| zero-count completion + fixed tie | DISCLOSED | C8 |
| conclusion restricted to the W₁ clause only | DISCLOSED | docstring; SOURCE-ISSUES scope note "earlier W1-only entry remains available" |

Bin counts: SOURCE 1, STANDING 2, TYPING 6, DISCLOSED 3, EXCESS 0.

**Other checks**
- Strict confidence.
- iota is the printed expression, with log₂ written as `log K/log 2`.
- With K≥2, iota is positive.
- T6 quantities are defined on the same path.

**VERDICT: PASS-DISCLOSED.**

## 4. Lemma5_7_K2_corrected — Ch5.lean:152 (wrapper :88)

Source: as in entry 3, all three bounds (:938–946) plus W₃ (:931).

**Reconstruction.** One event with probability > 1−12S²AHKδ′ on which:
- W₁ ≤ (as above);
- W₂ ≤ ⅛√(S²AH·T6diff·ι) + ⅛S²AH²ι;
- W₃ ≤ ⅛√(SAH³·T6low·ι) + ⅛√(S²AH³·T6diff·ι) + ⅛S²AH³ι.

The binder table is identical to entry 3, without the "W1 only" row. Counts: SOURCE 1, STANDING 2, TYPING 6, DISCLOSED 2, EXCESS 0.

**Other checks**
- All three inequalities match term by term.
- W₃ uses (Vᵏ_{h+1})² against P̂ᵏ − P.
- Joint event, strict confidence.

**VERDICT: PASS-DISCLOSED.**

## 5. Lemma5_3 — Ch5.lean:197 (wrapper :100)

Source: `lem:sum-inv-Nhk-ucbvi`, :639–646.

**Reconstruction.** For K≥2, the algorithm satisfies Σ_k Σ_h 1/max{N_hᵏ(s_hᵏ,a_hᵏ),1} ≤ 2SAH log₂K. Here N_hᵏ is the visit count before episode k.

| binder | bin | citation |
|---|---|---|
| State/Action/Fintype, H/hH | TYPING | |
| 2≤K | SOURCE | :640 |
| E, initial, fallback, planner, path (all arbitrary) | TYPING (generalization: the actual run is an instance) | |

Counts: SOURCE 1, TYPING 7, others 0.

**Other checks**
- The count is the number of row-outcomes in `history.take(kH)` for row (h, s_hᵏ, a_hᵏ), matching "before episode k".
- `max{·,1}` as printed. log₂ = log K/log 2.
- This is a plain entry and the printed result is implied.

**VERDICT: PASS.**

## 6. Lemma5_4 — Ch5.lean:221 (wrapper :111)

Source: `lem:cum-var-ub-Hsquare-ucbvi-mean`, :648–658.

**Reconstruction.** Fix a deterministic π. For a trajectory under π, E[Σ_h Var_{P_{s_h,a_h,h}}(V^π_{h+1})] ≤ H².

| binder | bin | citation |
|---|---|---|
| State/Action/Fintype, H, 0<H, E | TYPING | |
| ρ (arbitrary initial law) | STANDING | :26–33 (s₁∼ρ) |
| π : Fin H → State → Action | SOURCE | :650 deterministic policy |

Counts: SOURCE 1, STANDING 1, TYPING 5.

**Other checks**
- `finiteTrajectoryVarianceSum` sums the true-row variance of the remaining-trajectory value V^π_{h+1} along the path.
- The trajectory law uses point-mass actions π_h(s).
- The rewards in [0,1] come from `EnvironmentStage`.

**VERDICT: PASS.**

## 7. Lemma5_8_K2_corrected — Ch5.lean:243 (wrapper :121)

Source: `lem:bound-T234`, :988–1005.

**Reconstruction.** Suppose ι ≥ 8max{c₁²,c₂}log₂K·log(1/δ′). Then with probability > 1−4log₂(KH)δ′:
- T₂ ≤ ½√(SAH·T₅·ι) + ½SAH²ι;
- |T₃| ≤ √(8T6ucb·L) + 5HL ≤ 4√(T6low·L) + 4√(T6diff·L) + 5HL;
- |T₄| ≤ √(2KH²L).

| binder | bin | citation |
|---|---|---|
| types, H/hH, E, fallback | TYPING | |
| ρ | STANDING | |
| 2≤K | DISCLOSED | C12 (K=H=1 impossible confidence) |
| 0<δ≤1 | SOURCE/STANDING | :395 |
| 4≤c₁, c₁²≤c₂ | STANDING | :766, :777 |
| iota threshold hypothesis | SOURCE | :1003 |
| T₂ uses the zero-count charge H; algorithm completion; fixed tie | DISCLOSED | C8 |

Counts: SOURCE 2, STANDING 2, TYPING 6, DISCLOSED 2, EXCESS 0.

**Other checks**
- All four displayed inequalities are present, including both links of the T₃ chain, on one event.
- Strict confidence.
- T₄ = Σ(realized rewards) − V^{πᵏ}₁(s₁ᵏ), as printed.
- The threshold hypothesis is satisfiable (c=4,16), so the entry is not vacuous.

**VERDICT: PASS-DISCLOSED.**

## 8. Lemma5_9_K2_corrected — Ch5.lean:293 (wrapper :136)

Source: `lem:bound-T56`, :1055–1092. T0 at :1027–1033.

**Reconstruction.**
- (a) With probability ≥ 1−14S²AH²Kδ′:
  - T₅ ≤ W₃ + 2HT₂ + 2KH² + √(32H²·T6ucb·L) + 5H²L;
  - T6low ≤ KH² + √(2H⁶KL);
  - T6diff ≤ 2H²T0ub + 18H²L.
- (b) If K ≥ SAH²ι, then with probability ≥ 1−30S²AH²Kδ′:
  - T6low ≤ 2KH²;
  - T₅ ≤ 6KH² + ½√(S²AH³·T6diff·ι) + 4S²AH³ι.

| binder | bin | citation |
|---|---|---|
| types, H/hH, E, fallback | TYPING | |
| ρ | STANDING | |
| 2≤K | DISCLOSED | C12 + scope note |
| 0<δ<1 | STANDING | Thm 5.2 :474 |
| c₁=4, c₂=16 fixed in the planner (no c binders) | DISCLOSED | docstring + SOURCE-ISSUES scope note "Fixed universal c1=4,c2=16" |
| K ≥ SAH²ι (part b only) | SOURCE | :1084, eq:assumption-K-proof-ucbvi |
| C8 completion, fixed tie | DISCLOSED | C8 |

Counts: SOURCE 1, STANDING 2, TYPING 6, DISCLOSED 3, EXCESS 0.

**Other checks**
- T0 is written out literally (3/8, 3/8, 1/4, 7√(KH²)L, +T₂).
- The 14/30 coefficients are as printed, and so are the ≤ ("at least").
- The c=4/16 choice lies inside the source's standing c-domain. It discharges the iota threshold for K≥2 (ι ≥ 40000 log₂K·log 3·L ≥ 128 log₂K·L).

**VERDICT: PASS-DISCLOSED.**

## 9. Thm5_2_corrected — Ch5.lean:346 (wrapper :163)

Source: `thm-ucbvi-regret`, :472–482. Regret definition :113ff / :779–783.

**Reconstruction.** For K≥1 and 0<δ<1, with probability ≥ 1−δ and suitably chosen c₁,c₂: Regret(K) = Σ_k (V⋆₁(s₁ᵏ) − V^{πᵏ}₁(s₁ᵏ)) ≤ Õ(√(SAH³K) + S²AH³).

| binder | bin | citation |
|---|---|---|
| types, H/hH, E | TYPING | |
| 0<K | SOURCE | :474 |
| ρ | STANDING | |
| 0<δ<1 | SOURCE | :474 |
| ∃c₁ c₂ with c₁=4, c₂=16 | SOURCE ("suitably chosen") | :480; universal since pinned |
| Õ made explicit as 20(…)(1+ι) | DISCLOSED (explicit strengthening) | docstring; scope note |
| C8 completion, fixed tie | DISCLOSED | C8 |

Counts: SOURCE 3, STANDING 1, TYPING 4, DISCLOSED 2, EXCESS 0.

**Other checks**
- The constants are pinned to 4/16, so they cannot depend on the problem instance, even though `∃` sits after `∀δ`.
- ι is polylog(S,A,H,K,1/δ), so the explicit rate is a valid Õ instance.
- At K=1, ι=0 and the bound is 20(√(SAH³)+S²AH³) ≥ H, which is non-vacuous and true.
- πᵏ is the planner on `history.take(kH)`, i.e. exactly the deployed policy.

**VERDICT: PASS-DISCLOSED.**

## 10. Remark5_5_corrected — Ch5.lean:382 (wrapper :433)

Source: unlabeled remark, :790–802.

**Reconstruction.** V₁ᵏ(s₁ᵏ) = max_a Q₁ᵏ(s₁ᵏ,a) = Q₁ᵏ(s₁ᵏ, π₁ᵏ(s₁ᵏ)), by the greedy policy update.

| binder | bin | citation |
|---|---|---|
| types, H, E | TYPING | |
| L, c₁, c₂ (all reals) | TYPING (generalization) | |
| history (all completed histories) | TYPING (generalization over k) | |
| h (all stages; source h=1) | TYPING (generalization) | |
| s | SOURCE | |
| C8 tables | DISCLOSED | C8 paragraph naming Remark5_5_corrected |

Counts: SOURCE 1, TYPING 7, DISCLOSED 1.

**Other checks**
- The planner's maximized table is the same `onlineCompletedHistoryPlanningStages E history` as `stages`. Both conjuncts are the printed identity.

**VERDICT: PASS-DISCLOSED.**

## 11. Eq_regret_asymptotic_ucbvi_corrected — Ch5.lean:401 (wrapper :437)

Source: :491–506 (`eq:burn-in-ucbvi`, `eq:regret-asymptotic-ucbvi`).

**Reconstruction.** Once K ≳ S³AH³, Regret(K) ≤ Õ(√(SAH³K)), w.p. ≥ 1−δ (under Theorem 5.2's premises).

Binders are as in entry 9, plus:

| binder | bin | citation |
|---|---|---|
| S³AH³ ≤ K | SOURCE (≳ read with constant 1) | :497 |

Counts: SOURCE 4, STANDING 1, TYPING 4, DISCLOSED 2.

**Other checks**
- Under S³AH³≤K we have S²AH³ ≤ √(SAH³K), so 40√(SAH³K)(1+ι) is a valid explicit Õ.
- Constant-1 burn-in witnesses the existential "≳". Any c<1 regime only costs a constant factor inside Õ.
- The docstring states the reading.

**VERDICT: PASS-DISCLOSED.**

## 12. Remark5_9 — Ch5.lean:436 (wrapper :449)

Source: remark :1330–1332. f and property at :3296–3311.

**Reconstruction.** f(p,v,n) = ⟨p,v⟩ + max{c₁√(Var_p(v)L/n), c₁²HL/n}. For p∈Δ, 0≤v, ‖v‖∞≤H and n a positive integer, f is non-decreasing in each entry of v.

| binder | bin | citation |
|---|---|---|
| Ω, Fintype, DecidableEq | TYPING | |
| p | SOURCE | :3305 |
| c₁, H (all reals) | TYPING (generalization; source c₁>0, H≥1) | |
| δ′, 0<δ′≤1 | STANDING | :410–414 |
| n, 0<n | SOURCE | :3305 |
| v ∈ [0,H] box (inside conjuncts) | SOURCE | :3305 |

Counts: SOURCE 3, STANDING 1, TYPING 5.

**Other checks**
- The second conjunct is exactly the per-entry statement. The first is the stronger entrywise-order form.
- Variance = population variance under p.
- This is a plain entry and no deviation was found.

**VERDICT: PASS.**

## 13. Remark5_13_corrected — Ch5.lean:457 (wrapper :457)

Source: remark :3510–3524 (`eq:T6ucb-ub-T6-low-T6-diff`). Quantities at :879–893.

**Reconstruction.** Deterministic: T6ucb ≤ 2T6low + 2T6diff, and √T6ucb ≤ √(2T6low) + √(2T6diff).

| binder | bin | citation |
|---|---|---|
| types, H, K, hH, E, initial, fallback, path | TYPING (all paths) | |
| δ, c₁, c₂ (all reals) | TYPING (generalization) | |
| C8-completed objects | DISCLOSED | C8 (docstring) |

Counts: TYPING 13, DISCLOSED 1.

**Other checks**
- T6ucb uses the true-row variance of Vᵏ_{h+1}. T6low uses the variance of V^{πᵏ}_{h+1}. T6diff = ⟨P,(Vᵏ−V^{πᵏ})²⟩.
- The wrapper derives the √ form by elementary algebra from the export (permitted).

**VERDICT: PASS-DISCLOSED.** Minor: SOURCE-ISSUES C8 does not name Remark5_13_corrected explicitly. The docstring points to C8, which covers the completed objects. This is acceptable but worth a one-line mention there.

## 14. Lemma5_22_corrected — Ch5.lean:473 (wrapper :172)

Source: `lemma:sqv`, :3612–3615.

**Reconstruction.** X is a random variable with Cmax = largest magnitude. Then Var(X²) ≤ 4Cmax²Var(X) and Var((X−EX)²) ≤ Cmax²Var(X). The second clause is false (C14).

| binder | bin | citation |
|---|---|---|
| Ω, MeasurableSpace, μ, IsProbabilityMeasure | TYPING | |
| X, Measurable X | SOURCE ("random variable") | |
| C, ∀ω \|X ω\| ≤ C | SOURCE (Cmax) | :3613 |
| second-clause coefficient 1 → 4 | DISCLOSED | C14 (machine-checked counterexample) |

Counts: SOURCE 2, TYPING 4, DISCLOSED 1.

**Other checks**
- Mathlib `variance` = evariance.toReal. X is bounded, so it is finite and there is no junk.
- The first clause is as printed.

**VERDICT: PASS-DISCLOSED.**

## 15. Lemma5_11 — Ch5.lean:494 (wrapper :180)

Source: `lemma:key2`, :1540–1542. Profile at :1506–1525.

**Reconstruction.** If K ≥ SAH log₂K, the number of total profiles induced by MVP is ≤ (4SAHK)^{SAH log₂K + 1}.

| binder | bin | citation |
|---|---|---|
| State/Action, Fintype, Nonempty ×2 | TYPING | |
| K, 1≤K; H, 0<H | TYPING | |
| K ≥ SAH·log₂K | SOURCE | :1541 |

Counts: SOURCE 1, TYPING 8.

**Other checks**
- The counted set is the image of all K×H row tables. It is a superset of algorithm-induced profiles, so the printed bound is implied.
- The profile index is exactly `max{j: 2^{j−1} ≤ N}`.
- The real exponent uses rpow with a positive base.
- The C15 issue concerns only the proof's intermediate family, not the statement.

**VERDICT: PASS.**

## 16. Lemma5_12_powerOfTwo_corrected — Ch5.lean:515 (wrapper :191)

Source: `lem:sum-inv-Nhk-mvp`, :1570–1577. Trigger at :1280 vs prose :1213–1217.

**Reconstruction.** For K≥2, Σ_k Σ_h 1/max{N_hᵏ(s_hᵏ,a_hᵏ),1} ≤ 4SAH log₂K. Here N_hᵏ is the stored latest-batch count.

| binder | bin | citation |
|---|---|---|
| types, Fintype, DecidableEq ×2 | TYPING | |
| H, hH | TYPING | |
| 2≤K | SOURCE | :1571 |
| row, next (arbitrary traces) | TYPING (generalization) | |
| power-of-two trigger in `onlineMVPCountTablesRun` | DISCLOSED | C13 (literal trigger refuted in Lean) |

Counts: SOURCE 1, TYPING 7, DISCLOSED 1.

**Other checks**
- The stage tag is `n % H`. The tables after k·H records give the pre-episode count. Stored = batch size.

**VERDICT: PASS-DISCLOSED.**

## 17. Lemma5_13_confidence_corrected — Ch5.lean:538 (wrapper :216)

Source: `lemma:uniform`, :1696–1712. Assumption X :1670–1685. Batches :1462–1466.

**Reconstruction.** Assume K ≥ SAH log₂K and families X_{h,I} (I∈C) satisfying Assumption X. Then with probability ≥ 1−δ′, simultaneously for all I∈C, 2≤l≤log₂K+1 and X_{h,s,a}∈X_{h,I}:

Σ⟨P̂^{(l)}−P, X_{h+1}⟩ ≤ Σ max{·,0} ≤ √(SAHι/(2^l log₂K)·ΣVar) + SAH²ι/(2^l log₂K).

| binder | bin | citation |
|---|---|---|
| types, 0<H, 1≤K | TYPING | |
| E | TYPING | |
| K ≥ SAH log₂K | SOURCE | :1697 |
| 0<δ<1 | STANDING | Thm 5.10 domain |
| family (indexed by profile, h=continuation h+1, future code) | SOURCE (X families), generalized: ceiling profile cover (C15) and full strictly-future dependence | :1672–1683 |
| 0 ∈ family | SOURCE | :1675 |
| card ≤ K+1 | SOURCE | :1675 |
| 0 ≤ V ≤ H | SOURCE | :1675 |
| δ′ = δ/(100S²A²H²K²) instead of 100δ/(…) | DISCLOSED | C16 (printed allocation refuted in Lean) |

Counts: SOURCE 5, STANDING 1, TYPING 4, DISCLOSED 1.

**Other checks**
- Level j ↔ l=j+2 gives l ∈ [2, ⌊log₂K⌋+1], matching "l ≤ log₂K+1".
- The batch is at 0-based positions 2^j..2^{j+1}−1, matching the source batch l.
- Denominator `2^(j+2)·log₂K`.
- At K=1, `Fin 0` makes the event trivial. Disclosed, and consistent with the source, which has no levels then.
- The broader profile set and family class make the statement stronger.

**VERDICT: PASS-DISCLOSED.**

## 18. MVP_optimism_corrected — Ch5.lean:577 (wrapper :243)

Source: `eq:optimism-Q-V-geq-mvp`, :1480–1487. Regime :1402–1407. δ′ :1388.

**Reconstruction.** With probability ≥ 1−2SAHKδ′: Qᵏ ≥ Q⋆ and Vᵏ ≥ V⋆ for all (s,a,h,k), for MVP with the same bonus. This is under Lemma 5.5's c-conditions ("repeating Steps 1–2") and the standing regime K ≥ SAHι.

| binder | bin | citation |
|---|---|---|
| types, H/hH, K/hK, E, fallback | TYPING | |
| ρ | STANDING | |
| 0<δ<1 | SOURCE | Thm 5.10 |
| 4≤c₁, c₁²≤c₂ | STANDING | :766 via :1480 |
| SAHι ≤ K | STANDING | :1402–1407 |
| reciprocal δ′ allocation | DISCLOSED | C16 |
| power-of-two trigger | DISCLOSED | C13 |
| zero-count completion, fixed tie | DISCLOSED | C8 (names MVP_optimism_corrected) |

Counts: SOURCE 1, STANDING 4, TYPING 7, DISCLOSED 3.

**Other checks**
- The tables are `onlineMVPHistoryPlanningStages … (history.take(kH))`, i.e. the latest committed batches before episode k.
- V⋆/Q⋆ via `optimalValue/optimalQ`.
- The regime hypothesis is unused by the export (`_hlarge`), so the statement is non-vacuous and the export is stronger.

**VERDICT: PASS-DISCLOSED.**

---

## Summary

| # | Entry | Def line | Verdict |
|---|---|---|---|
| 1 | Lemma5_5_corrected | Ch5.lean:40 | PASS-DISCLOSED |
| 2 | Lemma5_6_corrected | :76 | PASS-DISCLOSED |
| 3 | Lemma5_7_W1_K2_corrected | :116 | PASS-DISCLOSED |
| 4 | Lemma5_7_K2_corrected | :152 | PASS-DISCLOSED |
| 5 | Lemma5_3 | :197 | PASS |
| 6 | Lemma5_4 | :221 | PASS |
| 7 | Lemma5_8_K2_corrected | :243 | PASS-DISCLOSED |
| 8 | Lemma5_9_K2_corrected | :293 | PASS-DISCLOSED |
| 9 | Thm5_2_corrected | :346 | PASS-DISCLOSED |
| 10 | Remark5_5_corrected | :382 | PASS-DISCLOSED |
| 11 | Eq_regret_asymptotic_ucbvi_corrected | :401 | PASS-DISCLOSED |
| 12 | Remark5_9 | :436 | PASS |
| 13 | Remark5_13_corrected | :457 | PASS-DISCLOSED |
| 14 | Lemma5_22_corrected | :473 | PASS-DISCLOSED |
| 15 | Lemma5_11 | :494 | PASS |
| 16 | Lemma5_12_powerOfTwo_corrected | :515 | PASS-DISCLOSED |
| 17 | Lemma5_13_confidence_corrected | :538 | PASS-DISCLOSED |
| 18 | MVP_optimism_corrected | :577 | PASS-DISCLOSED |

Totals: PASS 4, PASS-DISCLOSED 14, FAIL 0, UNSURE 0.

### Non-blocking observations

1. Entries 1, 3 and 4 fix `State Action : Type` (universe 0). This is harmless, since finite types transport, but it is inconsistent with the universe-polymorphic siblings.
2. Entries 3, 4, 7 and 18 carry c₁≥4, c₂≥c₁² from Lemma 5.5. I bin this as STANDING via :777 and :1480. The docstrings for entries 3 and 7 call it the "source bonus domain" without citing :766/:777; adding the citation would help readers.
3. Remark5_13_corrected relies on C8 but is not named in the C8 text, unlike Remark5_5_corrected and others. Adding a one-line mention is suggested.
4. Lemma5_5_corrected's δ≤1 restriction is stated in its docstring. It is STANDING (:395, Thm 5.2), so no SOURCE-ISSUES entry is required.

### Method notes

- No Lean was compiled. Evidence comes from reading the definitions, the statements, the wrappers and the raw `.tex`.
- The axiom closure was not re-run here.
