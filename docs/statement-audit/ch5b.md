> Public copy of an independent five-bin statement audit (2026-11-09/10), scrubbed of local paths and agent identifiers. Auditors were independent of the builders. No result here is author-approved. Method and totals: [README](README.md).

# Five-bin statement audit, batch ch5b (2026-11-09)

Auditor: independent statement auditor (read-only; no Lean compiled, nothing under
Formalization/, docs/, scripts/, site/ edited). Method: BRIEF.md + `skills/lean/skills/lean-statement-audit/SKILL.md`.

Source files read (pinned upstream, read-only):
`source/upstream/tex/chapters/onlineRL.tex` lines 1–145 (protocol, regret, regret-to-PAC), 400–420
(Bernstein bonus, δ′ for UCBVI), 1200–1500 (MVP algorithm `alg:main-mvp` 1256–1310, Theorem 5.10
1339–1352, ι and δ′ 1386–1391, regime K ≥ SAHι 1402–1407, notation 1430–1475, decomposition), 1660–1860
(Assumption, Lemmas 5.13/5.14/5.15, displays T1–T6), 1890–2045 (UCB-Q bonus/learning rate, Thm 5.16,
Alg. 5.4, η_n^N notation, Lemma 5.17), 2077 (ι = log(SAKH/δ)), 2115–2155 (Lemma 5.18), 2436–2460
(Thm 5.19), 2500–2730 (lower-bound construction, Lemmas 5.20, 5.21, Remark 5.12), 4330–4480
(Claim 5.1 and its proof). `source/upstream/tex/chapters/bandits.tex` 1–90 (model, regret,
decomposition), 170–300 (Algorithm 5.1, Theorem 5.1), 383–400 (∞-index convention).

Project definitions expanded (opened and read): `FiniteDistribution` (+`expectation`, `variance`,
`rowMeasure`, `empiricalRow`), `EnvironmentStage` (+`optimalValue`, `optimalQ`, `qBackup`),
`controlled`, `greedyStages`, `greedyAction`; `OnlineEpisodePlanner`, `onlineEpisodicChoose`,
`onlineEpisodicCurrentState`, `onlineMDPSuccessorRowLaw`, `onlineSequentialOutcomeLaw`,
`onlineInitialVectorLaw`, `onlineSequentialEpisodeLaw`, `onlineSequentialPathHistory`,
`OnlineOutcomePath`, `onlineTranscriptRowSequence`, `onlineActualStageRowSequence`,
`onlineRowOutcomes`; MVP: `onlineMVPRowTrigger`, `onlineMVPRowCountState`, `onlineMVPStoredCount`,
`onlineMVPSourceBatchStart/End/List`, `onlineMVPRowVisitList`, `onlineMVPActualPlanningStage`,
`onlineMVPHistoryRowAt/NextAt`, `onlineMVPHistoryPlanningStages`, `onlineMVPCommittedGreedyPlanner`,
`OnlineObservedPlanningStage`, `onlineUniformInitialRow`, `onlineObservedPlanningRow`,
`onlineCappedStageQ`, `onlineZeroCountSafeQUpdate`, `onlineCappedBackwardValue/Q(At)`; Q-learning:
`QLearningChronologicalTable`, `qLearningChronologicalInitial/Value/Policy/Update/Fold`,
`qLearningActualEpisodePlanner`, `qLearningActualSequentialHistory`, `qLearningActualTableAt`,
`qLearningActualVisitEpisodes`, `qLearningTrueOptimalNext/Q`, `qLearningActualRegret`,
`qLearningGreedyTruePolicyValue`, `onlineQRate`, `onlineQRateWeight`, `qLearningSourceOptimismGood`
(library, for the wrapper); lower bound: `onlineLBq`, `stayRow`, `exitRow`, `onlineLBSubStage(s)`,
`BanditLearner`, `banditRewardRow`, `banditEnv`, `compLaw`, `banditNextArmErrorProb`,
`OnlineLearner`, `episodeLaw`, `episodePathLaw`, `onlineHistoryLaw`, `policySuboptimality`,
`onlineExpectedRegret`; bandit: `gaussianNoiseTable`, `ucbIndex`, `ucbArgmax`, `ucbState`,
`ucbArm`, `extendNoise`, `ucbAction`, `GaussianBanditLB.history/armAt/regret`.
`interactionLaw`/`seqLaw` (AdaptiveKL) were not opened line by line; their docstrings describe the
adaptive interaction law and are consistent with the uses checked.

General findings on shared infrastructure (apply to all MVP/Q-learning entries):
- The sequential law is the genuine protocol: iid resets `∏ ρ(s₁ᵏ)`, then chronological successor
  draws from `P_h(·|s,a)` of the row chosen causally from the revealed history; planners see only
  `history.take (k*H)` (completed episodes). `rowMeasure` is the PMF measure with ⊤ σ-algebra, so
  `.real` of every event is its exact mass (no non-measurable junk).
- MVP batches: stored counts after n visits are 1,1,1,2,2,2,2,4,…, and `onlineMVPSourceBatchList`
  slices samples `[stored, 2·stored)` (0-based) for n ≥ 2 and the first sample for n = 1, which is
  exactly the source's `P̂^{(j)}` batch `{2^{j−2}+i}_{i=1}^{2^{j−2}}` (C13 dyadic trigger). Zero
  count: uniform row and Q = H (C8). Q update `min{r+⟨P̂,V⟩+b, H}`, V = max_a Q, terminal 0, cap H,
  bonus `c₁√(Var_{P̂}(V)·L/N) + c₂HL/N` with the same table's continuation: matches 1296–1308 / 407–417.
  Recomputing every episode from retained batches equals recomputing only on triggers (P̂, N
  change only at triggers).
- Q-learning: Q₀ = H, `N ← N+1`, `Q ← (1−η_n)Q + η_n(r + V_{h+1}(s′) + b_n)`, V = min(H, max Q),
  V_{H+1}=0, η_n = (H+1)/(H+n), greedy policy frozen at episode start: matches 1930–1979; nonterminal
  V initialisation and tie rule are the C20 completion.
- `fallback : State` is a totalisation witness used only outside the transcript (row/successor
  extraction past `history.length`, episode starts at index ≥ K); it is universally quantified, so it
  only strengthens the Prop. Binned TYPING.
- The planners `onlineMVPCommittedGreedyPlanner`, `qLearningChronologicalPolicy` are one fixed
  `Classical.choose` maximiser (fixed deterministic tie), disclosed in each docstring (and C8/C13/C20).

Bin legend: SRC = SOURCE, STD = STANDING, TYP = TYPING, DIS = DISCLOSED, EXC = EXCESS.

---

## 1. Lemma5_15_corrected

Def: `Formalization/Statements/Ch5.lean:613`; wrapper `Ch5Proofs.lean:257`.
Source: `lem:bound-T6-ucb-mvp`, onlineRL.tex:1822–1833 (read 1822–1833; ι/δ′ at 1386–1391; regime
1402–1407; T2/W4/T6 definitions 1475–1484, 1754–1773; bonus 407–417; constants "suitably chosen" 1350).

Independent reconstruction: For MVP (Alg. 5.3) with constants c₁,c₂ as suitably chosen in Thm 5.10,
δ′ = 100δ/(S²A²H²K²) (MVP section) and ι = 40000(log₂K)³log(3SAH)log(1/δ′): with probability at least
1 − 4SAHKδ′, T6 := Σ_{k,h} Var_{P_{s_h^k a_h^k h}}(V^k_{h+1}) ≤ 4H·T2 + 4H·W4 + KH²ι, where
T2 = Σ b_h^k(s_h^k,a_h^k), W4 = Σ max{⟨P̂^k − P, V^k_{h+1}⟩, 0}. No explicit premise; context
K ≥ 1, 0<δ<1, standing regime K ≥ SAHι (not required by the lemma's statement).

Binder table:

| binder | Lean type | bin | citation |
|---|---|---|---|
| State, Action | `Type u`, `Type v` | TYP | finite S, A |
| [Fintype State], [Fintype Action] | instances | TYP | finite MDP |
| H, K | ℕ | SRC | horizon, episodes |
| hH : 0 < H | Prop | TYP | H ≥ 1 implicit |
| hK : 0 < K | Prop | STD | Thm 5.10 "K ≥ 1" :1340 |
| E : Fin H → EnvironmentStage (fields: nonempty S, nonempty A, transition, reward ∈ [0,1]) | structure | STD | MDP model :17–25, rewards in [0,1] (prelim) |
| ρ : FiniteDistribution State | structure | STD | protocol (i) :26–31 |
| fallback : State | State | TYP | totalisation, ∀-quantified |
| δ | ℝ | SRC | confidence |
| 0 < δ, δ ≤ 1 | Prop | STD | Thm 5.10 "0<δ<1" (δ ≤ 1 assumes less) |
| c₁, c₂ | ℝ | SRC | bonus constants :1260, 407 |
| 4 ≤ c₁, c₁² ≤ c₂ | Prop | STD | reading of "c₁,c₂ suitably chosen" :1350 (∀ admissible pair) |
| δp := δ/(100S²A²H²K²) | let | DIS | C16 reciprocal allocation (docstring, SOURCE-ISSUES C16, C8 para on Lemma5_15) |
| zero-count Q=H / T2 charge H at N=0 | def body | DIS | C8 (docstring + SOURCE-ISSUES C8) |
| power-of-two trigger | def body | DIS | C13 |
| fixed deterministic tie | def body | DIS | docstring + C8 MVP paragraph |

Counts: SRC 4, STD 6, TYP 5, DIS 4, EXC 0.

Other checks: probability `1 − 4SAHKδp ≤ P` matches "at least". T6/T2/W4 bodies use actual rows
`sa h k` (stage-h row of episode k), `U h k` = V^k_{h+1} from the pre-episode table, stored batch
count as N_h^k. Constants 4H, 4H, KH²I exact. K = 1 (I = 0) is included, not vacuous. Self-contained.
Wrapper applies `mvpActualT6_source_confidence` and unfolds definitions only.

Verdict: **PASS-DISCLOSED**. Minor note: the c₁ ≥ 4, c₁² ≤ c₂ range is not mentioned in the docstring;
it is a legitimate reading of the source's "suitably chosen", but mentioning it would help readers.

## 2. MVP_T2_K2_corrected

Def: `Ch5.lean:660`; wrapper `Ch5Proofs.lean:271`.
Source: `eq:T2-ub-analysis-mvp`, onlineRL.tex:1793–1801 (read 1775–1801).

Reconstruction: in regime K ≥ SAHι, with probability ≥ 1 − (4log₂K)δ′ (jointly with T3, T4),
T2 ≤ ½√(SAH·T5·ι) + ½SAH²ι, T5 = Σ Var_{P̂^k}(V^k_{h+1}), c₁,c₂ suitably chosen.

| binder | Lean type | bin | citation |
|---|---|---|---|
| State, Action, Fintype insts | types | TYP | |
| H, K | ℕ | SRC | |
| hH : 0<H | Prop | TYP | |
| hK : 2 ≤ K | Prop | DIS | C12 (docstring; SOURCE-ISSUES C12, C8 T2/T5 paragraph) |
| E | EnvironmentStage | STD | MDP model |
| initial : Fin K → State, path | data | TYP | statement is pathwise (∀ realisations), stronger than in probability |
| fallback | State | TYP | |
| δ, 0<δ, δ≤1 | | SRC/STD | Thm 5.10 |
| K ≥ SAH·I | Prop | STD | regime :1402–1407 (docstring states it is retained) |
| c₁=4, c₂=16 fixed | let | DIS | "suitably chosen" witnessed (docstring) |
| δp reciprocal, C8 charge, C13, tie | def body | DIS | C16, C8, C13 |

Counts: SRC 3, STD 3, TYP 6, DIS 5, EXC 0.

Other checks: the Lean bound is deterministic (every initial/path), which implies the printed
probability statement. Bonus at positive count uses `Var_{P̂}(U)`, H·L/N; zero count charges H (C8).
I > 0 is attainable (K ≥ 2, S,A,H ≥ 1), regime satisfiable for large K: not vacuous. Wrapper applies
`mvpActualT2_le_sourceBound_fixed` (it does not use the regime premise; the entry keeps it as standing).

Verdict: **PASS-DISCLOSED**.

## 3. MVP_T5_corrected

Def: `Ch5.lean:704`; wrapper `Ch5Proofs.lean:286`.
Source: `eq:T5-ub-analysis-mvp`, onlineRL.tex:1804–1810.

Reconstruction: with probability ≥ 1 − 2δ′log(KH): T5 ≤ W3 + 2H·T2 + √(H²·T6·ι) + KH²ι,
W3 = Σ⟨P̂^k − P, (V^k_{h+1})²⟩; regime K ≥ SAHι; c's suitably chosen.

| binder | Lean type | bin | citation |
|---|---|---|---|
| State, Action, insts | | TYP | |
| H, K | ℕ | SRC | |
| hH | 0<H | TYP | |
| hK | 0<K | STD | K ≥ 1 |
| E, ρ | | STD | model, protocol |
| fallback | | TYP | |
| δ, 0<δ, δ≤1 | | SRC/STD | |
| K ≥ SAH·I | Prop | STD | :1402–1407 |
| c=(4,16) | | DIS | docstring |
| δp, C8, C13, tie | | DIS | C16, C8, C13 |

Counts: SRC 3, STD 5, TYP 4, DIS 5, EXC 0.

Other checks: `1 − 2·log(K·H)·δp ≤ P` matches the printed natural-log coefficient; W3 term uses
expectations of squares under P̂ and P; T2 is the (4,16) bonus sum with C8 charge. Wrapper applies
`mvpActualT5_source_confidence`. Verdict: **PASS-DISCLOSED**.

## 4. MVP_T234_K2_corrected

Def: `Ch5.lean:757`; wrapper `Ch5Proofs.lean:301`.
Source: `eq:T2/T3/T4-ub-analysis-mvp`, onlineRL.tex:1793–1802; T3/T4 definitions in
`eq:decomposition-mvp` 1478–1484.

Reconstruction: with probability ≥ 1 − (4log₂K)δ′, simultaneously T2 ≤ ½√(SAHT5ι)+½SAH²ι,
|T3| ≤ √(T6ι)+Hι with T3 = Σ⟨P − e_{s_{h+1}^k}, V^k_{h+1}⟩, and |T4| ≤ √(KH²ι) with
T4 = Σ_k(Σ_h r_h(s_h^k,a_h^k) − V^{π^k}_1(s_1^k)).

| binder | Lean type | bin | citation |
|---|---|---|---|
| State, Action, insts | | TYP | |
| H, K | ℕ | SRC | |
| hH | | TYP | |
| 2 ≤ K | | DIS | C12 |
| E, ρ | | STD | |
| fallback | | TYP | |
| δ, 0<δ, δ≤1 | | SRC/STD | |
| K ≥ SAH·I | | STD | :1402–1407 |
| c=(4,16), δp, C8, C13, tie | | DIS | docstring, C16/C8/C13 |

Counts: SRC 3, STD 4, TYP 4, DIS 5, EXC 0.

Other checks: `next h k` is the realised successor s_{h+1}^k at transcript index kH+h; T4's policy
value is the true trajectory value of the deployed `planner (history.take (k*H))`; probability
`1 − 4(log K/log 2)δp ≤ P` matches. One joint event as printed. Wrapper applies
`mvpActualT234_source_confidence_K2` (strict, weakened by `.le`) plus proved rewriting lemmas
`mvpT234_T3_eq_expanded`, `mvpT234_T4_eq_expanded` (bridges, not a second proof).
Verdict: **PASS-DISCLOSED**.

## 5. MVP_regret_corrected

Def: `Ch5.lean:822`; wrapper `Ch5Proofs.lean:350`.
Source: Theorem 5.10 `thm-mvp-regret`, onlineRL.tex:1339–1352.

Reconstruction: ∀K ≥ 1, 0<δ<1: with probability ≥ 1−δ, MVP with suitably chosen universal c₁,c₂
achieves Regret(K) = Σ_k(V⋆_1(s_1^k) − V^{π^k}_1(s_1^k)) ≤ Õ(min{√(SAH³K), HK}); the hidden constant
and polylog are universal (do not depend on the instance beyond logs).

| binder | Lean type | bin | citation |
|---|---|---|---|
| ∃ C, 0<C (outermost) | ℝ | SRC | Õ constant, universal: correct scope (before all instance data) |
| State, Action, insts | | TYP | |
| H, K | ℕ | SRC | |
| hH | 0<H | TYP | |
| 0<K | | SRC | "K ≥ 1" |
| E, ρ | | STD | |
| δ, 0<δ, δ<1 | | SRC | |
| ∃ c₁ c₂ = 4, 16 | | SRC | "suitably chosen" (existential, fixed universal values) |
| fallback := Classical.choice | let | TYP | |
| polylog factor `max 1 I` | conclusion | SRC | Õ reading; I is polylog in S,A,H,K,1/δ |
| δp reciprocal, C8, C13, tie, C15/C17 proof repairs | def body | DIS | docstring; C8, C13, C16, C17, C48 |

Counts: SRC 7, STD 1, TYP 4, DIS 1 (bundle of C8/C13/C16/tie), EXC 0.

Other checks: V⋆ = trajectory value of `greedyStages` (optimal greedy policy), V^{π^k} = true value of
the deployed policy from the completed pre-episode history; `1 − δ ≤ P`. K = 1 not vacuous
(bound C·H). Wrapper is `exact mvpSourceRegretCorrected_holds` (library Prop, definitionally equal).
Verdict: **PASS-DISCLOSED**.

## 6. Lemma5_14_corrected

Def: `Ch5.lean:857`; wrapper `Ch5Proofs.lean:355`.
Source: `lemma:decouple`, onlineRL.tex:1722–1744.

Reconstruction: premise K ≥ SAH log₂K; with probability exceeding 1−δ′:
T1 ≤ W4 ≤ √(SAHι·T6) + SAH²ι and W3 ≤ √(SAH³ι·T6) + SAH³ι.

| binder | Lean type | bin | citation |
|---|---|---|---|
| State, Action, insts | | TYP | |
| H, K | | SRC | |
| hH | | TYP | |
| hK : 0<K | | STD | |
| E, ρ | | STD | |
| fallback | | TYP | |
| δ, c₁, c₂ | ℝ | SRC | |
| 0<δ, δ≤1 | | STD | |
| 4 ≤ c₁, c₁² ≤ c₂ | | STD | "suitably chosen" :1350 |
| SAH·(log K/log 2) ≤ K | | SRC | :1723 |
| δp, C8, C13, C15, C16, C17, tie | | DIS | docstring, SOURCE-ISSUES C8/C13/C15/C16/C17 |

Counts: SRC 4, STD 5, TYP 4, DIS 1 (bundle), EXC 0.

Other checks: with d = SAH, `√(d·I·T6) + d·H·I` = √(SAHι T6)+SAH²ι and `√(d·H²·I·T6)+d·H²·I` =
√(SAH³ιT6)+SAH³ι; strict `1 − δp < P`; T1 ≤ W4 included. Wrapper applies
`mvp_actualDecouplingEvent_sourceConfidence` with cardinality/log rewriting only.
Verdict: **PASS-DISCLOSED**.

## 7. Claim5_1_corrected

Def: `Ch5.lean:935`; wrapper `Ch5Proofs.lean:388`.
Source: `claim:PV-l-UB`, onlineRL.tex:4340–4353 (context: proof of Lemma 5.14, premises of Lemma 5.14,
P̂^{(l)} definition 1465–1472).

Reconstruction: with probability exceeding 1−δ′, for all l = 1..log₂K and j = 1..2^{l−1}:
Σ_{s,a,h}⟨P̂^{(l)}_{s,a,h} − P_{s,a,h}, V^{k_{l,j,s,a,h}}_{h+1}⟩ ≤ √(SAHι/(2^l log₂K)·Σ Var_P(V^{k_{l,j,s,a,h}}_{h+1}))
+ SAH²ι/(2^l log₂K), where k_{l,j,s,a,h} is the episode of the (2^{l−1}+j)-th visit (V = 0 if none).

| binder | Lean type | bin | citation |
|---|---|---|---|
| State, Action, insts | | TYP | |
| H, K | | SRC | |
| hH | | TYP | |
| hK | | STD | |
| E, ρ | | STD | |
| fallback | | TYP | |
| δ, c₁, c₂ | | SRC | |
| 0<δ, δ≤1, 4≤c₁, c₁²≤c₂ | | STD | Thm 5.10 / "suitably chosen" |
| SAH log₂K ≤ K | | SRC | inherited premise of Lemma 5.14 :1723 (docstring states it) |
| ∀ l (1 ≤ l ≤ log₂K), ∀ j (1..2^{l−1}) | conclusion | SRC | :4352 |
| δp, C8, C13, C15, C17, tie | | DIS | docstring; SOURCE-ISSUES C16 Claim 5.1 note (line 1651), C8, C13, C15, C17 |

Counts: SRC 5, STD 4, TYP 4, DIS 1 (bundle), EXC 0.

Other checks: `cnt h k = 2^{l−1}+j−1` selects the unique episode of the (2^{l−1}+j)-th visit of
(h, s_h^k, a_h^k); unvisited triples contribute 0 (source's V = 0 convention). `Phat l h k` reads
zero-based visits 2^{l−2}..2^{l−1}−1 (l ≥ 2) or visit 0 (l = 1, ℕ subtraction gives 2^0 = 1), which
is exactly the l-th batch; all those visits precede the (2^{l−1}+j)-th, so the fallback is never
read on the selected terms. RHS factors exact. Strict probability. l = 1 is covered (more than
the printed proof establishes; disclosed). Wrapper `exact claimPV_eventConfidence …`.
Verdict: **PASS-DISCLOSED**.

## 8. Lemma5_18_restricted

Def: `Ch5.lean:990`; wrapper `Ch5Proofs.lean:392`.
Source: `lemma:opt_model_free`, onlineRL.tex:2121–2150; ι = log(SAKH/δ) at :2077; bonus :1890–1893.

Reconstruction: Suppose c_b large enough. W.p. ≥ 1−δ, ∀(s,a,h,k): 0 ≤ (Q^k_h − Q⋆_h)(s,a) ≤ η_0^t H +
Σ_{i=1}^t η_i^t (V^{k_i}_{h+1} − V⋆_{h+1})(s^{k_i}_{h+1}) + β_t, with β_0 = 0, β_t ≤ C√(H³ι/t)
(C absolute); then w.p. > 1−δ, Q^k ≥ Q⋆ and V^k ≥ V⋆. t = N_h^k(s,a) (visits before episode k),
k_1<…<k_t those episodes.

| binder | Lean type | bin | citation |
|---|---|---|---|
| State, Action, insts | | TYP | |
| H, K | | SRC | |
| hH | | TYP | |
| hK | | STD | Thm 5.16 "K ≥ 1" |
| E, ρ | | STD | |
| fallback | | TYP | |
| δ, 0<δ, δ<1 | | SRC | Thm 5.16, :1893 |
| L = log(SAHK/δ) | let | SRC | ι :2077 |
| bonus with c_b = 2 | let | DIS | "c_b large enough" witnessed by 2 (docstring; C20 "preserve the algorithm's bonus 2√(H³log(SAT/δ)/n)") |
| β_t := 8√(H³L/t), β_0 = 0 (C = 8) | let/conclusion | SRC | existential β, C absolute: explicit witness |
| V init = min(H, max Q), fixed tie | def body | DIS | C20 |

Counts: SRC 5, STD 3, TYP 4, DIS 2, EXC 0.

Other checks: visit list = earlier episodes e < k with row (h,s,a) at index eH+h (zero-based);
V^{k_i}_{h+1} is the table at the start of episode k_i evaluated at the realised s^{k_i}_{h+1}, which
is the value actually used in that update (stage h+1 not yet updated within the episode); η_0^t,
η_i^t = `onlineQRateWeight` (checked against :1995–2010). Optimism of V at all stages included.
Strict probability (stronger). The `(beta 0 = 0 ∧ …)` conjunct is a tautology of the let (harmless).
Wrapper applies `qLearning_sourceOptimism_confidence … 2 … (by norm_num)` and unfolds.

Note (not a failure): the library export holds for every c_b ≥ 2 with β constant 4c_b; the index
fixes c_b = 2. If "c_b large enough" is read as ∀ c_b ≥ c₀, the entry states less than both the
printed reading and the export. The docstring says "witnessed by c_b = 2", so the choice is visible;
recommend restating as `∀ cb ≥ 2` with residual `4·cb·√(H³L/t)` (the export supports it), or naming
the existential reading explicitly in C20.

Verdict: **PASS-DISCLOSED** (with the note above).

## 9. Thm5_16_corrected

Def: `Ch5.lean:1028`; wrapper `Ch5Proofs.lean:397`.
Source: `thm-ucbq-regret`, onlineRL.tex:1911–1922.

Reconstruction: ∀K ≥ 1, 0<δ<1, c_b suitably chosen: w.p. ≥ 1−δ, Regret(K) ≤ Õ(√(SAH⁵K)).

| binder | Lean type | bin | citation |
|---|---|---|---|
| State, Action, insts | | TYP | |
| H, K | | SRC | |
| hH | | TYP | |
| hK | | SRC | K ≥ 1 |
| E, ρ | | STD | |
| fallback | | TYP | |
| δ, hδ, hδ1 | | SRC | |
| bonus c_b = 2, L | let | SRC | "c_b suitably chosen" (∃) |
| explicit rate max(1,19e)√(H⁵SAKΛ), Λ = 1+log(4SAT/δ) | conclusion | DIS | Õ made explicit; docstring + C20 |
| V init, fixed tie | def body | DIS | C20 |

Counts: SRC 5, STD 1, TYP 4, DIS 2, EXC 0.

Other checks: regret = Σ_k (V⋆_1 − V^{π^k}_1)(s_1^k) with π^k the greedy policy frozen from the table
at kH; constant universal, Λ polylog; strict probability. Wrapper `exact qLearning_actualRegret_rate_confidence`.
Verdict: **PASS-DISCLOSED**.

## 10. Lemma5_17

Def: `Ch5.lean:1047`; wrapper `Ch5Proofs.lean:401`.
Source: `lemma:property_lr`, onlineRL.tex:2020–2041; η_n :1898–1904; η_n^N, η_0^N :1995–2010.

Reconstruction: ∀N ≥ 1: 1/√N ≤ Σ_{n=1}^N η_n^N/√n ≤ 2/√N and Σ(η_n^N)² ≤ 2H/N; ∀n ≥ 1:
Σ_{N≥n} η_n^N = 1 + 1/H.

| binder | Lean type | bin | citation |
|---|---|---|---|
| H | ℕ | STD | horizon of the chapter |
| 0 < H | Prop | TYP | H ≥ 1 |
| N, 0<N | | SRC | "every integer N ≥ 1" |
| n, 0<n | | SRC | "every integer n ≥ 1" |

Counts: SRC 2, STD 1, TYP 1, DIS 0, EXC 0.

Other checks: `onlineQRateWeight` matches η_n^N case split (empty product gives the N = n case);
the tail series is `HasSum (k ↦ η_n^{n+k}) (1+1/H)`, a genuine convergent-sum statement. Wrapper
assembles three library lemmas. Verdict: **PASS**.

## 11. Lemma5_20

Def: `Ch5.lean:1068`; wrapper `Ch5Proofs.lean:409`.
Source: `lem:Vh-star-Vhpi-gap-lower-bound-online-final`, onlineRL.tex:2654–2668; construction
2512–2650.

Reconstruction: H ≥ 2; ∀M_i ∈ C^sub (two states, r(1,·)=1, r(0,0)=0, 0 absorbing,
P(0|1,a) = q_{i_h}(a), 0<ε₀≤H/2), ∀ policy π: V⋆_1(1) − V^π_1(1) ≥ Σ_h ε₀(H−h)/(16H²)(1 − π_h(i_h|1)).

| binder | Lean type | bin | citation |
|---|---|---|---|
| H, A | ℕ | SRC/TYP | |
| hH : 2 ≤ H | | SRC | :2659 |
| ε, 0<ε, ε ≤ H/2 | | STD | construction range :2602 |
| i : Fin H → Fin A | | SRC | M_i, i ∈ [A]^H |
| π : ℕ → StationaryPolicy (Fin 2) (Fin A) | | SRC | every (Markov, randomized, nonstationary) policy |

Counts: SRC 4, STD 1, TYP 1 (A), DIS 0, EXC 0.

Other checks: `onlineLBq` reproduces `eqn:prob-astar-a-1` with arm 1 = index 0; stage rewards/
transitions match; state 0's action set is Fin A with identical actions (equivalent to a singleton);
0-based h gives weight (H − (h+1)). V⋆ = backward-induction optimum, V^π actual trajectory value.
Wrapper is the library theorem verbatim. Verdict: **PASS**.

## 12. Lemma5_21

Def: `Ch5.lean:1087`; wrapper `Ch5Proofs.lean:411`.
Source: `lem:online-lb-testing`, onlineRL.tex:2709–2721; bandit family 2683–2704.

Reconstruction: A ≥ 3, H ≥ 2, 0<ε₀≤H/2, t ≤ H³A/(18ε₀²): inf over algorithms of
(1/A)Σ_i P_{B_i}(a_{t+1} ≠ i) ≥ 1/3, rewards Bernoulli(1 − q_i(a)).

| binder | Lean type | bin | citation |
|---|---|---|---|
| A, H | ℕ | SRC | |
| 3 ≤ A, 2 ≤ H | | SRC | |
| ε, 0<ε, ε≤H/2 | | SRC | |
| t, t ≤ H³A/(18ε²) | | SRC | |
| L : BanditLearner A (finite seed + history-dependent randomized policy) | | SRC | "∀ algorithm" (class ⊇ printed seedless class) |

Counts: SRC 5, STD 0, TYP 0, DIS 0, EXC 0.

Other checks: `banditNextArmErrorProb` = seed-average of P(arm drawn at round index t after t rounds ≠ i)
under the adaptive interaction law with `banditEnv` (Bernoulli 1 − q_i(a)). Wrapper verbatim.
Verdict: **PASS**.

## 13. Thm5_19

Def: `Ch5.lean:1108`; wrapper `Ch5Proofs.lean:413`.
Source: `thm:minimax-lower-online`, onlineRL.tex:2443–2456.

Reconstruction: ∃ universal c₀ > 0: ∀S ≥ 2, A ≥ 3, H ≥ 2, K ≥ 1, ∃ family C_mdp (S states, ≤ A
actions, horizon H) and ρ with inf_alg sup_{M∈C} E_M[Σ_k(V⋆_1(ρ) − V^{π^k}_1(ρ))] ≥ c₀min{√(H³SAK), HK};
π^k depends on trajectories before episode k only.

| binder | Lean type | bin | citation |
|---|---|---|---|
| ∃ c₀, 0<c₀ (outermost) | | SRC | universal constant, correct scope |
| S, A, H, K and 2≤S, 3≤A, 2≤H, 1≤K | | SRC | :2445 |
| ∃ I finite, E : I → stages, ρ | | SRC | ∃ family and ρ |
| ∀ L : OnlineLearner, ∃ i | | SRC | inf–sup written ∀L ∃i (implies inf sup ≥) |

Counts: SRC 4 groups, EXC 0.

Other checks: `OnlineLearner` = finite seed plus π^k a randomized Markov policy depending on previous
episodes (states/actions; rewards are state-determined and known for the fixed family). This class
contains the printed (seedless) algorithm class, so the Prop is at least as strong. Expected regret
averages seed and history law with s_1^k ∼ ρ independently. Exactly A actions per state meets "at most A".
Wrapper verbatim. Verdict: **PASS**.

## 14. Eqn_regret_decomposition_ucb

Def: `Ch5.lean:1123`; wrapper `Ch5Proofs.lean:445`.
Source: `eq:regret_bandit` and `eqn:regret-decomposition-ucb`, bandits.tex:58–82.

Reconstruction: Regret(T) = Tr⋆ − Σ_t r(a_t) = Σ_t Δ(a_t) = Σ_a Δ(a)N_T(a), and Regret ≥ 0.

| binder | Lean type | bin | citation |
|---|---|---|---|
| 𝒜, [Fintype], [DecidableEq] | | TYP | finite arm set |
| r : 𝒜 → ℝ | | SRC | means (printed [0,1] dropped: assumes less) |
| T, arm : Fin T → 𝒜 | | SRC | any realised arm sequence |

Counts: SRC 2, TYP 3, EXC 0.

Other checks: `⨆ a, r a` on a nonempty finite type is the max; if 𝒜 is empty then T = 0 is forced
and all sides are 0, so no junk. Verdict: **PASS**.

## 15. Thm5_1_restricted

Def: `Ch5.lean:1151`; wrapper `Ch5Proofs.lean:415`.
Source: `thm:bandit-pure-ucb`, bandits.tex:258–277; Algorithm 5.1 :207–251; ∞ convention :387.

Reconstruction: 0<δ<1, T ≥ A ≥ 2, r(a) ∈ [0,1], N(0,1) iid noise: UCB with index
r̄(a)+√(2log(T²/δ)/N(a)) satisfies E[Regret] ≤ 8√(AT log(T²/δ)) and ≤ 10 log(T²/δ)Σ_{Δ>0}1/Δ(a).

| binder | Lean type | bin | citation |
|---|---|---|---|
| A, T | ℕ | SRC | |
| r, ∀a r a ∈ [0,1] | | SRC | :14 |
| δ, 0<δ, δ<1 | | SRC | |
| 2 ≤ A, A ≤ T | | SRC | |
| tie : ℕ → Finset → Fin A, tie t s ∈ s | | DIS | argmax choice unspecified :232; restricted to round/argmax-set rules (docstring, scope disclosures) |

Counts: SRC 4, DIS 1, EXC 0.

Other checks: noise table iid N(0,1); unpulled index ⊤; integrability proved as extra conclusion;
both bounds and constants unchanged. Wrapper verbatim. Verdict: **PASS-DISCLOSED**.

## 16. Remark5_12_lowerBound

Def: `Ch5.lean:1184`; wrapper `Ch5Proofs.lean:419`.
Source: Remark 5.12, onlineRL.tex:2725–2729 (informal); bandit model bandits.tex:3–48, :296.

Reconstruction (formal reading): the Lemma 5.21 argument with Gaussian KL gives an Ω(√(AT)) minimax
lower bound for the Gaussian bandit; no constant or range printed.

| binder | Lean type | bin | citation |
|---|---|---|---|
| A, T, 2≤A, A≤T | | STD | Theorem 5.1's range (remark compares with it) |
| ∃ μ family in [0,1]^A (before learner) | | SRC | fixed-family inf–sup form |
| Seed : Type, MeasurableSpace, ν probability | | TYP | universe-0 seed disclosed in docstring and scope disclosures |
| arm maps, measurability | | TYP | needed for the expectation to exist (disclosed) |
| constant 1/16 | conclusion | SRC | Ω(·) witnessed |

Counts: SRC 2, STD 1, TYP 2, EXC 0.

Other checks: regret = pseudo-regret with ⨆ over means; integrability is a conclusion, so the
integral is not a junk value. Unsuffixed entry for an informal remark; all choices are visible in the
docstring and in SOURCE-ISSUES scope disclosures. Wrapper verbatim. Verdict: **PASS**.

## 17. Remark5_12_restricted

Def: `Ch5.lean:1214`; wrapper `Ch5Proofs.lean:422`.
Source: as 16, plus Theorem 5.1.

Reconstruction (formal reading): UCB is minimax optimal up to log factors: its worst-case regret is
within a polylog factor of the best achievable worst-case regret.

| binder | Lean type | bin | citation |
|---|---|---|---|
| A, T, δ, 2≤A≤T, 0<δ<1 | | SRC/STD | Thm 5.1 premises |
| tie rule | | DIS | inherits Thm5_1_restricted scope (docstring, scope disclosures) |
| ∃ μ, ∀ learner (Seed : Type, measurable arms), ∃ i | | SRC/TYP | as in 16 |
| factor 128√L | conclusion | SRC | 8√(ATL) / ((1/16)√(AT)) |

Counts: SRC 3, STD 1, TYP 2, DIS 1, EXC 0.

Other checks: L > 0 since T ≥ 2, δ < 1; UCB integrability included. Verdict: **PASS-DISCLOSED**.

## 18. Eq_PAC_from_regret_conversion_corrected

Def: `Ch5.lean:1250`; wrapper `Ch5Proofs.lean:426`.
Source: `eq:PAC-from-regret-conversion`, `eq:uniform-policy-pihat`, onlineRL.tex:113–141; protocol 17–41.

Reconstruction: if for any MDP with S,A,H, E[Regret(K)] ≤ C_{S,A,H}K^{1−α} (α ∈ [0,1]), and π̂ ∼ Unif(π¹..π^K),
then w.p. ≥ 1−δ, V⋆_1(ρ) − V^{π̂}_1(ρ) ≤ C_{S,A,H+1}K^{−α}δ^{−1}.

| binder | Lean type | bin | citation |
|---|---|---|---|
| State, Action, insts | | TYP | |
| Seed, Fintype Seed, ν | | DIS | finite internal randomness (docstring, scope disclosures, C46) |
| H, K, hH, 0<K | | SRC/TYP | |
| E, ρ | | STD | |
| fallback | | TYP | |
| planner : Seed → OnlineEpisodePlanner (deterministic Markov given seed+history) | | DIS | randomized π^k not covered (docstring, C46 scope) |
| C, α, δ; 0≤α≤1, 0<δ | | SRC | |
| regret hypothesis at the instance only | Prop | SRC | weaker than printed "for any MDP" (assumes less) |
| conclusion constant C (not C_{S,A,H+1}) | | DIS | C46 (printed constant refuted in Lean) |

Counts: SRC 4, STD 1, TYP 3, DIS 3, EXC 0.

Other checks: π̂ probability written as seed- and J-average of (1/K)Σ_k P(...): correct joint law
with J uniform and independent. Regret hypothesis forces C ≥ 0 (regret ≥ 0), so not vacuous.
Wrapper verbatim. Verdict: **PASS-DISCLOSED**.

## 19. Eq_PAC_from_regret_conversion_restricted

Def: `Ch5.lean:1286`; wrapper `Ch5Proofs.lean:429`.
Source: as 18.

| binder | Lean type | bin | citation |
|---|---|---|---|
| State, Action, insts | | TYP | |
| Seed, ν H K finite | | DIS | finite seed (C46 scope) |
| alg H K reward ω (sees H, K, known reward, seed) | | SRC | algorithm input :1260-type, known reward :20 |
| C : ℕ→ℕ→ℕ→ℝ, α ∈ [0,1] | | SRC | |
| ∀H, C_{S,A,H} ≤ C_{S,A,H+1} | Prop | DIS | added monotonicity premise (docstring, C46) |
| regret hypothesis ∀ H, K>0, E, ρ on the carriers | Prop | SRC | "for any MDP with S states, A actions, horizon H" |
| H, K, E, ρ, δ, 0<δ | | SRC/STD | |
| deterministic Markov deployed policies | | DIS | C46 scope |

Counts: SRC 5, STD 1, TYP 1, DIS 3, EXC 0.

Other checks: conclusion uses the printed C_{S,A,H+1}. The monotonicity premise is necessary (C46
refutation is Lean-checked). Wrapper verbatim. Verdict: **PASS-DISCLOSED**.

---

## Summary

| # | Entry | Def line | Verdict |
|---|---|---|---|
| 1 | Lemma5_15_corrected | Ch5.lean:613 | PASS-DISCLOSED |
| 2 | MVP_T2_K2_corrected | :660 | PASS-DISCLOSED |
| 3 | MVP_T5_corrected | :704 | PASS-DISCLOSED |
| 4 | MVP_T234_K2_corrected | :757 | PASS-DISCLOSED |
| 5 | MVP_regret_corrected | :822 | PASS-DISCLOSED |
| 6 | Lemma5_14_corrected | :857 | PASS-DISCLOSED |
| 7 | Claim5_1_corrected | :935 | PASS-DISCLOSED |
| 8 | Lemma5_18_restricted | :990 | PASS-DISCLOSED (note: c_b fixed to 2) |
| 9 | Thm5_16_corrected | :1028 | PASS-DISCLOSED |
| 10 | Lemma5_17 | :1047 | PASS |
| 11 | Lemma5_20 | :1068 | PASS |
| 12 | Lemma5_21 | :1087 | PASS |
| 13 | Thm5_19 | :1108 | PASS |
| 14 | Eqn_regret_decomposition_ucb | :1123 | PASS |
| 15 | Thm5_1_restricted | :1151 | PASS-DISCLOSED |
| 16 | Remark5_12_lowerBound | :1184 | PASS |
| 17 | Remark5_12_restricted | :1214 | PASS-DISCLOSED |
| 18 | Eq_PAC_from_regret_conversion_corrected | :1250 | PASS-DISCLOSED |
| 19 | Eq_PAC_from_regret_conversion_restricted | :1286 | PASS-DISCLOSED |

Totals: PASS 6, PASS-DISCLOSED 13, FAIL 0, UNSURE 0.

Advisory (no verdict change):
1. Lemma5_18_restricted fixes c_b = 2 although the export proves every c_b ≥ 2 (residual 4c_b). If
   "c_b large enough" means ∀ c_b ≥ c₀, the entry is narrower than both. Restate as ∀ cb ≥ 2, or name
   the existential reading in C20.
2. Lemma5_15_corrected, Lemma5_14_corrected and Claim5_1_corrected quantify over c₁ ≥ 4, c₁² ≤ c₂
   (a reading of "suitably chosen"); only Claim5_1's docstring mentions it. Add it to the other two.
3. MVP_T2/T5/T234 keep the regime K ≥ SAH·I as a premise that their exports do not use; this matches
   the source's standing regime and is fine. It could be dropped to state more.

Not done: no Lean elaboration or `#print axioms` (reading-only audit, per brief). `interactionLaw`,
`seqLaw` and the library proofs themselves were not audited.

---

## Re-audit after fix (2026-11-09)

Scope: Lemma5_18_restricted only (fix log the fix log (local, not published)); docstring
citations for Lemma5_14_corrected / Lemma5_15_corrected spot-checked. Read-only; nothing compiled.

Lemma5_18_restricted, now at `Formalization/Statements/Ch5.lean:1003`; wrapper `Ch5Proofs.lean:392`.
Source re-read: onlineRL.tex:2121–2150 (lemma), :2077 (ι), :1890–1893 (bonus).

Change: `∀ cb : ℝ, 2 ≤ cb →` after `0 < δ → δ < 1 →`; bonus `cb·√(H³L/i)`; β_t = `4·cb·√(H³L/t)`
(β_0 = 0). The rest of the body is unchanged from the first audit.

| binder | Lean type | bin | citation |
|---|---|---|---|
| State, Action, Fintype insts | | TYP | |
| H, K | ℕ | SRC | |
| hH : 0<H | | TYP | |
| hK : 0<K | | STD | Thm 5.16 "K ≥ 1" |
| E, ρ | | STD | MDP model, protocol |
| fallback | State | TYP | totalisation, ∀-quantified |
| δ, 0<δ, δ<1 | | SRC | :1893, Thm 5.16 |
| cb, 2 ≤ cb | ℝ, Prop | SRC | "c_b large enough" :2122, read as ∀ c_b ≥ c₀ with c₀ = 2 |
| L = log(SAHK/δ) | let | SRC | ι :2077 |
| β_t = 4cb√(H³L/t), β_0 = 0 | let/conclusion | SRC | "β_t ≤ C√(H³ι/t)"; C = 4cb depends only on the universal constant c_b |
| V init = min(H, max Q), fixed tie | def body | DIS | C20 (docstring; SOURCE-ISSUES C20 now states c_b ≥ 2, residual 4c_b) |

Counts: SRC 6, STD 3, TYP 4, DIS 1, EXC 0.

Quantifier order: cb is universally quantified after the instance data, and β is a let that depends
only on (H, L, cb). It does not depend on k, r or the sample, so "C absolute (given c_b)" is
respected. The `beta 0 = 0 ∧ …` conjunct remains a harmless tautology. The premise 2 ≤ cb is
satisfiable, so the Prop is not vacuous.

Wrapper: `intro … cb hcb; have h := qLearning_sourceOptimism_confidence H K hH hK E ρ fallback δ cb
hδ hδ1 hcb; simpa only [qLearningSourceOptimismGood, qLearningSourceBeta] using h`. It only applies
the export; `qLearningSourceBeta` (ActualErrorAll.lean:10) is literally `if t=0 then 0 else
4*cb*√(H³L/t)`, which matches the index let.

Docstring is accurate: "covered for every c_b ≥ 2, with residual constant 4c_b".

The previous advisory 1 is resolved. Verdict: **PASS-DISCLOSED**.

Side check of advisory 2: the Lemma5_15_corrected docstring (Ch5.lean:622) and the Lemma5_14_corrected
docstring (Ch5.lean:868) now cite onlineRL.tex:766 and :777. Line 766 prints exactly "c₁ ≥ 4 and
c₂ ≥ c₁²" (Lemma `lemma:opt`), and line 777 makes all later analysis run on that event. The c-range
is therefore a printed standing assumption: STANDING with an exact citation. Advisory 2 is resolved.
