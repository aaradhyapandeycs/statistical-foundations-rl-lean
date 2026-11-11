> Public copy of an independent five-bin statement audit (2026-11-09/10), scrubbed of local paths and agent identifiers. Auditors were independent of the builders. No result here is author-approved. Method and totals: [README](README.md).

# Five-bin statement audit — batch ch7a (2026-11-09)

Auditor: independent statement auditor (no authorship of the audited entries).
Targets: 20 entries in `Formalization/Statements/Ch7.lean` with wrappers in
`Formalization/Statements/Ch7Proofs.lean`.

Source read (raw `.tex`, pinned tree `source/upstream/tex/chapters/`; SHA-256 prefixes):
`robust_RL.tex` 95ce19a9…, `federated_RL.tex` c9df1d9f…, `marl.tex` 8fadfab2…,
`inference.tex` 82707713… (matches the C47 pin), `intro.tex` 6bfa41c0….
Ranges read: robust_RL.tex:1–160 (model, standing σ>0 at :37–38, rewards in [0,1], 0<γ<1 at :22),
:200–480 (DRVI, Lemma 7.1, Thms 7.2–7.5, Remarks 7.1–7.2); federated_RL.tex:15–250
(FedSynQ, Thm 7.9, generic algorithm, Thm 7.10); marl.tex:20–70, :320–345, :470–510;
inference.tex:40–213; intro.tex:215–236 (TV, χ²). The reconstructions below were made from
the `.tex` before reading the docstrings and SOURCE-ISSUES.

Project definitions opened and expanded: `MDP/CoreDefinitions.lean` (`FiniteDistribution`,
`DiscountedMDP` – reward∈[0,1], 0≤γ<1, nonempty S/A bundled; `StationaryPolicy`),
`RobustRL/LowerBounds/Ch7Definitions.lean` (`tvBall`, `chiBall`, `RobustAdmissible`,
`robustPolicyValue` = sInf of actual trajectory values over rectangular admissible kernels,
`robustOptimalValue` = sSup over stationary randomized policies, `…At`, `drviIterate`
(Q̂₀=0), `empiricalDRVI`, `IsGreedy`, `detPolicy`), `Generative/ModelBasedDefinitions.lean`
(`Samples`, `samplingLaw` = genuine product of nominal rows, `empiricalModel` keeps reward and
γ), `ModelFree/QLearningRobustDefinitions.lean` (`qChiSquared`, `qChiBall` with q≪p),
`MultiAgent/LowerBound/PrintedStatement.lean` + `MultiAgent/LowerBound/Definitions.lean` (`MarkovGame`, `JointPolicy`, `deviate`,
`valueJ`, `bestResponseValueJ`, `gapJ`, `Query`, `genEnv`, `zeroSumAdm`, `constSumAdm`),
`Probability/AdaptiveKLDefinitions.lean` (`interactionLaw`), `Federated/Sync/PrintedStatement.lean`
(`greedyValue`, `localUpdate`, `fedStep`, `fedRun`, `fedOutput`), `Federated/LowerBound/GenericAlgorithmDefinitions.lean`
(`batchUpdate`, `genericStep`, `genericRun`, `genericOutput`, `fedSamplingLaw`,
`fedSamplesExtend`, `supError`), `TDInference/Definitions.lean` (all objects), 
`MDP/FixedPointDefinitions.lean` (`optimalityFixedPoint` via proved ∃!),
`MDP/DiscountedFiniteTrajectory.lean` (`valueFixedPoint` via proved ∃!),
`Probability/FiniteSampleDefinitions.lean` (`rowMeasure` = PMF measure).
No fallback/junk definition was found in these bodies except the disclosed `Matrix.inv`
junk in `lambdaHat` (C47(4)); all `Classical.choose` uses are from proved ∃! theorems.

Compilation: not run by me (brief prefers reading). `.lake/build/.../Statements/Ch7.olean`
(19:15:49) and `Ch7Proofs.olean` (19:16:41) are newer than both sources (19:12:04, 11:36:36),
so the files elaborated in the current working tree. Axiom audit not re-run.

Wrappers: every `_holds` in scope is either a direct term `:= Library.export` or an
`intro … exact Library.export …` with only argument plumbing (`by linarith` for η₀<1/4 ⇒ η₀≤1,
`hη1.le`, `by omega`). `Lemma7_1_holds`/`Lemma7_1_tv_holds` add short set-equality and
`inf'`/`min'` glue lemmas (`valueMin_eq_global`, `valueMax_eq_global`,
`chiSquared_primal_set_eq`) and `simpa` unfoldings; no optimization argument is reproved.
`Thm7_9_corrected_holds` supplies constants (10⁴, 1/216) and calls
`FedSync.fedSynQ_error_le_of_eta_le_one`. `Thm7_10_holds` supplies c₀=1, Cγ=`lbConst 1` and
calls `lowerBound_of_fewRounds_onRange`. All OK.

Bin legend: SRC = SOURCE, STD = STANDING, TYP = TYPING, DISC = DISCLOSED, EXC = EXCESS.

---

## 1. Lemma7_1_tv — Ch7.lean:21

Source: `lemma:dual-form`, robust_RL.tex:302–324 (TV bullet :311–316); TV def intro.tex:219–224;
standing σ>0 robust_RL.tex:37–38.

Reconstruction: ∀ finite S, p⁰∈Δ(S), σ (>0, standing), V∈ℝ^S with V≥0:
inf_{p: TV(p,p⁰)≤σ} ⟨p,V⟩ = max_{α∈[Vmin,Vmax]} {⟨p⁰,[V]_α⟩ − σ(α − min_{s'}[V]_α(s'))},
[V]_α = min(V,α).

| binder | Lean type | bin | citation |
|---|---|---|---|
| State, Fintype | Type u | TYP | 𝒮 = {1..S} :22 |
| Nonempty State | inst | TYP | S≥1 implicit; needed for V_min/V_max |
| p | FiniteDistribution State | SRC | :305 |
| V | State → ℝ | SRC | :305 |
| σ | ℝ | SRC | :305 |
| 0 < σ | hyp | STD | :37–38 "σ>0" |
| ∀ s, 0 ≤ V s | hyp | SRC | :305 "V ≥ 0" |

Counts: SRC 4, STD 1, TYP 2, DISC 0, EXC 0.
Checks: TV ball = ½‖p−q‖₁ ≤ σ (equals event-sup TV on a finite carrier). `⨅` over the subtype:
nonempty (q = p) and bounded below (V ≥ 0), so no junk. "max" is encoded as ∃α in the interval
attaining the inf with every β's objective ≤ α's — equivalent to "the max exists and equals the
inf". Endpoints, clipping and min_{s'} match. Scope: only the TV bullet, which is stated exactly
as printed; the full lemma is `Lemma7_1`. Not a deviation within its scope.
Verdict: **PASS**.

## 2. Lemma7_1 — Ch7.lean:46

Source: as above, both bullets :311–322; χ² def intro.tex:229–234 (P ≪ Q required);
Var_p prelim.tex:443.

Reconstruction: TV bullet as above ∧ χ² bullet: inf_{p≪p⁰, χ²(p‖p⁰)≤σ}⟨p,V⟩ =
max_{α∈[Vmin,Vmax]} {⟨p⁰,[V]_α⟩ − √(σ Var_{p⁰}([V]_α))}.

| binder | Lean type | bin | citation |
|---|---|---|---|
| State, Fintype | Type u | TYP | :22 |
| Nonempty State | inst | TYP | V_min/V_max |
| p, V, σ | as above | SRC | :305 |
| 0 < σ | hyp | STD | :37–38 |
| V ≥ 0 | hyp | SRC | :305 |

Counts: SRC 4, STD 1, TYP 2, EXC 0.
Checks: χ² feasible set = {q : q≪p ∧ Σ_{p>0}(q−p)²/p ≤ σ} is exactly χ²(q‖p) ≤ σ with the
absolute-continuity requirement of intro.tex:228; sInf of a nonempty (q=p), bounded-below set.
Var written as E[x²] − (E x)², matching prelim.tex:443. No junk sqrt issue (the argument is
σ·Var ≥ 0 at every α). Self-contained.
Verdict: **PASS**.

## 3. Thm7_10 — Ch7.lean:113

Source: `thm:lower_bound`, federated_RL.tex:227–239; algorithm :166–220 (update :186–188,
averaging :191–194, standing t_{C_round}=T and N=BT :196, Q₀=0 :207). SOURCE-ISSUES C42.

Reconstruction: (reading: universal c₀ first) ∃c₀>0, ∃ C_γ>0 depending only on γ, ∀γ∈[5/6,1),
∀ S≥4, A≥2, ∀ T ≥ max{16, 1/(1−γ)}, ∀ schedule (linear with c_η>0, or constant η∈(0,1)), ∀
communication schedule 𝒞 ⊆ [T] with T∈𝒞, ∀ B≥1, if C_round ≤ c₀/((1−γ)log²N) then ∃ MDP
instance s.t. ∀ K≥2: E‖Q̂ − Q⋆‖∞ ≥ C_γ/(√N log³N), N=BT; 𝒜 ranges over "a federated
Q-learning algorithm with intermittent communication, as described in Algorithm 2", whose
description includes (:196) "the averaging step may be replaced by any distributed mean
estimation routine, including variants that include compression".

| binder | Lean type | bin | citation |
|---|---|---|---|
| c₀, 0<c₀ | ∃ ℝ | SRC | :233 "some universal constant c₀>0" (c₀-first reading, C42) |
| Cγ : ℝ→ℝ, ∀γ, 0<Cγ γ | ∃ | SRC | :238 "C_γ>0 depends only on γ" |
| 5/6 ≤ γ, γ<1 | hyp | SRC | :229 |
| State, Action, Fintype | Type | TYP | |
| 4 ≤ card State, 2 ≤ card Action | hyp | SRC | :229 |
| T, B, 𝒞, η | ∀ | SRC | :230–235 |
| 16 ≤ T, 1/(1−γ) ≤ T | hyp | SRC | :230 |
| 1 ≤ B | hyp | TYP | batch size (v) :178 |
| 𝒞 ⊆ Icc 1 T | hyp | STD | 𝒞 = {t_r} of iterations :179,:191 |
| T ∈ 𝒞 | hyp | STD | :196 "assume t_{C_round}=T" |
| schedule disjunction (on 1≤t≤T) | hyp | SRC | :230, :235 |
| 𝒞.card ≤ c₀/((1−γ)log²(BT)) | hyp | SRC | :231–233, N=BT :196 |
| ∃ M, M.discount = γ (rewards∈[0,1] in structure) | concl | SRC | :235 |
| ∀ K, 2 ≤ K | concl | SRC | :238 |

Counts: SRC 10, STD 2, TYP 2, DISC 0, EXC 0.
Checks: quantifier order matches (instance after all algorithm parameters, before K; Cγ before
everything except γ). `genericOutput` = (1/K)Σ_k Q_T^k equals each agent's Q_T because T∈𝒞;
`fedSamplingLaw` is the genuine product law; integral over a finite space (no integrability
junk); `supError` over nonempty finite carriers. Junk: log(BT)>0 since BT≥16. The printed
statement is vacuous-in-N (C42) but that is not a deviation.
Deviation: only exact averaging is modelled; the algorithm class of the printed theorem (via
:196) also includes any distributed mean-estimation routine / compressed variants. A lower bound
over the smaller class is weaker than the printed result. The docstring and C42 disclose this
("Disclosure: only exact averaging is modelled …"), but the entry is **unsuffixed**. Per the
brief, any deviation in a plain entry is a FAIL. (Judgment note: one could argue the :196 sentence
is an informal side remark outside the algorithm box; I read "as described in Algorithm" as
including it. The underlying mathematics and the disclosure text are accurate.)
Verdict: **FAIL** (classification only).
Proposed fix: rename to `Thm7_10_restricted` (keep the Prop unchanged), state in the docstring
that it differs from the printed result by restricting 𝒜 to exact averaging, and point to C42
(which already records the restriction) or to `#statement-index-scope-disclosures`. If the project
instead rules that :196 is not part of the theorem's algorithm class, remove the word
"Disclosure" and say so explicitly in C42.

## 4. Thm7_3_corrected — Ch7.lean:156

Source: `thm:l1-lower-bound`, robust_RL.tex:377–391; model :19–157. SOURCE-ISSUES C38.

Reconstruction: ∀ c₀∈(0,1/8] (printed "any small enough positive constant"), ∀ (S, A, γ, σ, ε)
with σ∈(0,1−c₀], γ∈[1/2,1), ε∈(0, c₀/(256(1−γ))], ∀ N ≤ c₀ log2/(8192(1−γ)²max{1−γ,σ}ε²):
∃ two γ-discounted RMDPs M₀,M₁ and μ s.t. inf_{π̂} max_i P_i(V_i^{⋆,σ}(μ) − V_i^{π̂,σ}(μ) > ε) ≥ 1/8.

| binder | Lean type | bin | citation |
|---|---|---|---|
| c₀, 0<c₀, c₀≤1/8 | ∀ | SRC | :379 |
| State, Action, Fintype, Nonempty | Type | TYP | :22 |
| γ, σ, ε, N | ∀ | SRC | :379–388 |
| 2 ≤ card Action | hyp | DISC | name `_corrected`, docstring, C38 |
| 0<σ, σ≤1−c₀ | hyp | SRC | :379 |
| 1/2≤γ, γ<1 | hyp | SRC | :380 |
| 0<ε, ε≤c₀/(256(1−γ)) | hyp | SRC | :380 |
| N bound | hyp | SRC | :388 |
| ∃ M₀ M₁ μ, discounts = γ | concl | SRC | :380–381 |
| ∀ est : Samples → StationaryPolicy | concl | SRC | :390 "all estimators" |

Counts: SRC 9, TYP 1, DISC 1, EXC 0.
Checks: TV ball/rectangularity/robust values are the source objects (sInf over admissible kernels
of actual trajectory values; V⋆ = sSup over stationary randomized policies — both bounded, no junk).
Sampling law = product of nominal rows, N per (s,a). Models chosen after N (allowed: the dataset
depends on N in the printed text). Rewards may differ between M₀ and M₁, and estimators see only
samples; docstring and C38 disclose that this is why S=1 works and give the known-reward variant.
Note (non-blocking): estimators are deterministic maps of the data (randomized estimators, i.e.
data + independent seed, are not quantified); `max` is not linear under mixtures, so this is not
automatically equivalent. This is the standard meaning of "estimator" and is stated in the
docstring, but SOURCE-ISSUES does not mention it; consider one sentence in C38.
Verdict: **PASS-DISCLOSED**.

## 5. Thm7_3_corrected_knownReward — Ch7.lean:186

Source/reconstruction as in 4, under the known-reward convention
(generative_model_model_based.tex:31; robust_RL.tex:25, :206–215).

Binder table: as entry 4, plus:

| binder | Lean type | bin | citation |
|---|---|---|---|
| 2 ≤ card State | hyp | DISC | C38 (S=1 false under known reward; paper argument) |
| 2 ≤ card Action | hyp | DISC | C38 (A=1 refuted in Lean, `not_thm7_3_printed`) |
| M₀.reward = M₁.reward | concl | SRC | known-reward convention (strengthens the construction) |

Counts: SRC 10, TYP 1, DISC 2, EXC 0.
Checks: docstring accurately says S=1 necessity is paper-only and A=1 is machine-checked, matching
C38. Same estimator-class note as entry 4.
Verdict: **PASS-DISCLOSED**.

## 6. Thm7_5_corrected — Ch7.lean:236

Source: `thm:chi2-lower-bound`, robust_RL.tex:461–480; χ² intro.tex:229–234. SOURCE-ISSUES C7.

Reconstruction: ∃ c₃>0 (small), ∃ c₄>0, ∀ (S, A, γ∈[3/4,1), σ∈(0,∞), ε ≤ c₃/(1−γ)), ∀ N ≤
c₄/((1−γ)³ε²)(1+σ/(1−γ)): ∃ M₀, M₁, μ with inf_{π̂} max_i P_i(gap > ε) ≥ 1/8.

| binder | Lean type | bin | citation |
|---|---|---|---|
| c₃, c₄, positivity | ∃ first | SRC | :465, :476 |
| State, Action, Fintype, Nonempty | Type | TYP | |
| γ, σ, ε, N | ∀ | SRC | |
| 2 ≤ card Action | hyp | DISC | `_corrected`, docstring, C7 |
| 3/4≤γ, γ<1 | hyp | SRC | :463 |
| 0<σ | hyp | SRC | :463 |
| ε ≤ c₃/(1−γ) | hyp | SRC | :464 |
| N bound | hyp | SRC | :475–477 |
| ∃ M₀ M₁ μ, discounts | concl | SRC | |
| ∀ est | concl | SRC | :479 |

Counts: SRC 9, TYP 1, DISC 1, EXC 0.
Checks: no ε>0 is added (as printed); at ε<0 the event is sure since V⋆ ≥ V^{π̂} (π̂ is among the
policies in the sSup), at ε=0 the Lean value c₄/0=0 forces N=0 — disclosed and harmless. χ² ball
is support-aware. Same estimator-class note as entry 4.
Verdict: **PASS-DISCLOSED**.

## 7. Thm7_5_corrected_knownReward — Ch7.lean:265

As entry 6 plus `2 ≤ card State` (DISC, C7), `2 ≤ card Action` (DISC, C7), shared reward in the
conclusion (SRC, known-reward convention). Counts: SRC 10, TYP 1, DISC 2, EXC 0.
Checks: docstring claim "both necessities machine-checked" matches C7 and the existence of
`knownReward_needs_two_states`, `knownReward_needs_two_actions`, `printed_at_fails`
(`RobustRL/LowerBounds/LowerBound75Necessity.lean`).
Verdict: **PASS-DISCLOSED**.

## 8. Thm7_8_corrected — Ch7.lean:316

Source: `thm:lower-marl`, marl.tex:487–503; model :20–54 (rewards [0,1], two-player zero-sum
r₂=−r₁, r₁≥0 :50–53); gap :326–340. SOURCE-ISSUES C40.

Reconstruction: ∃ c₁, c₂ >0 small; ∀ m≥2, ∀ 0<ε≤c₁H: ∃ family {MG_θ} of m-player zero-sum games
with S states, horizon H, A_i actions s.t. inf_{π̂} max_θ P_θ{gap(π̂) > ε} ≥ 1/4 whenever total
sample size < c₂H⁴S max_iA_i/ε².

| binder | Lean type | bin | citation |
|---|---|---|---|
| c₁, c₂ >0 | ∃ first | SRC | :490, :499 |
| m, S, H, A | ∀ ℕ | SRC/TYP | :490–491 |
| 2 ≤ m | hyp | SRC | :490 |
| 2 ≤ S, 2 ≤ H, 2 ≤ sup A | hyp | DISC | C40, docstring |
| ε, 0<ε, ε≤c₁H | hyp | SRC | :490 |
| ∃ Θ, G | concl | SRC | :491 |
| zeroSumAdm (G θ) | concl | DISC | m≥3 convention C40 (for m=2 it equals r₂=−r₁, r₁∈[0,1]) |
| shared reward | concl | SRC | known-reward convention; strengthens construction |
| N, N < c₂H⁴S maxA/ε² | ∀/hyp | SRC | :496–499 |
| Ω, μ ≥0, HasSum μ 1 | ∀ | DISC | discrete randomization (docstring, C40) |
| rule (adaptive query law) | ∀ | SRC | generative model :307–311 |
| out (joint Markov policy from history) | ∀ | SRC | :501 "(joint) policy estimators" |
| ∃ θ, 1/4 ≤ P_θ(gap>ε) | concl | SRC | ∃θ is stronger than max ≥ |

Counts: SRC 10, TYP 0 (sizes counted SRC), DISC 3 groups, EXC 0.
Checks: `gapJ` = max_s max_i (best-response − value) with real iSup over Markov deviations
(bounded since |r|≤1 and H finite, so no junk). Family fixed before N (stronger). Rewards
constrained at every h∈ℕ (constrains the existential construction; stronger). If some A_j=0 the
query type is empty and the statement is vacuous — disclosed, outside the source domain.
Verdict: **PASS-DISCLOSED**.

## 9. Thm7_8_corrected_constSum — Ch7.lean:339

Identical to entry 8 with `constSumAdm` (Σ_i r = 1, all r∈[0,1]) in place of `zeroSumAdm`.
`constSumAdm`: DISC (C40 "normalised constant-sum" reading, footnote marl.tex:53). Other bins as
entry 8; EXC 0.
Verdict: **PASS-DISCLOSED**.

## 10. Thm7_9_corrected — Ch7.lean:396

Source: `thm:dist-syncq-local`, federated_RL.tex:99–117; algorithm :35–90 (0<η<1 :51,:76; WLOG
τ∣T :70); sampling :21–29. SOURCE-ISSUES C41.

Reconstruction: ∃ c_T, c_η >0; ∀ δ∈(0,1), ε∈(0,1/(1−γ)], 0≤Q₀≤1/(1−γ), τ satisfying (106),
with η = c_ηK(1−γ)⁴ε²/log(SAKT/δ) and T ≥ c_T/(K(1−γ)⁵ε²)·log³(SAKT/(δε(1−γ)²)): w.p. ≥1−δ,
‖Q_T − Q⋆‖∞ ≤ ε.

| binder | Lean type | bin | citation |
|---|---|---|---|
| c_T, c_η >0 | ∃ first | SRC | :104 |
| State, Action, Fintype | Type | TYP | |
| M | DiscountedMDP | SRC | :21 |
| K, τ, T | ℕ | SRC | |
| 1≤K, 1≤τ, 1≤T | hyp | TYP | :21, :56, :74 |
| τ ∣ T | hyp | STD | :70 "assume T divisible by τ" |
| 0 < γ | hyp | STD | MDP 0<γ<1 (standing MDP def.; needed for (106) division) |
| δ∈(0,1) | hyp | SRC | :101 |
| ε∈(0,1/(1−γ)] | hyp | SRC | :101 |
| Q₀ bounds | hyp | SRC | :102 |
| η = formula | hyp | SRC | :114 |
| η < 1 | hyp | DISC | `_corrected`, docstring, C41 |
| τ condition | hyp | SRC | :106 |
| T condition | hyp | SRC | :112–113 |

Counts: SRC 10, STD 2, TYP 2, DISC 1, EXC 0.
Checks: probability under the genuine product law `fedSamplingLaw M T K 1`, read through
`fedSamplesExtend … 0`; Q⋆ = `optimalityFixedPoint` (from proved ∃!); output (1/K)Σ_k Q_T^k with
averaging when t ≡ 0 mod τ — matches (59–68). η>0 follows from hypotheses (log argument >1).
Docstring accurately states the constants and that "every sufficiently small c_η" is not claimed.
Verdict: **PASS-DISCLOSED**.

## 11. Thm7_2_corrected — Ch7.lean:441

Source: `thm:l1-upper-bound`, robust_RL.tex:342–359; DRVI :243–289. SOURCE-ISSUES C37.

Reconstruction: ∃ C₁, C₂ large universal; ∀ γ∈[1/4,1), σ∈(0,1), δ∈(0,1), ε∈(0,√(1/max{1−γ,σ})];
π̂ = DRVI greedy output after T = C₁log(N/(1−γ)) iterations; if N ≥ C₂log(SAN/((1−γ)δ))/((1−γ)²
max{1−γ,σ}ε²) then w.p. ≥1−δ, ∀s V^{⋆,σ}(s) − V^{π̂,σ}(s) ≤ ε.

| binder | Lean type | bin | citation |
|---|---|---|---|
| C₁, C₂ >0 | ∃ first | SRC | :357 |
| State, Action, Fintype | Type | TYP | |
| M (nominal kernel, reward, γ) | DiscountedMDP | SRC | RMDP :22 |
| σ, δ, ε, N | ∀ | SRC | |
| hN : 0 < N | binder | TYP | empirical kernel (:206–212) needs N≥1 |
| 1/4 ≤ γ | hyp | SRC | :344 |
| 0<σ<1, δ∈(0,1), 0<ε, ε≤√(…) | hyp | SRC | :344–345 |
| N bound | hyp | SRC | :352–354 |
| ∀ T, C₁log(N/(1−γ))/(1−γ) ≤ T | hyp | DISC | C37, docstring (was T = C₁log(N/(1−γ))) |
| ∀ pick, ∀ data IsGreedy | hyp | SRC | greedy output :254–258, ties unspecified |

Counts: SRC 8, TYP 2, DISC 1, EXC 0.
Checks: `empiricalDRVI` starts at Q̂₀=0 and iterates the exact robust Bellman operator on
P̂⁰; output deterministic greedy policy as printed; "∀ pick" covers every tie rule. Values as in
entry 4.
Verdict: **PASS-DISCLOSED**.

## 12. Thm7_4_corrected — Ch7.lean:470

Source: `thm:l2-upper-bound`, robust_RL.tex:437–450. SOURCE-ISSUES C37.
Reconstruction: as entry 11 with χ², σ∈(0,∞), ε∈(0,1/(1−γ)], N ≥ c₂(1+max{√σ,σ}/(1−γ))
log(SAN/δ)/((1−γ)³ε²), T = c₁log(N/(1−γ)).

Binder table identical in shape to entry 11: c₁,c₂ (SRC :449), types (TYP), M,σ,δ,ε,N (SRC),
hN (TYP), 0<σ (SRC :439), 1/4≤γ (SRC), δ, ε ranges (SRC :439), N bound (SRC :445–447),
T ≥ c₁log(N/(1−γ))/(1−γ) (DISC, C37), ∀ greedy pick (SRC).
Counts: SRC 8, TYP 2, DISC 1, EXC 0.
Verdict: **PASS-DISCLOSED**.

## 13. Remark7_1_restricted — Ch7.lean:508

Source: `remark:tv-upper`, robust_RL.tex:361–372 (eq:oracle_requirement :365–369).
SOURCE-ISSUES `#statement-index-scope-disclosures` (Remark 7.1 bullet).

Reconstruction: Theorem 7.2's conclusion holds for any planner on P̂⁰ whose output satisfies
‖V̂^{⋆,σ} − V̂^{π̂,σ}‖∞ ≤ Õ((1−γ)²/N).

| binder | Lean type | bin | citation |
|---|---|---|---|
| c_opt ≥ 0, ∀ c_opt ∃ C₂ | quantifiers | DISC | reading of Õ, scope disclosures |
| C₂ > 0 | ∃ | SRC | inherited from Thm 7.2 |
| types, M, σ, δ, ε, N, hN | as entry 11 | SRC/TYP | |
| premises on γ, σ, δ, ε, N | hyp | SRC | Thm 7.2 :344–354 |
| ∀ f : State → Action (deterministic planner output) | in event | DISC | scope disclosures |
| requirement with c_opt(1−γ)²log(SAN/((1−γ)δ))/N | in event | DISC | Õ reading (log factor from commented :367) |

Counts: SRC ~7, TYP 2, DISC 3, EXC 0.
Checks: event quantifies ∀ f inside the probability, so any data-dependent planner is covered
without measurability; |·| form equivalent to one-sided (V̂⋆ ≥ V̂^f). No DRVI iteration count.
Verdict: **PASS-DISCLOSED**.

## 14. Remark7_2_restricted — Ch7.lean:552

Source: `remark:chi2-upper`, robust_RL.tex:453–457. Same structure as entry 13 with Theorem 7.4
premises and requirement c_opt·log(SAN/((1−γ)δ))/N² (the printed O(·), constant read as c_opt;
DISC). Deterministic outputs only (DISC). Counts: SRC ~7, TYP 2, DISC 3, EXC 0.
Verdict: **PASS-DISCLOSED**.

## 15. Thm7_11_corrected_halfspace — Ch7.lean:600

Source: `thm:Berry-Esseen-linear`, inference.tex:132–141; setting :47–89; Λ⋆, A, Γ :99–117.
SOURCE-ISSUES C43 (half-space paragraph).

Reconstruction: TD with iid samples (μ, λ₀>0), η_t = η₀t^{-2/3}, 0<η₀<1/4, PR averaging:
d_cvx(√TΔ̄_T, N(0,A⁻¹ΓA⁻ᵀ)) ≲ (coef)T^{-1/3} + C̃T^{-1/2}, with universal ≲ and polynomial C̃.

| binder | Lean type | bin | citation |
|---|---|---|---|
| State, Action, Fintype, DecidableEq, Nonempty | Type | TYP | |
| M, π, μ | ∀ | SRC | :47–61 |
| η₀ | ∀ | SRC | :133 |
| V₀ | ∀ | SRC (source leaves V₀ free; ∀ is stronger) | |
| ∀ s, 0 < μ s | hyp | SRC | :61 λ₀>0 |
| 0<η₀<1/4 | hyp | SRC | :133 |
| ∀ s, 0 < trueGamma s | hyp | DISC | Γ_true ≻ 0, C43, docstring |
| ∃ K > 0 (instance-, η₀-, V₀-dependent) | concl | DISC | docstring (3), C43 |
| ∀ T ≥ 1, ∀ u b, half-spaces only | concl | DISC | docstring (2), C43 |
| Γ = trueGamma | object | DISC | docstring (1), C43 |

Counts: SRC 6, TYP 1, DISC 4, EXC 0.
Checks: `lawProb` = exact iid law of √TΔ̄_T (finite sum); `gaussCov` = law of A⁻¹(√Γ⊙Z), a
genuine probability measure; tdA invertible under μ>0, γ<1 (no Matrix.inv junk);
`stepSize` indexing gives η_t = η₀t^{-2/3} for t≥1; `rpow` with T≥1 fine.
Verdict: **PASS-DISCLOSED**.

## 16. Eq_classic_clt_corrected — Ch7.lean:639

Source: `eqn:classic-clt`, inference.tex:98–117. SOURCE-ISSUES C43 (classic CLT paragraph).
Reconstruction: with an appropriate schedule, √TΔ̄_T →d N(0, A⁻¹ΓA⁻ᵀ) as T→∞.

| binder | Lean type | bin | citation |
|---|---|---|---|
| types/instances | | TYP | |
| M, π, μ, V₀ | ∀ | SRC | |
| η₀ ∀, 0<η₀<1/4 | ∀/hyp | SRC (implies the printed ∃ schedule) | :98 ∃ schedule; family from :133 |
| ∀ s, 0<μ s | hyp | SRC | :61 |
| ∀ g bounded continuous | ∀ | SRC | definition of →d |
| limit covariance trueGamma | object | DISC | C43 |

Counts: SRC 5, TYP 1, DISC 1, EXC 0.
Checks: E g = Σ_ω pathWeight·g(scaledError) is the exact expectation; no Γ ≻ 0 needed (degenerate
Gaussians allowed; √Γ≥0). Docstring scope of refutations accurate vs C43.
Verdict: **PASS-DISCLOSED**.

## 17. Eq_classic_clt_restricted — Ch7.lean:666

As entry 16 with printed Γ (`printedGamma`, r(s)=r_π(s)) and the added hypothesis
`∀ s a a', π(a|s)>0 → π(a'|s)>0 → r(s,a)=r(s,a')` (DISC: `_restricted`, docstring, C43 classic CLT
paragraph). Counts: SRC 5, TYP 1, DISC 1, EXC 0.
Checks: hypothesis is satisfiable (state-only rewards, deterministic π) — not vacuous.
Verdict: **PASS-DISCLOSED**.

## 18. Eq_convex_Cdelta_corrected_oracle — Ch7.lean:703

Source: `eq:convex.Cdelta`, inference.tex:187–196 (display :191–193, claim :196). SOURCE-ISSUES
C47 (oracle fixed-shape paragraph), C43.
Reconstruction: any data-chosen convex C_α with N(V̄_T, Λ̂_T/T)-mass ≥ 1−α is an approximate
confidence region for V^π.

| binder | Lean type | bin | citation |
|---|---|---|---|
| types/instances; M, π, μ, η₀, V₀ | | TYP/SRC | |
| μ>0, 0<η₀<1/4 | hyp | SRC | :61, :133 |
| Γ_true ≻ 0 | hyp | DISC | docstring, C47 oracle paragraph |
| ∃ K>0, ∀ T≥1 | concl | DISC | rate T^{-1/3}, instance K |
| fixed u≠0, z (shape fixed before data) | ∀ | DISC | C47(1) correction |
| oracle Λ = A⁻¹diag(Γ_true)A⁻ᵀ instead of Λ̂_T | object | DISC | docstring (2), C47 |
| only half-lines, slabs, Bonferroni box | scope | DISC | docstring (3) |

Counts: SRC 5, TYP 1, DISC 5, EXC 0.
Checks: formulas verified: (1) P(uᵀV̄ − z√(uᵀΛu/T) ≤ uᵀV^π) vs Φ(z); (2) two-sided vs 2Φ(z)−1
with 2K; (3) union bound 1 − 2S(1−Φ(z)) − 2SK T^{-1/3} (uses (2) at u=e_s). `(tdA)⁻¹ᵀ` parses
as transpose of the (genuine) inverse. `gaussianReal 0 1` is standard normal.
Verdict: **PASS-DISCLOSED**.

## 19. Eq_convex_Cdelta_corrected_plugin — Ch7.lean:759

Source: as 18 plus `eq:defn-hat-Lambda` :180–182. SOURCE-ISSUES C47 (plug-in paragraph, (4)).
Binders as entry 18 except: printed plug-in Λ̂_T = `lambdaHat` (SRC), conclusions are limits
pointwise in (u,z) and "eventually ≥ … − η" (DISC: asymptotic only), Γ_true ≻ 0 (DISC),
fixed shapes (DISC). Junk `Matrix.inv`=0 on singular Ā_T: disclosed, does not affect limits
(singular event probability → 0). √ of uᵀΛ̂u: Λ̂ is PSD (Γ̂ PSD with positive weights), so no
negative-sqrt junk. Counts: SRC 6, TYP 1, DISC 4, EXC 0.
Verdict: **PASS-DISCLOSED**.

## 20. Eq_defn_hat_Lambda_corrected — Ch7.lean:801

Source: `eq:defn-hat-Lambda`, inference.tex:180–184 ("final estimator of Λ⋆"); Ā_T, Γ̂_T :165–177.
SOURCE-ISSUES C43 (plug-in paragraph), C47(4).
Reconstruction: Λ̂_T is an estimator of Λ⋆ — read as consistency Λ̂_T →p Λ⋆.

| binder | Lean type | bin | citation |
|---|---|---|---|
| types; M, π, μ, η₀, V₀ | | TYP/SRC | |
| μ>0, 0<η₀<1/4 | hyp | SRC | :67, :133 |
| ε > 0 | ∀ | SRC | def. of →p |
| target trueLambda (Γ_true) instead of Λ⋆ | object | DISC | C43 plug-in paragraph |

Counts: SRC 5, TYP 1, DISC 1, EXC 0.
Checks: `aBar`, `gammaHat` (residuals at V̄_T, weights 2t/(T(T+1)) via 0-based (t+1)/Σ), `lambdaHat`
match :165–182; junk inverse disclosed and asymptotically irrelevant. No Γ ≻ 0 assumed.
Verdict: **PASS-DISCLOSED**.

---

## Summary

| # | Entry | Def line | Verdict |
|---|---|---|---|
| 1 | Lemma7_1_tv | Ch7.lean:21 | PASS |
| 2 | Lemma7_1 | :46 | PASS |
| 3 | Thm7_10 | :113 | FAIL (unsuffixed but disclosed restriction to exact averaging) |
| 4 | Thm7_3_corrected | :156 | PASS-DISCLOSED |
| 5 | Thm7_3_corrected_knownReward | :186 | PASS-DISCLOSED |
| 6 | Thm7_5_corrected | :236 | PASS-DISCLOSED |
| 7 | Thm7_5_corrected_knownReward | :265 | PASS-DISCLOSED |
| 8 | Thm7_8_corrected | :316 | PASS-DISCLOSED |
| 9 | Thm7_8_corrected_constSum | :339 | PASS-DISCLOSED |
| 10 | Thm7_9_corrected | :396 | PASS-DISCLOSED |
| 11 | Thm7_2_corrected | :441 | PASS-DISCLOSED |
| 12 | Thm7_4_corrected | :470 | PASS-DISCLOSED |
| 13 | Remark7_1_restricted | :508 | PASS-DISCLOSED |
| 14 | Remark7_2_restricted | :552 | PASS-DISCLOSED |
| 15 | Thm7_11_corrected_halfspace | :600 | PASS-DISCLOSED |
| 16 | Eq_classic_clt_corrected | :639 | PASS-DISCLOSED |
| 17 | Eq_classic_clt_restricted | :666 | PASS-DISCLOSED |
| 18 | Eq_convex_Cdelta_corrected_oracle | :703 | PASS-DISCLOSED |
| 19 | Eq_convex_Cdelta_corrected_plugin | :759 | PASS-DISCLOSED |
| 20 | Eq_defn_hat_Lambda_corrected | :801 | PASS-DISCLOSED |

Counts: PASS 2, PASS-DISCLOSED 17, FAIL 1, UNSURE 0.

Non-blocking recommendations:
- Thm7_3/7_5 (all four entries): the estimator class is deterministic maps of the data to
  stationary randomized policies; randomized estimators (data + independent seed) are not
  covered, and `max_i P_i` is not linear under mixtures. Standard reading of "estimator", stated in
  the docstrings, but not in C7/C38; add one sentence there (Thm7_8 handles this explicitly).
- No compilation or axiom audit was run by this auditor; evidence of elaboration is olean
  timestamps only.

---

## Re-audit after fix (2026-11-09)

Scope: `Thm7_10_restricted` (formerly `Thm7_10`), the C7/C38 estimator-class additions, and
consistency across the ledgers. Read-only; no compilation by me (the fix log reports
`lean-local.sh` rc=0 for Ch7/Ch7Proofs and axioms limited to propext/Classical.choice/Quot.sound).

- **Entry** (Ch7.lean:84 docstring, def :114). The Prop is unchanged: I compared it token by token
  with the text audited above. The docstring now says "restricted", cites
  `docs/SOURCE-ISSUES.md#C42` and federated_RL.tex line 196, and states that only exact
  averaging is modelled. The wrapper `Thm7_10_restricted_holds` (Ch7Proofs.lean:168) has the same
  plumbing as before. The binder table is unchanged, except that the exact-averaging restriction
  is now DISC (name + docstring + C42). EXC 0. Verdict: **PASS-DISCLOSED** (was FAIL).
- **C42** now names `Thm7_10_restricted`, records the rename and says the entry is counted as a
  restricted variant. ERRATA item 14 matches.
- **C7** (SOURCE-ISSUES:238) and **C38** (:1241) each have the sentence "Estimator class (both
  entries): estimators are deterministic maps from the sample array to policies; randomized
  estimators are not covered." This closes my non-blocking note.
- **Ledgers:**
  - `docs/named-result-status.json`: Theorem 7.10 now sits in `proved_variants` with
    `lean_statement` and `lean_statement_proof` renamed. It holds 46 certified + 48 variant
    records (94 records for the 90 results).
  - `docs/graph/nodes.json`: the summary gives printed/corrected/restricted 44/30/16 over 90
    named results, and the 7.10 node has variant "restricted", ledger "variant".
  - `docs/COVERAGE.md:29` says "Restricted result proved", with the reason.
  - `docs/PROGRESS.md:5` gives the same 44/30/16 split and the same reason.
  - `README.md` gives no per-status counts; its deviation text names the exact-averaging
    restriction.
  - No live reference to the old name remains in Formalization/, docs/, scripts/ or site/;
    `Federated/LowerBound/GenericAlgorithmDefinitions.lean:101` is already updated, so the fix log's "not done" note about it is stale.
- **Minor, non-blocking:**
  1. `docs/PROGRESS.md:110` is a dated history paragraph and still says "Theorem 7.10 is proved as
     printed". Line 5 supersedes it, but a short "(superseded 2026-11-09: restricted)" note would
     avoid a contradiction.
  2. The `line` fields in `docs/graph/nodes.json` look stale for some Ch7 entries. For example,
     Thm7_3_corrected is listed at 132 but its docstring starts at 138; Thm7_10_restricted at 84 is
     correct. If `gen_nodes.py --check` passed, this may be its own convention; worth a
     regeneration check.

Re-audit verdict for ch7a: PASS 2, PASS-DISCLOSED 18, FAIL 0, UNSURE 0.
