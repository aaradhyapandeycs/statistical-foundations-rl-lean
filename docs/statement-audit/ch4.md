> Public copy of an independent five-bin statement audit (2026-11-09/10), scrubbed of local paths and agent identifiers. Auditors were independent of the builders. No result here is author-approved. Method and totals: [README](README.md).

# Five-bin statement audit: batch ch4 (2026-11-09)

Auditor: independent statement auditor (read-only; no Lean compiled, no git, no edits outside this file).

Pinned inputs (sha256):
- `source/upstream/tex/chapters/generative_model_model_free.tex` 7f4eb058e00480bc0694cac93ac41e22f4cfe48aa58a00c4ccf909f805e60b22
- `Formalization/Statements/Ch4.lean` 86923d993aab1153a084d9fe622b28ba7506f4c68c9390efef46d9320c3baabd
- `Formalization/Statements/Ch4Proofs.lean` 39d6d11d46244d6bc2483e35c3b3d33a549d9e4dd2f8f4448bdb851b8d0f6971

Method: BRIEF.md + `skills/lean/skills/lean-statement-audit/SKILL.md`. For each entry the printed `.tex`
statement (and surrounding standing text) was read first, then the Lean `Prop`, then project definitions
were expanded (files listed in "Definitions expanded"). Compilation was not needed: all findings are textual.

Abbreviations: `.tex` = the chapter file above; H = `M.effectiveHorizon` = `1/(1-M.discount)`.

## Definitions expanded (shared by many entries)

| Object | File | Finding |
|---|---|---|
| `DiscountedMDP` | `Formalization/MDP/CoreDefinitions.lean:30` | fields: nonempty S, A; transition rows (`FiniteDistribution`); reward in [0,1]; discount in [0,1). These are the monograph's standing MDP conventions (rewards in [0,1], γ∈[0,1)). STANDING/TYPING. |
| `FiniteDistribution`, `expectation` | same `:15` | genuine probability vector. OK. |
| `StationaryPolicy` | same `:42` | `State → FiniteDistribution Action`. OK. |
| `trajectoryExpectedValue` (V^π) | `MDP/InfiniteReturn.lean:43` | expectation of infinite discounted return under trajectory law. Source object. OK. |
| `trajectoryExpectedQ` (Q^π) | `MDP/ForcedActionReturn.lean:35` | forced first action, then π. OK. |
| `optimalGreedyPolicy` | `MDP/OptimalTrajectoryValue.lean:33` | greedy w.r.t. the optimality fixed point (choice from a proved maximizer existence). Q⋆ := Q^{π_greedy}, V⋆ := V^{π_greedy}. Project convention, correct object. |
| `effectiveHorizon` | `MDP/FixedPoint.lean:81` | literally `1/(1-γ)`. |
| `policyTransition` | `MDP/Basic.lean:136` | P_π(·|s) = Σ_a π(a|s) P(·|s,a) (eq:defn-P-s-pi-inf). OK. |
| `FiniteDistribution.variance` | `Probability/VarianceDefinitions.lean:14` | E f² − (E f)². OK. |
| `tdIterate`, `policyReward` | `ModelFree/TDIterateBounds.lean:11,16` | V_{t+1}(s)=(1−η_{t+1})V_t(s)+η_{t+1}(r_π(s)+γV_t(s_{t+1}(s))) — Algorithm alg:td-infinite exactly. |
| `tdSourceSamplingLaw`, `tdSourceSamplesExtend`, `tdSourceSampledIterate` | `ModelFree/TDSourceSamplingDefinitions.lean` | product of T·S independent P_π rows; update k reads draw k−1. Faithful. |
| `tdSamplingLaw`, `tdSamplesExtend` | `ModelFree/TDSamplingDefinitions.lean` | (T+1)-layer product with unused time-0 layer; marginal on used coordinates is the source law. OK. |
| `ModelBasedPolicyEvaluation.samplingLaw`, `ModelBasedPolicyLearning.samplingLaw` | `Generative/ModelBasedDefinitions.lean:24,69` | `Measure.pi` of true rows. OK. |
| `tdValueBefore`, `tdPastSigma` | `TDConditionalMomentDefinitions.lean`, `TDCausality.lean:24` | V_t from padded data; σ-algebra = comap of exactly the used coordinates with times 1..t (sub-σ-algebra of the ambient; so `μ[f|m]` is not junk). OK. |
| `tdSourceFixedTerminalProxyVector` → `tdSquareLateWindowRandomProxy` | `TDSharpVarianceSum.lean:30` | Σ_{k=⌊t/2⌋+1}^{t} η̄ η_k γ² [∏_{i=k+1}^t(I−η_i(I−γP_π)) Var_{P_π}(V_{k−1})]_q = W̄_t of eq:TD-variance-proxy. OK. |
| `tdSourceBarEta` | `TDSourceFreedmanBudgetSmallness.lean:11` | 2log³T/((1−γ)T) = η̄ of eq:defn-bar-eta-large-k-TD. OK. |
| `tdTerminalVarianceSum` | `TDVarianceSum.lean:44` | Σ_{k<t} E[Z_{k+1}²|F_k] with Z the fixed-terminal increment (`tdWeightedErrorIncrement`, = eq:TD-Zk-defn); conditional 2nd moment = conditional variance for centered Z. = W_t of eq:defn-Wt-TD. OK. |
| `qLearningIterate`, `qLearningValue` | `QLearningIterateBounds.lean:11,18` | synchronous update with max over actions = alg:q-infinite. OK. |
| `qSamplingLaw`, `qSamplesExtend`, `qSampledIterate`, `qPolicySampledIterate` | `QLearningSamplingDefinitions.lean` | product of T·S·A true rows; Q̃ uses next action f(s'). OK. |
| `qChiSquared`, `qChiBall`, `qRobustExpectations`, `qRobustBellmanPlus/Minus`, `qChiValueSpan` | `QLearningRobustDefinitions.lean`, `QLearningComparisonDefinitions.lean` | χ²(q‖p)=Σ_{p>0}(q−p)²/p with explicit support condition = eq:Q-comparison-ball; T^± = eq:Q-comparison-operator with V_Q = max_a Q; span = max − min. OK. sSup/sInf of a nonempty (contains p) bounded set: no junk. |
| `qHardMDP`, `qHardP`, `qHardRow` | `QLearningHardMDPDefinitions.lean` | M_hard with p=(4γ−1)/(3γ); copied action at states 0,2,3. Rewards/transitions match `.tex:2752–2768`. |
| `qLbMDP`, `qLbStay`, `qLbAuxIterate`, `qLbAuxValue`, `qLbXi`, `qLbXiMax` | `QLearningLowerBoundDefinitions.lean` | M_hard with dominated dummy action; Q̂, V̂, ξ_t(a), ξ_{t,max} literally eqn:Qhat-schumann and eqn:defn-xi-t. OK. |
| `qLbSingleAuxIterate` | `QLearningRateFacts.lean:132` | single-action recursion Q̂_{k+1}=(1−η)Q̂_k+η(1+γP_{k+1}(1|1,a)Q̂_k). OK. |
| `FiniteQLearning.sampledIterate`, `FiniteHorizonGenerative.samplingLaw`, `EnvironmentStage.optimalQ` | `FiniteQ/Definitions.lean`, `Generative/FiniteHorizonSamplingDefinitions.lean`, `MDP/EnvironmentDefinitions.lean` | backward sweep with current-iteration Q_{t,h+1}, terminal Q_{t,H+1}≡0, H·S·A·T independent draws, Q⋆_h by backward induction. OK. |
| `AsyncQ.pairKernel`, `pairPow`, `initLaw`, `pathLaw`, `iterate`; `FiniteMarkov.kpow`, `tvDist`, `pathMeasure`, `pathAt` | `AsyncQ/Definitions.lean`, `Probability/FiniteMarkov/Definitions.lean` | pair chain K((s,a),(s',a'))=P(s'|s,a)π_b(a'|s'); path law of (X_0..X_T) from s₀; one-entry update with constant η; TV = ½Σ|p−q|. Faithful to `.tex:1898–1946`. |

No fallback/junk definition found in any object reached by the Ch4 Props.

---

## 1. `Thm4_1` — Ch4.lean:25; `thm:policy-evaluation-TD`, `.tex:204–224` (schedule `:181–187`, alg `:154–176`)

Reconstruction: ∃ universal c₁ ≥ c₂ > 0 ("for some small enough") and c₃ > 0 ("sufficiently large") such that ∀ S, A, M, π, δ∈(0,1), ε∈(0,1/(1−γ)], γ∈[1/2,1), schedule (1≤t≤T), T≥2, budget T ≥ c₃ log³T log(ST/δ)/((1−γ)³ε²), V₀∈[0,1/(1−γ)]: P(∀s |V_T(s)−V^π(s)|≤ε) ≥ 1−δ.

| Binder | Lean type | Bin | Citation |
|---|---|---|---|
| c₁ c₂ c₃, `0<c₂`, `c₂≤c₁`, `0<c₃` | ∃ ℝ | SOURCE | `.tex:206–211` |
| State, Action, `[Fintype]` | Type | TYPING | finite MDP convention |
| M (fields: nonempty, rewards∈[0,1], γ∈[0,1)) | DiscountedMDP | STANDING/TYPING | MDP conventions |
| π | StationaryPolicy | SOURCE | `:179` "given policy π" |
| η, δ, ε, T | | SOURCE | |
| `1/2 ≤ γ`, `γ < 1` | | SOURCE | `:206` |
| `2 ≤ T` | | SOURCE | `:206` |
| `0<δ<1` | | SOURCE | `:206` |
| `0<ε≤1/(1−γ)` | | SOURCE | `:206` |
| schedule ∀1≤t≤T | | SOURCE | eq:thm:eta-TD `:184` |
| V₀, `0≤V₀≤1/(1−γ)` | | SOURCE | `:216` |
| budget | | SOURCE | eq:thm:sample-size-TD-thm `:209–210` |

Counts: SOURCE 11, STANDING 1, TYPING 1, DISCLOSED 0, EXCESS 0.
Other checks: quantifier order ∃c's before everything (universal) OK; conclusion carrier `.real` of the real product law, event exact; logs positive (T≥2, S≥1, δ<1); no vacuity (budget polylog). Reading note: "for some small enough universal constants" read existentially, which is the literal "for some" (docstring states witnesses). Wrapper: applies `tdSource_policyEvaluation_exactSamples_accuracy_exists_universal_constants`, unfolds H; no second proof.
**Verdict: PASS.**

## 2. `Lemma4_2` — Ch4.lean:46; `lemma:TD-bounded`, `.tex:293–302`

Reconstruction: V₀∈[0,H], 0≤η_t≤1 ∀0≤t≤T ⇒ ∀0≤t≤T: 0≤V_t≤H·1 and ‖V_t−V^π‖∞≤H.

| Binder | Bin | Citation |
|---|---|---|
| State, Action, Fintype | TYPING | |
| M, π | STANDING | |
| η, T | SOURCE | |
| samples (arbitrary realization) | TYPING (generalization: pathwise, stronger than "TD iterates") | |
| V₀, `0≤V₀≤H` | SOURCE | `:295` |
| `∀k≤T, 0≤η k≤1` | SOURCE | `:300` |
| `t ≤ T` | SOURCE | `:300` |

Counts: SOURCE 5, STANDING 1, TYPING 2, DISCLOSED 0, EXCESS 0. Conclusion sup-norm on `State → ℝ` = ℓ∞. Wrapper restricts the global rate hypothesis to k≤t (allowed). **Verdict: PASS.**

## 3. `Lemma4_4` — Ch4.lean:58; `lemma:TD-square`, `.tex:643–659`

Reconstruction: for every k≥1, η_k(1−η_k)γ² Var_{P_π}(V_{k−1}) ≤ (I−η_k(I−γP_π))(V_{k−1}∘V_{k−1}) − E_{k−1}[V_k∘V_k] + 2η_k/(1−γ)·1, a.s., in the TD context (V₀ bounded, rates in [0,1]).

| Binder | Bin | Citation |
|---|---|---|
| State, Action, Fintype; M, π | TYPING/STANDING | |
| η, T, V₀ | SOURCE/STANDING | |
| `0≤V₀≤H` | STANDING | Thm 4.1 premise `:216`; lemma used inside its proof |
| `∀1≤i≤T, 0≤η i≤1` | STANDING | SA framework 0<η_t<1 (`:39`), schedule ⇒ η∈(0,1] |
| k, `1≤k≤T` | SOURCE | "every k≥1"; T is the experiment horizon, arbitrary, so no loss |

Counts: SOURCE 3, STANDING 3, TYPING 2, EXCESS 0. Expansion of (I−η(I−γP))(V²) = (1−η)V²+ηγP_πV² matches. Conditional expectation w.r.t. `tdPastSigma T (k−1)` (history through k−1) is a genuine sub-σ-algebra. **Verdict: PASS.**

## 4. `Lemma4_5` — Ch4.lean:78; `lemma:TD-variance-proxy-bound`, `.tex:727–743`, context `:489`, `:540–546`

Reconstruction: in the Thm 4.1 setting, for fixed t with T/(c₂ log T) ≤ t ≤ T: with probability ≥ 1−δ/(2T), ‖W̄_t‖∞ ≤ 16η̄/(1−γ)² and ‖W_t‖∞ ≤ 33 log³T/((1−γ)³T).

| Binder | Bin | Citation |
|---|---|---|
| ∃c₀>0 ∀ 0<c₂≤c₁≤c₀ ∃c₃>0 (threshold form, updated 2026-11-13; was ∃c₁≥c₂ ∃c₃, implied by it) | SOURCE | constants of Thm 4.1 |
| State, Action, M, π | TYPING/STANDING | |
| η, δ, ε, T, t, V₀ | SOURCE | |
| `1/2≤γ`, `2≤T`, `0<δ<1`, `0<ε≤H` | STANDING | Thm 4.1 premises `:206` |
| schedule, V₀ bounds, budget | STANDING | `:184`, `:216`, `:209` |
| `t ≤ T` | STANDING | W_t defined for t≤T |
| `T/(c₂ log T) ≤ t` | STANDING | `:489` "Throughout this step, we assume t ≥ T/(c₂ log T)" |

Counts: SOURCE 2, STANDING 7, TYPING 1, EXCESS 0. W̄_t and W_t match eq:TD-variance-proxy and eq:defn-Wt-TD (see table above); η̄ = `tdSourceBarEta`. Joint event, probability 1−δ/(2T): matches. Wrapper applies `tdSource_varianceProxy_exists_universal_constants`. **Verdict: PASS.**

## 5. `Lemma4_8` — Ch4.lean:98; `lemma:non-negativity-Qt-Vt`, `.tex:1052–1071`

Reconstruction: Q₀∈[0,H], 0≤η_t≤1 ∀t≥0 ⇒ ∀t: 0≤Q_t≤H, 0≤V_t≤H, ‖Q_t−Q⋆‖∞≤H.
Binders: State/Action/M (TYPING/STANDING), η, samples (pathwise generalization), Q₀, t (SOURCE), `0≤Q₀≤H` (SOURCE `:1055`), `∀k 0≤η k≤1` (SOURCE `:1063`). Counts: SOURCE 5, STANDING 1, TYPING 2, EXCESS 0. Q⋆ = trajectory Q of the optimal greedy policy. **Verdict: PASS.**

## 6. `Lemma4_9` — Ch4.lean:262; `lemma:Q-step-size`, `.tex:1093–1112` (schedule `:881–886`, weights `:1075–1083`, η̄ `:1087–1089`)

Reconstruction: under schedule (0≤t≤T) with c₁≥c₂>0: for ⌊T/2⌋<i≤t≤T, 0≤η_i^{(t)}≤η_i≤η̄ and Σ_{i=⌊T/2⌋+1}^t(η_i^{(t)})²≤η̄; Σ_{i=τ}^t η_i^{(t)} = 1−∏_{j=τ}^t(1−η_j) (1≤τ≤t), = 1 (τ=0).

| Binder | Bin | Citation |
|---|---|---|
| γ, c₁, c₂, T, η | SOURCE | |
| `2 ≤ T` | STANDING | Thm 4.6 `:894` (T≥2; schedule needs log T>0) |
| `γ < 1` | STANDING | discount convention (γ≥0 not even assumed) |
| `0<c₁`, `0<c₂` | SOURCE | `:888` c₁≥c₂>0 (c₁≥c₂ dropped: assumes less) |
| schedule ∀k≤T | SOURCE | eq:thm:infinite-horizaon-eta |

Counts: SOURCE 4, STANDING 2, EXCESS 0. Weight `w` matches def:eta-i-t-simple on i≤t (i>t values never used); `T/2` = ⌊T/2⌋. Square-sum stated ∀t≤T (empty for t≤⌊T/2⌋): implies printed. Sum identities hold for any η (stronger). **Verdict: PASS.**

## 7. `Lemma4_10` — Ch4.lean:112; `lemma:Q-comparison-facts`, `.tex:1338–1373`

Reconstruction: (i) ∀p∈Δ(S), ρ>0, V with span ≤ 1/(1−γ): √(ρVar_p V) − ρ/(1−γ) ≤ sup_{U_ρ(p)} qᵀV − pᵀV ≤ √(ρVar_p V), same for pᵀV − inf. (ii) P' rows in U_ρ(P rows), same r,γ ⇒ ‖Q⋆,P' − Q⋆‖∞ ≤ √(ργ/(2(1−γ)³)).

| Binder | Bin | Citation |
|---|---|---|
| State, Fintype, `Nonempty State` | TYPING | Δ(S) nonempty |
| p, ρ, `0<ρ`, v, span hyp | SOURCE | `:1340, :1354` |
| γ, `0≤γ`, `γ<1` | STANDING | discount convention |
| (ii) State, Action, M, M', ρ, `0<ρ` | SOURCE/TYPING | `:1363–1365` |
| `M'.reward = M.reward`, `M'.discount = M.discount` | SOURCE | "same rewards and discount" |
| balls premise | SOURCE | `:1364` |

Counts: SOURCE 9, STANDING 2, TYPING 2, EXCESS 0. Ball includes the support condition. **Verdict: PASS.**

## 8. `Lemma4_11` — Ch4.lean:132; `lemma:robust-Bellman-contraction`, `.tex:1422–1438` (operators `:1407–1420`)

Reconstruction: T^± (with ρ = 8η̄ log(4SAT/δ), b = 2ρ/(1−γ)) are γ-contractions in ℓ∞.
Lean: for every ρ>0 with b = 2ρ/(1−γ). Binders: State/Action/M (TYPING/STANDING), ρ, `0<ρ` (SOURCE; generalization of the specific positive ρ), Q, R (SOURCE). Counts: SOURCE 3, STANDING 1, TYPING 1, EXCESS 0. Generalizing ρ implies the printed case. **Verdict: PASS.**

## 9. `Thm4_6` — Ch4.lean:147; `thm:infinite-horizon-simple`, `.tex:891–912` (schedule `:881–886`)

Reconstruction: ∃ c₁≥c₂>0 ("for some small enough"), c₃>0; ∀ δ∈(0,1), ε∈(0,H], γ∈[1/2,1), A≥2, schedule (0≤t≤T, log³T), T≥2, budget log⁴T log(SAT/δ)/((1−γ)⁴ε²), Q₀∈[0,H] ⇒ P(∀(s,a) |Q_T−Q⋆|≤ε) ≥ 1−δ.

| Binder | Bin | Citation |
|---|---|---|
| ∃c₁ c₂ c₃ + signs/order | SOURCE | `:894–899` |
| State, Action, Fintype, M | TYPING/STANDING | |
| η, δ, ε, T, Q₀ | SOURCE | |
| `1/2≤γ` | SOURCE | `:894` (γ<1 in structure) |
| `2 ≤ card Action` | SOURCE | `:894` A≥2 |
| `2≤T`, `0<δ<1`, `0<ε≤H` | SOURCE | `:894–896` |
| schedule ∀k≤T | SOURCE | `:884` 0≤t≤T |
| Q₀ bounds | SOURCE | `:902` |
| budget | SOURCE | `:897–898` |

Counts: SOURCE 13, STANDING 1, TYPING 1, EXCESS 0. Reading note as for Thm4_1 (existential "for some"); docstring transparently states the witnesses c₁=c₂=1 and that the "every sufficiently small" reading is not established. **Verdict: PASS** (interpretive caveat recorded below).

## 10. `Thm4_6_constantRate` — Ch4.lean:175; prose `.tex:945–953`

Reconstruction: when T ≍ threshold, the constant rate η ≡ 1/(1+c₁(1−γ)T/log³T) satisfies the schedule for 0≤t≤T and is Õ((1−γ)³ε²).
Binders: c₁,c₂,c₃,γ,ε,δ,S,A,T and `0<c₂≤c₁`, `0<c₃` (SOURCE/STANDING, constants of the schedule/budget), `0≤γ<1` (STANDING), `0<ε`, `0<δ<1`, `1≤S`, `1≤A`, `2≤T` (STANDING: Thm 4.6 context; S,A≥1 typing of a finite MDP). (ii) premise = "T ≥ threshold" (SOURCE: the `≥` half of `≍`, which is the only direction an upper bound on η uses — disclosed in docstring and not a weakening of the claim, since the claim is an upper bound). Counts: SOURCE 4, STANDING 9, TYPING 2, EXCESS 0. Algebra checked: η ≤ log³T/(c₁(1−γ)T) ≤ (1−γ)³ε²/(c₁c₃ log T log(SAT/δ)). Õ made explicit. **Verdict: PASS.**

## 11. `Thm4_6_underestimation_restricted` — Ch4.lean:210; prose `.tex:1869–1881`

Reconstruction: Q̃ (same init and samples, next action from deterministic optimal π⋆) satisfies Q̃_T ≤ Q_T, and (in the Thm 4.6 setting, w.h.p.) Q_T−Q⋆ ≥ Q̃_T−Q⋆ ≥ −Õ(√(1/((1−γ)³T)))·1.

| Binder | Bin | Citation |
|---|---|---|
| ∃c₁≥c₂>0, C>0 | SOURCE | schedule constants of Thm 4.6; Õ constant |
| State, Action, M | TYPING/STANDING | |
| η, δ, T, Q₀, schedule, `1/2≤γ`, `2≤T`, `0<δ<1`, Q₀ bounds | STANDING | Thm 4.6 setting `:891–912` |
| f, `∀s V^f(s)=V⋆(s)` | SOURCE | "deterministic optimal policy π⋆" `:1871` |

No A≥2, no budget, no ε (assumes less). Counts: SOURCE 3, STANDING 9, TYPING 1, EXCESS 0. Hidden polylog explicit (log⁴T·log(SAT/δ)). Clause 1 pathwise ∀ data (stronger). **Verdict: PASS.**

## 12. `Lemma4_3_corrected` — Ch4.lean:241; `lemma:TD-step-size`, `.tex:317–327` (schedule `:182–185`, weights `:308–313`)

Reconstruction (printed): schedule (1≤t≤T), c₁c₂≤1/8; ∀t ≥ T/(c₂ log T): η_k^{(t)} ≤ 1/T² for 0≤k≤t/2, and η_k^{(t)} ≤ η_k ≤ 2log³T/((1−γ)T) for t/2<k≤t.

| Binder | Bin | Citation |
|---|---|---|
| γ, c₁, c₂, T, η, t, k | SOURCE | |
| `2 ≤ T` | DISCLOSED | docstring; SOURCE-ISSUES C5 (minimality paragraph "with T ≥ 2 and t ≤ T") |
| `0≤γ<1` | STANDING | discount convention (docstring) |
| `0<c₁`, `0<c₂` | SOURCE | `:187` c₁≥c₂>0 |
| `c₁c₂ ≤ 1/8` | SOURCE | `:319` |
| `log²T ≤ c₁(1−γ)T` | DISCLOSED | C5 (Lean counterexample `TDStandaloneStepSizeCounterexample.lean`) |
| schedule | SOURCE | |
| `t ≤ T` | DISCLOSED | C5 |
| `k ≤ t` | SOURCE | case ranges |
| `T/(c₂ log T) ≤ t` | SOURCE | `:319` |

Counts: SOURCE 9, STANDING 1, DISCLOSED 3, EXCESS 0. Weight body = def:eta-k-t (k=0 branch precedence at t=0; t≥1 here anyway). Name suffix, docstring and C5 agree. **Verdict: PASS-DISCLOSED.**

## 13. `Lemma4_14` — Ch4.lean:289; `lem:optimal-V-Q-hardMDP`, `.tex:2797–2811` (M_hard `:2723–2788`)

Reconstruction: for M_hard with p=(4γ−1)/(3γ): V⋆(0)=Q⋆(0,1)=0; V⋆(1)=Q⋆(1,1)=Q⋆(1,2)=V⋆(2)=Q⋆(2,1)=1/(1−γp)=3/(4(1−γ)); V⋆(3)=Q⋆(3,1)=1/(1−γ). Context 3/4≤γ<1.
Binders: γ (SOURCE), `1/4<γ` and `γ<1` (STANDING; weaker than the context 3/4≤γ). Counts: SOURCE 1, STANDING 2, EXCESS 0. Encoding: state-dependent action sets represented by copying the single action at states 0,2,3 (`qHardMDP`); copies are identical so V⋆ and Q⋆ on source actions are unchanged, and "∀a" covers the source action. Treated as TYPING (encoding of A_s), disclosed in docstring. **Verdict: PASS.**

## 14. `Thm4_7_restricted` — Ch4.lean:323; `thm:LB-example-Q-generative`, `.tex:969–982`

Reconstruction: printed theorem (both schedules). Entry states case (ii) only.
Binders: ∃c₃,c_lb>0 (SOURCE), γ, `3/4≤γ<1` (SOURCE), T, `c₃/(1−γ)²≤T` (SOURCE), η, `0<η<1` (SOURCE, case ii); existential MDP (Fin 4, Bool) with discount γ (SOURCE). Restriction to case (ii): DISCLOSED (suffix, docstring, SOURCE-ISSUES C30 names `Thm4_7_restricted`). Counts: SOURCE 6, DISCLOSED 1, EXCESS 0. Max over s encoded as ∃s (finite S), Q₀≡0, V_T=max_a Q_T. **Verdict: PASS-DISCLOSED** (now redundant with `Thm4_7`).

## 15. `Lemma4_15` — Ch4.lean:346; `lem:lower-bound-E-xi-lower-Q`, `.tex:3429–3449` (Step-5 context `:3270–3275`, `:3316–3324`, `:3405–3412`)

Reconstruction: in Step 5 (3/4≤γ<1, T≥c₃/(1−γ)², 4/((1−γ)T)<η<1/((1−γ)²T)), τ̂ = max{τ : (1−η(1−γp))^{T−τ+1} ≤ 6/7}; ∃ universal c>0: E[ξ_{t,max}] ≥ c/(√((1−γ)²T) log T) ∀t≥τ̂.

| Binder | Bin | Citation |
|---|---|---|
| ∃c>0 | SOURCE | `:3441` |
| ∃c₃>0 | STANDING | Thm 4.7 `:971` |
| γ, `3/4≤γ<1` | STANDING | `:971` |
| T, `c₃/(1−γ)²≤T` | STANDING | `:971` |
| η, moderate-regime bounds | STANDING | `:3272` |
| τ̂ with maximality (existence concluded) | SOURCE | eq:tau-hat-byproduct-duplicate; remark `:3451–3453` |
| t, N, `τ̂≤t`, `t≤N` | SOURCE | "for all t≥τ̂"; N is only the experiment horizon |

Counts: SOURCE 4, STANDING 4, EXCESS 0. ℕ-subtraction: τ>T+1 gives exponent 0 → 1 > 6/7, so the max is the source's. WLOG log T ≤ 1/(1−γ) (C31(1)) not assumed; η₀^{(T)}≤1/100 not assumed. Constant slips (C31(3)) only affect the unnamed c; plain name is appropriate. **Verdict: PASS.**

## 16. `Remark4_5` — Ch4.lean:378; Remark `.tex:3455–3457`

Reconstruction: E ξ_{t,max} > 0 (max + ≥2 actions); with a single action a, E ξ_{t,max} = E ξ_t(a) = 0; third sentence explanatory.
Binders (i)/(ii): γ, `3/4≤γ<1` (STANDING), η, N, t, a, `t≤N` (SOURCE/TYPING), W + adaptedness premise (SOURCE: generalizes V̂, which is adapted to state-1 draws). Part (iii): ∃c₃ and the Lemma 4.15 regime, τ̂ maximality, `τ̂≤t≤N` (STANDING: the remark follows Lemma 4.15 whose claim is "for all t ≥ τ̂"). Counts: SOURCE 4, STANDING 6, TYPING 2, EXCESS 0. Single-action experiment represented by the action-a draws at state 1 (law Bernoulli(p), iid), disclosed; (iii) restricted to t≥τ̂ because positivity fails at t=0 (ξ₀ = 0), disclosed in docstring. Note: (iii)'s narrowing is a context reading, not recorded in SOURCE-ISSUES; acceptable as STANDING, but adding a one-line SOURCE-ISSUES note would make the reading auditable. Wrapper (iii) derives positivity from `qLb_lemma415` with c₃' = max c₃ 1 (small derivation of the printed claim from the export; permitted). **Verdict: PASS.**

## 17. `QLearning_singleAction_eq_TD` — Ch4.lean:418; prose `.tex:3455–3457` (sentence 3), also `.tex:931–934`

Reconstruction: with A=1, Q-learning is TD learning (pathwise and in law), and Q⋆(·,a)=V^π.
Binders: State, Action, Fintype, `[Subsingleton Action]` (SOURCE: "single action"), M, π, a, η, Q₀ (SOURCE). Counts: SOURCE 6, TYPING 2, EXCESS 0. Conclusions are exact equalities; no rate restated (as docstring says). **Verdict: PASS.**

## 18. `Thm4_13_corrected` — Ch4.lean:452; `thm:finite-horizon-simple-Q-generative`, `.tex:2215–2236` (schedule `:2203–2210`, update `:2175–2194`)

Reconstruction: for sufficiently small universal c₁≥c₂>0 (schedule 0≤t≤T), sufficiently large c₃; ∀ δ∈(0,1), ε∈(0,1], budget c₃H⁴log³T log(SAT/δ)/ε², Q_{0,h}∈[0,H+1−h] ⇒ P(∀(s,a,h) |Q_{T,h}−Q⋆_h| ≤ ε) > 1−δ.

| Binder | Bin | Citation |
|---|---|---|
| ∃c₀>0 ∀ 0<c₂≤c₁≤c₀ ∃c₃>0 | SOURCE | "sufficiently small" `:2210`, "sufficiently large" `:2220` |
| State, Action, Fintype | TYPING | |
| H, E (stages with rewards∈[0,1]) | STANDING | finite-horizon nonstationary MDP conventions |
| η, δ, ε, T, Q₀ | SOURCE | |
| `2 ≤ T` | DISCLOSED | suffix, docstring, C35 (Lean refutation `not_thm4_13_from_one`) |
| `0<δ<1`, `0<ε≤1` | SOURCE | `:2217` |
| schedule ∀t≤T | SOURCE | `:2207` |
| budget | SOURCE | `:2220–2222` |
| `0≤Q₀ h ≤ H−h` | SOURCE | `:2226` (0-based h) |

Counts: SOURCE 9, STANDING 1, TYPING 1, DISCLOSED 1, EXCESS 0. Strict `<` as printed; terminal convention C35(2). Wrapper picks c₀=1/64, c₃=8000/c₂ and applies the library theorem. **Verdict: PASS-DISCLOSED.**

## 19. `Thm4_12_corrected` — Ch4.lean:502; `thm:infinite-horizon-asyn`, `.tex:2062–2086` (rate `:2054–2058`, assumption `:2012–2015`, μ_min `:2024–2028`, t_mix `:2034–2039`)

Reconstruction: for some universal c₁∈(0,1] and sufficiently large c₂: ∀ δ∈(0,1), ε∈(0,1], γ∈[1/2,1), uniform ergodicity, budget, Q₀∈[0,H] ⇒ with rate η = c₁log³T/((1−γ)Tμ_min), P(max|Q_T−Q⋆|≤ε) ≥ 1−δ.

| Binder | Bin | Citation |
|---|---|---|
| ∃c₁∈(0,1], ∃c₂>0 | SOURCE | `:2058`, `:2071` |
| S, A, Fintype, (Classical DecidableEq) | TYPING | |
| M, πb, s₀ | SOURCE | `:1898–1906` |
| μ + stationarity | SOURCE | μ_{π_b} "its stationary distribution" `:2010` |
| uniform ergodicity ∃C r<1 | SOURCE | Assumption `:2012–2015` |
| tmix, IsLeast | SOURCE | defn-tmix (definitional binder) |
| μmin, `∀x μmin≤μ x`, `∃x μ x = μmin` | SOURCE | defn:mu-min (definitional binder) |
| `0 < μmin` | DISCLOSED | C34(2) |
| `1 ≤ T` | DISCLOSED | C34 corrected-result paragraph (domain premise) |
| `2≤T ∨ 2≤SA` | DISCLOSED | C34(1) |
| `1/2≤γ`, `0<δ<1`, `0<ε≤1` | SOURCE | `:2066` |
| budget | SOURCE | `:2072–2074` |
| Q₀ bounds | SOURCE | `:2077` |

Counts: SOURCE 15, TYPING 2, DISCLOSED 3, EXCESS 0. Conclusion carrier: path law of (X₀..X_T) (Q_T depends only on it). Budget jointly satisfiable for large T (polylog); not vacuous. **Verdict: PASS-DISCLOSED.**

## 20. `Thm4_7` — Ch4.lean:549; `thm:LB-example-Q-generative`, `.tex:969–982`

Reconstruction: ∃ c₃ (sufficiently large), c_lb>0 universal; ∀ 3/4≤γ<1, T≥c₃/(1−γ)², Q₀≡0, η either (i) 1/(1+c_η(1−γ)t) ∀t≥0 for any c_η>0, or (ii) η_t≡η∈(0,1): ∃ γ-discounted MDP, S=4, A=2: max_s E|V_T(s)−V⋆(s)|² ≥ c_lb/((1−γ)⁴T log²T).

| Binder | Bin | Citation |
|---|---|---|
| ∃c₃ c_lb >0 | SOURCE | `:971`, `:980` |
| γ, `3/4≤γ<1` | SOURCE | `:971` |
| T, `c₃/(1−γ)²≤T` | SOURCE | `:971` |
| η, disjunction (i)∨(ii) | SOURCE | `:972–973` |
| ∃ M (Fin 4, Bool), `M.discount = γ` | SOURCE (conclusion witness) | `:974` |

Counts: SOURCE 5 (+conclusion witness), EXCESS 0. MDP chosen after the schedule, as printed. Q₀ ≡ 0 built in. Junk check: at T∈{0,1} log T = 0 makes LHS 0 (trivially true), but any admissible c₃ makes the statement non-vacuous for all large T; harmless. **Verdict: PASS.**

## 21. `Thm4_7_iterationLowerBound` — Ch4.lean:569; prose `.tex:992–1000`

Reconstruction: within Thm 4.7's regime and either schedule, there is an MDP on which max_s E|V_T−V⋆|² ≤ ε² forces T ≳ Ω̃(1/((1−γ)⁴ε²)).
Binders as Thm4_7 (SOURCE/STANDING), plus ∀ε>0 and the accuracy premise (SOURCE). MDP before ε (stronger than needed). Ω̃ made explicit as `T log²T ≥ c_lb/((1−γ)⁴ε²)`. Counts: SOURCE 7, EXCESS 0. **Verdict: PASS.**

## 22. `Thm4_7_case_i` — Ch4.lean:588; `thm:LB-example-Q-generative` case (i), `.tex:969–982`

Binders: ∃c₃ c_lb (SOURCE), γ bounds, T bound (SOURCE), c_η, `0<c_η` (SOURCE `:972`), ∃M (SOURCE). Counts: SOURCE 5, EXCESS 0. This is a sub-statement of the printed theorem (case (i)), named by the case it covers and labelled "implied by Thm4_7" in its docstring; it states printed mathematics, not a modified version. Naming note: it is neither unsuffixed-full nor `_restricted`; acceptable as a reading aid since `Thm4_7` carries the full printed statement. **Verdict: PASS.**

## 23. `Remark4_1` — Ch4.lean:609; Remark `.tex:226–239`

Reconstruction: with δ = ε(1−γ)/2∈(0,1) and budget with log(2ST/(ε(1−γ))): E max_s|V_T−V^π| ≤ ε(1−δ)+δ/(1−γ) ≤ 2ε.
Binders: same as Thm4_1 minus δ (SOURCE/STANDING), budget with substituted δ (SOURCE `:236–237`). Counts: SOURCE 10, STANDING 1, TYPING 1, EXCESS 0. Integrability concluded (excludes Bochner junk); ⨆ over finite nonempty State = max. 0<δ<1 concluded. **Verdict: PASS.**

## 24. `Remark4_2` — Ch4.lean:643; Remark `.tex:914–929`

As Remark4_1 for Thm 4.6 (A≥2, log⁴T, log(2SAT/(ε(1−γ)))). Counts: SOURCE 12, STANDING 1, TYPING 1, EXCESS 0. **Verdict: PASS.**

## 25. `Remark4_3_corrected` — Ch4.lean:692; Remark `.tex:2088–2090`

Reconstruction: remark has no formula; reading "as before" (Remarks 4.1/4.2): δ=ε(1−γ)/2 in Thm 4.12's budget, E max|Q_T−Q⋆| ≤ ε(1−δ)+δ/(1−γ) ≤ 2ε. Binders as Thm4_12_corrected with δ substituted. DISCLOSED: `0<μmin`, `1≤T`, `2≤T ∨ 2≤SA` (suffix, docstring, C34 trailing paragraph names `Remark4_3_corrected`). Counts: SOURCE 14, TYPING 2, DISCLOSED 3, EXCESS 0. Fresh ∃c₁ ∃c₂ ("essentially the same sample complexity") is a disclosed reading. **Verdict: PASS-DISCLOSED.**

---

## Wrappers (`Ch4Proofs.lean`)

All 25 `_holds` theorems either are a single library term or apply one library export after trivial
reshaping (unfolding H, restricting a global rate hypothesis to the used range, choosing c₀/c₃ that
the export proves for, or, in `Remark4_5_holds` (iii), deriving positivity from `qLb_lemma415`
with c₃' = max c₃ 1). None restates or reproves a result. Signatures of library theorems not inspected for
change (outside scope); no `sorry`/`admit` in either file.

## Cross-cutting observations (non-failing)

0. Update 2026-11-13: Thm4_1, Lemma4_5, Thm4_6, Remark4_1, Remark4_2 are now stated in the threshold form (∃c₀ ∀ 0<c₂≤c₁≤c₀ ∃c₃), which implies the reading below; only Thm4_6_underestimation_restricted remains single-pair (C52). The paragraph below is the earlier reading.
1. Constant-quantifier reading. Thm4_1, Lemma4_5, Thm4_6, Thm4_6_underestimation_restricted, Remark4_1, Remark4_2 read
   "for some small enough universal constants c₁ ≥ c₂ > 0" existentially (the literal "for some"); Thm4_13_corrected
   reads "for sufficiently small" (no "some", `.tex:2210`) universally (∃c₀ ∀ c₁≥c₂ ≤ c₀). The split follows the
   printed wording. A reader who takes "small enough" in Thm 4.1/4.6 to mean "every sufficiently small pair" would
   find Thm4_6 (witness c₁=c₂=1) weaker than that reading; the docstring says so explicitly. Not a FAIL under the
   literal wording.
2. Import hygiene (AGENTS.md "ChN.lean imports definition modules only"): Ch4.lean's direct imports are all
   `*Definitions` modules, but some of them transitively import proof modules (e.g.
   `TDSourceFixedTerminalProxyDefinitions` imports `TDSharpEnergyProxy`, `TDSourceRateProxyTransport`;
   `QLearningSamplingDefinitions` imports `QLearningIterateBounds`). Ch4.lean itself contains no proofs. Project
   hygiene only; no fidelity effect.
3. Remark4_5 (iii) narrows "E ξ_{t,max} > 0" to Lemma 4.15's range t ≥ τ̂ (false at t = 0). Classified STANDING
   (context of Lemma 4.15); optional: a one-line SOURCE-ISSUES note.
4. `Thm4_7_restricted` is superseded by `Thm4_7` and `Thm4_7_case_i` overlaps it; harmless duplicates.

## Summary

| # | Entry | Def line | Verdict |
|---|---|---|---|
| 1 | Thm4_1 | 25 | PASS |
| 2 | Lemma4_2 | 46 | PASS |
| 3 | Lemma4_4 | 58 | PASS |
| 4 | Lemma4_5 | 78 | PASS |
| 5 | Lemma4_8 | 98 | PASS |
| 6 | Lemma4_9 | 262 | PASS |
| 7 | Lemma4_10 | 112 | PASS |
| 8 | Lemma4_11 | 132 | PASS |
| 9 | Thm4_6 | 147 | PASS |
| 10 | Thm4_6_constantRate | 175 | PASS |
| 11 | Thm4_6_underestimation_restricted | 210 | PASS |
| 12 | Lemma4_3_corrected | 241 | PASS-DISCLOSED |
| 13 | Lemma4_14 | 289 | PASS |
| 14 | Thm4_7_restricted | 323 | PASS-DISCLOSED |
| 15 | Lemma4_15 | 346 | PASS |
| 16 | Remark4_5 | 378 | PASS |
| 17 | QLearning_singleAction_eq_TD | 418 | PASS |
| 18 | Thm4_13_corrected | 452 | PASS-DISCLOSED |
| 19 | Thm4_12_corrected | 502 | PASS-DISCLOSED |
| 20 | Thm4_7 | 549 | PASS |
| 21 | Thm4_7_iterationLowerBound | 569 | PASS |
| 22 | Thm4_7_case_i | 588 | PASS |
| 23 | Remark4_1 | 609 | PASS |
| 24 | Remark4_2 | 643 | PASS |
| 25 | Remark4_3_corrected | 692 | PASS-DISCLOSED |

Totals: PASS 20, PASS-DISCLOSED 5, FAIL 0, UNSURE 0. EXCESS binders found: 0.
