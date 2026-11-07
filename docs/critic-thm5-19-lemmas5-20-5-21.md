# CRITIC — Theorem 5.19, Lemma 5.20, Lemma 5.21 (online minimax regret lower bound)

Public copy of the independent critic report; local paths removed.

- Date (UTC): 2026-11-07 00:26 (session start; written shortly after)
- Reviewer: independent Claude critic subagent (did not build this code)
- Git HEAD: `35cd1f38aaaa7bf916653564bee48ab88147c1c7` (branch `recovery-batch-ch3-ch6-lower-bounds-20261106`); all reviewed Lean files are **untracked** WIP (`?? Formalization/Online/LowerBound/`, `?? Formalization/Probability/AdaptiveKL*.lean`), not yet imported from `Formalization.lean`.
- Mode: source-only review. No Lean, lake, lean-lsp or compiler was run. Numerics with `python3 -I` in the scratchpad only. The source reconstruction and comparison below were written before reading any PREFLIGHT, BUILD-LOG, PROGRESS or other CRITIC file.

## SHA256

| File | SHA256 |
|---|---|
| `source/upstream/tex/chapters/onlineRL.tex` | `393a4d26c228d833a27e54a4913489e499d2143f2f9b80ebf3c55d9a9ccb8c53` (matches `source/provenance.json`) |
| `source/upstream/tex/chapters/prelim.tex` | `2d27bb720d49020ce1d3ea362b1678a90c6208882accca90fef21c25e42031a5` (matches provenance) |
| `<builder working folder>/probe/StatementProbe.lean` | `48fb35c89d808790ce890a26f5bfbcba4c3a0ba2280539bb23aa2d9df50cb546` |
| `<builder working folder>/probe/AxiomProbe.lean` | `3af517c7079c9f50612f2331b3601909fa13c75e4f84217b4630a0db1793b98d` |
| `Formalization/Online/LowerBound/FamilyDefinitions.lean` | `8e92c375fab8ddfd7a75141d9716de103f8b4f1b2652a763d7342c84160b5da2` |
| `Formalization/Online/LowerBound/ValueGap.lean` | `f694c5f0f392ef255351ae8d5ed286a66d1c060b2f618d7ebdcbbb410fce3266` |
| `Formalization/Online/LowerBound/BanditDefinitions.lean` | `59c437c03fe8a5b04590cef43a19d92d43c845c2b96a439b9ad620f31673820e` |
| `Formalization/Online/LowerBound/TestingTools.lean` | `fa9ff366611f9578eda599234df4ab41857ba5a18fbcce97f8f00fd14ae072e0` |
| `Formalization/Online/LowerBound/BanditTesting.lean` | `1b6287decf3901d91f2188dcc7a27ca3ee6e76bf77fde2babb11c3200d17a0af` |
| `Formalization/Online/LowerBound/RegretDefinitions.lean` | `c0d16bcf003951621decab98a030c1ed186989f6fe9197c936e77e9c5996415c` |
| `Formalization/Online/LowerBound/HistoryKL.lean` | `748c84e320f4b451691bfafe9c60e08fc073ab1bca3c8a58e16ff3327ff6f0ab` |
| `Formalization/Online/LowerBound/MinimaxRegret.lean` | `216271231ed08c4a50501d7a1dba0c99e849daf10f47c6a524ce369f3669f219` |
| `Formalization/Probability/AdaptiveKLDefinitions.lean` | `07d71f2449bc81c846b36f3aeb56e36fd72ea685eeb58cc154562ba05465dbd1` |
| `Formalization/Probability/AdaptiveKL.lean` | `811a9f5a1952279b7d7ea5ceed9cd0dd58fc75665fa1e772c241a90fa3b64ba8` |

## 1. Independent source reconstruction

### Model (onlineRL.tex:80–92, prelim.tex:687–720)
Finite-horizon nonstationary MDP, rewards `r_h(s,a) ∈ [0,1]` (deterministic), Markov randomized policies `π = {π_h : S → Δ(A)}`, `V_h^π(s) = E[Σ_{t≥h} r_t(s_t,a_t) | s_h = s]`. Online learner: before episode `k` chooses `π^k` from the trajectories of episodes `< k` (with arbitrary internal randomization). Theorem 5.19 uses the ρ-regret `E_M[Σ_k (V_1^⋆(ρ) − V_1^{π^k}(ρ))]`.

### Theorem 5.19 (`thm:minimax-lower-online`, 2443–2456)
`∃ c₀ > 0` universal such that `∀ S ≥ 2, A ≥ 3, H ≥ 2, K ≥ 1`, `∃` a collection `C_mdp` of MDPs (S states, at most A actions per state, horizon H) and `ρ ∈ Δ(S)` with
`inf_{π̂} sup_{M ∈ C_mdp} E_M[Σ_{k=1}^K (V_1^⋆(ρ) − V_1^{π^k}(ρ))] ≥ c₀ min{√(H³SAK), HK}`.
The quantifier order in the prose ("holds for some universal constant") puts `c₀` uniformly before `S,A,H,K`. The source family is finite (`|C_mdp| = A^{H S/2}`), so `sup = max`.

### Hard sub-MDP (2512–2650)
States `{0,1}`; `A_0 = {0}`, `A_1 = {1,…,A}`; `r_h(0,0)=0`, `r_h(1,a)=1`; `P_h(0|0,0)=1`; `P_h(0|1,a) = q_{a_h^⋆}(a)`; `ρ = δ_1`. For `a⋆ ≠ 1`: `q(a⋆)=1/H−ε₀/H²`, `q(1)=1/H−ε₀/(2H²)`, else `1/H`; for `a⋆ = 1`: `q(1)=1/H−ε₀/(2H²)`, else `1/H`. Range `0 < ε₀ ≤ H/2`. Family `M_i`, `i ∈ [A]^H`. Independent check: with `ε₀ ≤ H/2`, `q ∈ [1/(2H), 1/H]`; the gap `P(1|1,a⋆) − P(1|1,a) ≥ ε₀/(2H²)` for `a ≠ a⋆` holds in all four cases.

### Lemma 5.20 (2654–2668; proof 4798–4935)
`H ≥ 2`, every `M ∈ C^sub` and every (Markov) policy `π`: `V_1^⋆(1) − V_1^π(1) ≥ Σ_{h=1}^H ε₀(H−h)/(16H²) (1 − π_h(a_h^⋆|1))`.
My re-derivation: `V_h^π(1) ≥ (H−h+1)/2` (uses `P(1|1,·) ≥ 1−1/H`, `1−e^{−x} ≥ x/2` on `[0,1]`); one-step recursion `Δ_h ≥ (1−1/H)Δ_{h+1} + ε₀(H−h)/(4H²)(1−π_h(a⋆|1))` (also valid at `h=H` since `V_{H+1}=0` makes the weight `0`); unrolling gives coefficient `Π_{h'<h} P(1|1,a⋆_{h'}) ≥ (1−1/H)^{h−1} ≥ (1−1/H)^H ≥ 1/4`. The printed proof writes `(1−1/H)^h` (an index slip that only weakens the bound). **The printed weight `ε₀(H−h)/(16H²)` is correct as stated.**

### Lemma 5.21 (2709–2721; proof 4938–5097)
`A ≥ 3, H ≥ 2, 0 < ε₀ ≤ H/2`, any round `t ≤ H³A/(18ε₀²)`: `inf_{π̂} (1/A) Σ_{i=1}^A P_{B_i}(a_{t+1} ≠ i) ≥ 1/3`, where `B_i` has Bernoulli reward `1 − q_i(a)` and `a_{t+1} ∼ π^{t+1}(·|x_t)`.
Re-derivation: only arm `a = i` distinguishes `B_1` from `B_i` (`q_1(1) = q_i(1)` for `i≠1`), with KL `≤ (ε₀/H²)²/(1/(4H)) = 4ε₀²/H³`; chain rule ⇒ `Σ_{i≥2} KL(P_1^{(t)}‖P_i^{(t)}) ≤ 4ε₀²t/H³ ≤ 2A/9`; reverse Fano (prelim.tex:1209–1229, `M = A−1`) ⇒ error `≥ 1 − 1/A − √((A−1)/(9A))`, which is `≈ 0.3945` at `A=3` and increasing in `A`, so `≥ 1/3`. Correct. (The reverse-Fano step is valid for randomized tests.)

### Proof of Theorem 5.19 (2733–3290)
S=2: per-coordinate counterfactual action `ã_h^k ∼ π_h^k(·|1)`, reduction to Lemma 5.21 with `t = k−1` per coordinate `h`, average over `i_{−h}`; total `≥ ε₀K(H−1)/(96H) ≥ ε₀K/192`, `ε₀ = min{√(H³A/(18K)), H/2}`. General S (even S assumed, 3015): `S/2` disjoint copies, `ρ` uniform on the copies' rewarding states, conditioning on `J = (s_1^k)_k`, Case 1 (`K ≥ S/2`, binomial tail) and Case 2 (`K < S/2`, `Σ_j P(K_j=1) = K(1−2/S)^{K−1} ≥ K/4`, which I verified: `(1−2/S)^{K−1} ≥ (1−2/S)^{S/2} ≥ 1/4` for `S ≥ 4`), then `ε₀ = min{√(SAH³/(1800K)), H/2}`. Constant implied by the printed route: about `1/(768√1800) ≈ 3.1e−5`.

## 2. Comparison tables

### Lemma 5.20 (`ProbeCh5.Lemma5_20` = type of `onlineLBSub_value_gap`)

| Item | Source | Lean | Verdict |
|---|---|---|---|
| States | `{0,1}`, 1 rewarding, 0 absorbing | `Fin 2`, state `1` rewarding (`reward s _ = if s = 1 then 1 else 0`), state `0` `stayRow` | match |
| Actions | `A_0={0}`, `A_1={1..A}` | `Fin A` at both states; at `0` all actions identical | admissible (exactly A ≤ "at most A"); values unaffected |
| Arm index | source arm `a` | `Fin` index `a−1`; distinguished arm `1` ↔ index `0` in `onlineLBq` (`(astar : ℕ) ≠ 0`, `(a : ℕ) = 0`) | match, literal case split |
| Exit probs | `q_{a⋆}(a)` cases above | `onlineLBq` identical; `onlineLBq_bounds` proves `[1/(2H), 1/H]` | match |
| Transition | `P(0|1,a)=q`, `P(1|1,a)=1−q` | `exitRow 1 0 … q` | match |
| Range | `H ≥ 2`, `0 < ε₀ ≤ H/2` (standing) | `2 ≤ H`, `0 < ε`, `ε ≤ H/2` | match (construction's standing range, not hidden) |
| Policy | Markov randomized `π_h(·|s)` | `π : ℕ → StationaryPolicy (Fin 2) (Fin A)`; `controlled` feeds `π 0` to stage 0 | match |
| Values | `V_1^⋆(1)`, `V_1^π(1)` | `optimalValue (List.ofFn …) 1` (backward induction), `trajectoryValue (controlled …) 1` (actual trajectory expectation) | match |
| Weight | `ε₀(H−h)/(16H²)`, `h=1..H` | `ε(H−((h:ℕ)+1))/(16H²)`, `h : Fin H` 0-based | match |
| Error term | `1 − π_h(a_h^⋆|1)` | `1 − (π h 1).prob (i h)` | match |

### Lemma 5.21 (`ProbeCh5.Lemma5_21` = type of `bandit_testing`)

| Item | Source | Lean | Verdict |
|---|---|---|---|
| Instances/arms | `B_i`, `i ∈ [A]`, Bernoulli `1−q_i(a)` | `banditRewardRow … i a`: `true` w.p. `1 − onlineLBq H ε i a` | match |
| Learner | `π^t(·|x_{t−1})` history-dependent randomized | `BanditLearner`: `policy σ t x` with finite seed `σ ∼ seedLaw` | superset of source class (one-point seed = source class) ⇒ stronger |
| History law | `Π π^τ(a_τ|x_{τ−1}) P_i(R_τ|a_τ)` | `interactionLaw (L.policy σ) (banditEnv … i) t` = `seqLaw` of `π·e` | match |
| `a_{t+1}` | drawn from `π^{t+1}(·|x_t)` | `compLaw (history law t) (L.policy σ t)`, error `x.2 ≠ i`, averaged over σ | match (0-based round `t` = source round `t+1`) |
| Range | `A ≥ 3`, `H ≥ 2`, `0<ε₀≤H/2`, `t ≤ H³A/(18ε₀²)` | `3 ≤ A`, `2 ≤ H`, `0<ε≤H/2`, `(t:ℝ) ≤ H³A/(18ε²)`, `t : ℕ` (incl. 0) | match |
| Conclusion | `inf_π̂ (1/A)Σ_i P(a_{t+1}≠i) ≥ 1/3` | `∀ L, 1/3 ≤ (1/A) Σ_i banditNextArmErrorProb L … i t` | match (∀L ⇔ inf ≥) |

### Theorem 5.19 (`ProbeCh5.Thm5_19` = type of `minimax_lower_online`)

| Item | Source | Lean | Verdict |
|---|---|---|---|
| Constant | `∃ c₀ > 0` universal | `∃ c₀, 0 < c₀ ∧ ∀ S A H K …` (proved with `1/1536`) | match (uniform) |
| Ranges | `S≥2, A≥3, H≥2, K≥1` | same | match |
| Family | collection of MDPs, S states, ≤A actions, horizon H, with one ρ | `∃ I, Fintype I, E : I → Fin H → EnvironmentStage (Fin S) (Fin A), ρ : FiniteDistribution (Fin S)` | match; `EnvironmentStage` enforces `reward ∈ [0,1]` and stochastic rows, so no reward-scaling vacuity; ρ shared across members; family may depend on `K` (as in source) |
| inf/sup | `inf_π̂ sup_M E[…] ≥ c₀ min{…}` | `∀ L, ∃ i, c₀ min{…} ≤ regret` | equivalent for finite `I` (sup = max) |
| Learner | any algorithm, `π^k` depends on trajectories before `k` | `OnlineLearner`: finite seed, `policy σ k τ : ℕ → StationaryPolicy` from the `k` previous episodes | see F-N1/F-N2: no loss |
| Episode data | trajectory `(s_h,a_h,r_h)` | `(s₁, ((a_h, s_{h+1}))_{h<H})`; rewards omitted, `s_{H+1}` included | no loss for the witness family (rewards are the fixed function `1{s<⌊S/2⌋}` of the state) |
| Episode law | `s_1^k ∼ ρ` i.i.d., `a_h ∼ π_h^k(·|s_h)`, `s_{h+1} ∼ P_h` | `episodeLaw = compLaw ρ (episodePathLaw …)`, `onlineHistoryLaw = seqLaw` over episodes | match |
| Regret | `E[Σ_k V_1^⋆(ρ) − V_1^{π^k}(ρ)]` | `Σ_σ w(σ) Σ_τ P(τ) Σ_{k<K} policySuboptimality E ρ (policy σ k τ[:k])`, `policySuboptimality = Σ_s ρ(s)(optimalValue − trajectoryValue)` | match |
| Rate | `min{√(H³SAK), HK}` | `min (√(H³·S·A·K)) (H·K)` over ℝ | match |
| Actions | at most A | exactly `Fin A` everywhere, absorbing states ignore the action | admissible witness |
| Odd S | claimed for all S≥2, proof assumes even | `m = ⌊S/2⌋` copies + unused absorbing state with `ρ = 0`; uses `S ≤ 3m` | covers all S; see SI-a |

## 3. Alternative proof route (Lean) — soundness assessment

I re-derived the Lean route independently from the Lean source text (not compiled by me):

1. `policySuboptimality_ge`: ρ uniform on the `m` copies + Lemma 5.20 per copy (`onlineLBStages_value_gap`) ⇒ per-episode suboptimality `≥ (1/m) Σ_{j,h} ε(H−h)/(16H²)(1 − π_h(i_{j,h}|j))`. Sound: copies are disjoint and a path from `j` only visits `j` or absorbing states (`hard_path_reach`).
2. `history_sum_KL_le`: flipping coordinate `(j,h)` from index `0` to `a'+1` only changes the step-`h` row at state `j`, only for action `a'+1`, by Bernoulli KL `≤ 4ε²/H³` (`stepRow_flip_sum_le`, `stepRow_eq_of_agree`); a path visits `j` only if it starts at `j` (prob. `1/m`); so `Σ_{a'} KL(history_0 ‖ history_{a'+1}) ≤ k·4ε²/(mH³)` by the direct adaptive chain rule on the episode-level `seqLaw` and the step-level `interactionLaw`. I checked this is exactly the right quantity: per visit, at most one alternative accrues KL, so the alternatives' sum is bounded by expected visits × `4ε²/H³` ≤ `(k/m)·4ε²/H³`. Sound. This replaces the source's induced-bandit reduction and the conditioning on `J`.
3. `coordinate_testing`: reverse Fano on `(history_k, ã)` with `ã ∼ π^k_h(·|j)` (the counterfactual action — evaluated at state `j` irrespective of whether `j` is visited, matching `eq:counterfactual-action-online-lb`), all other coordinates fixed to `r`; `Equiv.funSplitAt (j,h)` gives the bijection `I ≃ Fin A × (other coords → Fin A)` so that `coordinate_sum_ge` sums the row bounds to `|I|/3`. Sound.
4. `hard_family_sum_regret`: per seed, regret = Σ_k E_{prefix law}[suboptimality] (`seqLaw_sum_prefix`), then weights `Σ_{j,h} w = ε(H−1)/(32H)`; average over `I` `≥ Kε(H−1)/(96H) ≥ Kε/192`, under `K·4ε²/(mH³) ≤ 2A/9` ⇔ `ε² ≤ mAH³/(18K)`. Then averaged over the seed.
5. `minimax_lower_online`: `ε = min{√(mAH³/(18K)), H/2}`; `√(H³SAK) ≤ 8Kx` uses `S ≤ 3m` (`64/18·m ≥ S` ⇔ `m ≥ 0.28 S`); `HK/1536 ≤ K(H/2)/192`; pigeonhole from the sum over `I`. Arithmetic checked: `c₀ = 1/1536` works.

The route uses only expected visit counts, so no binomial concentration is needed; it is strictly simpler than the printed Cases 1/2 and is not affected by SI-b. I found no gap.

## 4. Source-issue assessment

**SI-a (odd S) — CONFIRMED (proof gap, statement true).** The theorem is stated for every `S ≥ 2` (2446) but the proof assumes `S` even "for simplicity" (3015–3016) and never treats odd `S`. Fix: use `⌊S/2⌋ ≥ S/3` copies and one extra absorbing zero-reward state with zero initial mass; only the constant changes. The Lean construction does exactly this.

**SI-b (Case 1 tail) — CONFIRMED, three defects, conclusion unaffected.** At 3205–3218:
1. The cited Lemma `lem:tail-bound-sum-Bernoulli` (prelim.tex:1010–1014) gives `P(K_j > τ) ≤ 2 exp(−0.19τ)` for `τ ≥ 2pn`; the first term at 3210 uses `P(K_j > 100K/S) ≤ exp(−19K/S)`, dropping the factor `2`.
2. The intermediate inequality `(100K/S) e^{−19K/S} + (2/0.19) e^{−19K/S} ≤ (111K/S) e^{−19K/S}` needs `K/S ≥ (2/0.19)/11 ≈ 0.957`; it is false for `S/2 ≤ K < 0.957 S` (e.g. `K/S = 1/2`: LHS `≈ 4.53e−3`, RHS `≈ 4.15e−3`).
3. With the factor 2 restored, the final bound `≤ 0.01K/S` is false near `K/S = 1/2` (`(200x + 2/0.19)e^{−19x} ≈ 8.27e−3 > 5e−3` at `x = 1/2`; it holds only for `x ≳ 0.5263`).
The printed final value `≤ 0.01K/S` (without the 2) does hold for all `K/S ≥ 1/2` (`4.53e−3 ≤ 5e−3`), and any of the following repairs the step: replace `0.01` by `0.02` (giving `0.99 ε₀K/192`), or use the sharper multiplicative Chernoff bound (`P(Bin > 50μ) ≤ exp(−146μ)`). Theorem 5.19's statement is unaffected (universal constant).

**SI-c (omitted reductions) — CONFIRMED as proof-detail gaps, not errors.** (i) S=2 (2759–2765, 2850–2858): the induced bandit algorithm simulates episodes (steps ≠ h, dummy rounds) with persistent internal state, but Lemma 5.21's class is `π^t(·|x_{t−1})` with no persistent seed; one needs a Kuhn-type mixed→behavioral reduction (the instance-likelihood factor cancels in the conditional seed law, so it holds) or Lemma 5.21 for seeded learners. (ii) General S (3085–3110): "conditionally on `J` … a valid randomized `K_j`-episode algorithm" combines random episode counts, simulation of other components from the prior, and applying the S=2 bound conditionally; asserted in prose only. Both are standard and true; neither is needed by the Lean route.

**Lemma 5.20 weight note.** The printed weight `ε₀(H−h)/(16H²)` is correct; only the proof's unrolling exponent `(1−1/H)^h` should be `(1−1/H)^{h−1}` (harmless: it is a smaller lower bound). The `h = H` term has weight `0`, consistent with `V_{H+1} = 0`. Not a source-fidelity finding for the statement; at most a typo-level remark.

## 5. Proof honesty

- Wrappers: `Lemma5_20_holds := onlineLBSub_value_gap`, `Lemma5_21_holds := bandit_testing`, `Thm5_19_holds := minimax_lower_online` — direct term applications; the probe `Prop`s are syntactically the export types (I compared the binders and bodies in `ValueGap.lean:385–390`, `BanditTesting.lean:85–88`, `MinimaxRegret.lean:319–325`).
- Import-closure grep (70 project files reachable from `StatementProbe.lean`) for `sorry|admit|axiom|opaque|implemented_by|unsafe|native_decide|@[extern|ofReduceBool`: **0 hits**. No `set_option`, `macro`, `elab`, `run_cmd`, `#eval` in the LowerBound / AdaptiveKL files.
- Build evidence (indirect only): every `.olean` under `.lake/build/lib/lean/Formalization/Online/LowerBound/` and `…/Probability/AdaptiveKL*.olean` is newer than its source; `<builder working folder>/last.out` is empty. I did not compile and did not see `#print axioms` output.

## 6. Findings

**BLOCKING:** none.

**MAJOR:** none.

**MINOR**
- M1 (landing). `StatementProbe.lean` imports proof modules (`ValueGap`, `BanditTesting`, `MinimaxRegret`) next to the `Prop`s. Per AGENTS.md, `Formalization/Statements/Ch5.lean` must import only definition modules (`FamilyDefinitions`, `BanditDefinitions`, `RegretDefinitions`), with the wrappers in `Ch5Proofs.lean`, and both new module trees must be imported from `Formalization.lean` before the axiom audit can cover them. Failure scenario: landing the probe as-is would put proof imports into the statement index and leave the modules outside the audit (they are untracked today).
- M2 (evidence). The axiom audit and a full `python3 scripts/check.py` run must be shown on the landed state; this review saw no `#print axioms` output.

**NOTE**
- N1 (finite seed). `OnlineLearner`/`BanditLearner` allow only finite seeds. No loss: because `I` is finite and regrets are bounded, for any measurable continuous-seed learner the vector `(E_U R_i(U))_i` lies in the closure of the convex hull of `{(R_i(u))_i}`, and the Lean statement for finite mixtures gives `max_i ≥ c₀ min{…}` on that hull, hence on its closure. The Lean proof itself also bounds the uniform average over `I` for each seed separately.
- N2 (episode data). Rewards are not recorded in `OnlineEpisode`, `s_{H+1}` is. For the witness family the reward is `1{s < ⌊S/2⌋}`, a known function of the state, so every reward-observing learner is simulated by an `OnlineLearner`. `OnlineLearner` should not be reused for families with instance-dependent rewards without adding rewards to the episode record.
- N3 (actions). All states carry exactly `A` actions; absorbing states ignore the action. This is a valid witness for "at most A actions per state".
- N4 (constant). Lean proves `c₀ = 1/1536`, larger than the constant implied by the printed route (`≈ 3.1e−5`); allowed, since the source only claims some universal `c₀`.
- N5 (Lemma 5.20 hypotheses). `0 < ε ≤ H/2` appear as explicit binders because the stage definitions need them for well-formed rows. They are the source's standing range (2602), not hidden hypotheses.

## 7. Suggested `docs/SOURCE-ISSUES.md` text

**Thm 5.19 / odd S (SI-a).** `chapters/onlineRL.tex:2443–2456` states the bound for every `S ≥ 2`, but the proof (`:3004–3290`) assumes `S` even ("for simplicity", `:3015–3016`) and never treats odd `S`. Repair: take `⌊S/2⌋ ≥ S/3` copies and one extra absorbing zero-reward state with zero initial mass; only the universal constant changes. The formalization uses this construction (`onlineLBStages`, `onlineLBRho`). The statement stays as printed; this is a proof gap.

**Thm 5.19 proof, Case 1 tail bound (SI-b).** `chapters/onlineRL.tex:3205–3218`: (a) the cited `lem:tail-bound-sum-Bernoulli` (`chapters/prelim.tex:1010–1014`) gives `P(K_j > τ) ≤ 2exp(−0.19τ)`, but the first term is bounded by `(100K/S) exp(−19K/S)` without the factor `2`; (b) the step `≤ (111K/S) exp(−19K/S)` requires `K/S ≥ (2/0.19)/11 ≈ 0.957` and fails for `S/2 ≤ K < 0.957S` (at `K/S = 1/2`: `4.53e−3 > 4.15e−3`); (c) with the factor 2 restored, the final `≤ 0.01K/S` fails near `K/S = 1/2` (`8.27e−3 > 5e−3`). Repair: use `0.02K/S` (giving `0.99 ε₀K/192`) or the multiplicative Chernoff bound. Theorem 5.19 is unaffected. The formalization avoids the step (it bounds expected visit counts directly).

**Thm 5.19 proof, omitted reductions (SI-c).** `chapters/onlineRL.tex:2759–2765, 2850–2858, 3085–3110`: the reduction from the MDP learner to a Lemma 5.21 bandit algorithm, and the conditioning on the initial-state sequence `J`, are asserted in prose only. The induced algorithm keeps persistent internal state (simulated steps and components), while Lemma 5.21's class is `π^t(·|x_{t−1})`, so a mixed-to-behavioral reduction is implicitly used. Both steps are true. The formalization instead proves the coordinatewise testing bound directly from the adaptive KL chain rule on the episode-history law (`HistoryKL.history_sum_KL_le`).

(Lemma 5.20: no SOURCE-ISSUES entry needed. Optional typo remark: in the proof, `:4920–4930`, the exponent `(1−1/H)^h` should be `(1−1/H)^{h−1}`; the printed bound remains valid.)

## 8. VERDICT

- **Lemma 5.20 (`Lemma5_20`)**: VERDICT — **FAITHFUL** to the printed statement (original, not corrected). Wrapper honest. Approve, conditional on M2.
- **Lemma 5.21 (`Lemma5_21`)**: VERDICT — **FAITHFUL** (the learner class is a superset of the source's, so the statement is at least as strong). Wrapper honest. Approve, conditional on M2.
- **Theorem 5.19 (`Thm5_19`)**: VERDICT — **FAITHFUL** to the printed statement as an original (not `_corrected`) entry. Quantifiers, family constraints, ρ, learner class, regret and rate match; finite-seed and reward-free episode records lose nothing (N1, N2). The proof route is an alternative and I found it sound. SI-a, SI-b and SI-c are source *proof* issues to record in `SOURCE-ISSUES.md`; they do not affect the statement. Approve, conditional on M1 and M2.

## Addendum (written after sections 1–8)

After finishing the sections above I read only the SI-a/SI-b paragraphs of `the private preflight note (Thm5_19)` (lines 140–165). My independent numbers agree with them: the factor-2 failure region is `K/S ∈ [0.5, ≈0.526]` (`8.27e−3` vs `5e−3` at `1/2`), and the `111K/S` step needs `K/S ≥ 0.957`. The preflight lists other repairs (threshold `200K/S`, or Case 1 starting at `K ≥ S`), and either one is fine. No verdict changed.
