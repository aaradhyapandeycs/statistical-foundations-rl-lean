# CHECK: Theorem 7.7 plan (`thm:Q-FTRL`)

Public copy of the independent critic report; local paths removed.

**Scope.** This is an independent plan check against the source only.
- No Lean or lake command was run, and nothing under `Formalization/` or `.lake` was touched.
- No paper was fetched, including li2022minimax.
- I read AGENTS.md, SOURCE-ISSUES C39/C40/C45, the Theorem 7.6 plan check (docs/critic-thm7-6-plan-check.md, for format) and marl.tex:13–346 and :420–510,
  and wrote down my own reading (§1) before reading the plan's conclusions.
- Every mathematical step in plan §3 was re-derived by hand (§3). Library names were checked by grep (§4).

**Files written.** Only this file.

## 0. Pins

| File | SHA-256 |
| --- | --- |
| `source/upstream/tex/chapters/marl.tex` | `8fadfab2c41ecad62349e27478adf2018047ad24a363c63a9918279238d12ffb` (matches plan §0) |
| the builder's private plan (as reviewed) | `56b14e1bc4ce97ed25de30560606e8890f0c71360ac54f671c2029ab6900e9a0` (verified) |

## 1. My reading of the printed statement (written before reading the plan)

- **Text (:441–467).** For every δ ∈ (0,1) and ε ∈ (0,H] "there exists a model-based algorithm (i.e., Q-FTRL)" that, with
  probability ≥ 1−δ:
  - (a) in a two-player zero-sum game, finds π̂_NE with gap ≤ ε using Õ(SAH⁴/ε²) samples;
  - (b) in a general-sum game, finds π̂_CCE with gap ≤ ε using Õ(H⁴SΣ_iA_i/ε²) samples.
- **Definitions.**
  - gap is step-1 only, max over s and i (:326–342).
  - An ε-NE must be a **product** policy, and an ε-CCE may be joint (:345–346).
  - The best response is the max over Markov π′_i of V^{π′_i × π_{−i}}, where π_{−i} is the marginal of π (:119–126).
  - Zero-sum means r₂ = −r₁ with r₁ ∈ [0,1] (:50–54). The footnote allows a constant shift for player 2.
  - The generative model returns only s′ (:306–311). Rewards are known (generative_model_model_based.tex:31; same convention as `Thm7_8_corrected`).
- **Ambiguities.**
  - The witness is undefined (:432).
  - A is undefined. The lower-bound discussion at :507 ("minimax optimal for NE", against H⁴S·max_iA_i/ε² in Thm 7.8) points to A = max(A₁,A₂).
  - Õ is unspecified.
- **CCE ⇒ NE by marginals, under the step-1 definitions (my own derivation).**
  - Setup: π is an ε-CCE with marginals μ, ν, and σ = μ×ν.
  - σ has the same opponent marginals as π. So V^{†,ν}_1 and min_{ν′}V_1^{μ×ν′} are the same objects for σ and π.
  - Player 1's CCE inequality gives V^{†,ν}_1 ≤ V^π_1 + ε.
  - Player 2's CCE inequality, with V₂ = −V₁ on steps 1..H, gives min_{ν′}V₁^{μ×ν′} ≥ V^π_1 − ε.
  - Since ν is one of the ν′: min_{ν′}V₁^{μ×ν′} ≤ V₁^σ ≤ V^{†,ν}_1. Hence gap_1(σ) ≤ 2ε and gap_2(σ) ≤ 2ε, pointwise in s.
  - **Factor 2 confirmed.**
  - Shifting r₂ by +1 changes every player-2 step-1 value by the same H, so the gap is invariant.
- **Edge cases.**
  - Values lie in [0,H] (player 2 in [−H,0]), so gap ≤ H. At ε = H the claim is trivially true with 0 samples. This is harmless for an upper bound.
  - A_i = 1: gap = 0.
  - m = 1: an MDP with H⁴SA/ε², which is the known nonstationary rate, so true.
  - I found no reading under which (a) or (b) is false or vacuous on (0,H) for the max/sum readings of A with polylog factors.

My reading agrees with plan §1.2–1.4, except for the naming decision (§2, Q1) and the equivalence remark in §1.3 item 7 (§2.4).

## 2. Statement reading

### 2.1 Existential reading and Õ: FAITHFUL OR STRONGER

- **Quantifier order.** The plan's Prop places ∃(N, rule, out) after the size, reward and accuracy binders and **before** ∀P. This is the right
  order: the algorithm may use the known reward, ε and δ, but not the kernel.
- **Strength.** The fixed universal C, the single factor log(4HSΣA/δ) with no ε, and the **sure** (deterministic) query count are all at least as strong as any
  standard reading of "total sample complexity Õ(·)". Any polylog(S,H,ΣA,1/δ,1/ε) reading follows.
- **Q4: no ε in the logarithm.** This is achievable. The analysis uses fixed-λ Freedman, so it needs no peeling and no union bound over T or over
  λ (re-derived in §3.4). Acceptable.
- **The algorithm class.**
  - Rule randomness only, no seed, and a deterministic output make the class narrower than the `Thm7_8_corrected` seed class, so the existence claim is stronger.
  - It cannot cheat:
    - N is the history length.
    - `genEnv` maps the query step `q.1 : Fin H` to `transition (q.1+1)`, the same kernel `valueJ` uses at that step.
    - The rule sees only the history and the binders.
- **Not too strong.**
  - The rule must exist for every t, including t ≥ N, so `Query` must be nonempty. This is why the S ≥ 1 and A_i ≥ 1 binders are needed, and they are the weakest that work.
  - H ≥ 1 already follows from 0 < ε ≤ H.

### 2.2 Max reading of A: CORRECT AND STRONGEST

- max ≤ A₁+A₂ ≤ 2max, and A₁ = A₂ = A is a special case. The max reading implies the other two.
- It also matches the optimality remark at :507.

### 2.3 Added binders and reward hypotheses: WEAKEST

- `1 ≤ S`, `∀ i, 1 ≤ A i`.
- Rewards are constrained only on steps 1..H. `valueJ`/`value` with k = H from h = 1 read rewards only at steps 1..H, as I checked in `Marl78Defs.valueJ` and
  `MarlPrinted78.value`.
- The zero-sum relation r₂ = −r₁ is also imposed only on steps 1..H.
- **m = 0.**
  - `Query 0 S H A` is nonempty when S,H ≥ 1.
  - `gapJ` is an `iSup` over `Fin 0`, which is 0 in ℝ.
  - The bound's RHS is C·…·0·log 0 = 0, so N = 0 works.
  - No `1 ≤ m` binder is needed.

### 2.4 One algorithm versus two clauses: plan §1.3 item 7 is INACCURATE (required fix 2)

- **The plan's claim.** On the overlap r ≡ 0 (steps 1..H, m = 2), the NE-mode output "is also an ε-CCE within the general-sum budget, because A ≤ ΣA".
- **This does not follow from the Props.** The NE budget has log(8HS·max/δ), and this can exceed the CCE budget's log(4HSΣA/δ) times the factor
  ΣA/max.
- **Counterexample to the abstract claim.** A = (100, 1), H = S = 1, δ → 1:
  - NE budget 100·log 800 ≈ 668;
  - CCE budget 101·log 404 ≈ 606 (same C).
- **What is true.**
  - On the overlap every policy has gap 0, so a combined algorithm can take N = 0 there.
  - Alternatively, double C, since log(8HSΣA/δ) ≤ 2·log(4HSΣA/δ).
  - The concrete witness is fine: its NE-mode count is HS(A₁+A₂)T′ ≤ 4·2501·H⁴SΣA·L/ε², with the same L.
- **The conjunction of two clause-wise existentials is acceptable (Q6).** The docstring must state the equivalence correctly ("one algorithm that branches on the
  known reward, taking N = 0 on the overlap r ≡ 0"), or drop the word "equivalent".

### 2.5 Q1, naming: use `Thm7_7_restricted` (required fix 1)

- **The literal claim.**
  - The printed claim is "there exists a **model-based** algorithm **(i.e., Q-FTRL)**" with the stated guarantee.
  - The proposed Prop proves "there exists an algorithm" with the guarantee.
  - It does not establish that the witness is Q-FTRL, which is undefined in the monograph (:432).
  - It does not establish that the witness is "model-based". The plan's witness never forms P̂. It estimates P_hV̄_{h+1} from single next-state samples, and is
    arguably a model-free, Q-learning-style procedure.
- **The export is weaker than the literal statement.** Under the literal reading it concludes less. AGENTS.md says such a result gets a `_restricted`/`_corrected` entry.
- **Closest precedent.** C32/`Thm6_16_restricted` ("there exists a variant of the above VI-LCB algorithm", proved for one explicit
  variant from scratch) and C33/`Thm6_17_restricted`, not C42/`Thm7_10`.
  - C42 is a choice between readings of a constant's quantifier position, and both readings are statements about the same objects.
  - Here the dropped descriptors name the witness.
- **Required.**
  - Name the entry `Thm7_7_restricted`, with the same Prop.
  - The docstring opens with: "restricted variant: proves the existential sample-complexity guarantee with an explicit reconstructed witness; that the witness is Q-FTRL or model-based is not established".
  - COVERAGE status: "Restricted variant proved".
  - C39 gets the restricted-result paragraph in the C32 style.
- **The alternative.** The bare name `Thm7_7` would be defensible only if the lead explicitly records "(i.e., Q-FTRL)" and "model-based" as non-mathematical
  attributions in C39 and justifies the departure from C32. I do not recommend it.

## 3. Mathematics: all re-derived; VERIFIED at the H⁴ rate

Fix i, h and s. V̄_{h+1} is frozen before stage h by backward induction. Within round t, every query law depends only on the pre-round history.

- **(F1) Second-order Hedge: CORRECT.**
  - The potential step is Φ_t − Φ_{t−1} = ⟨π,q⟩ + η⁻¹log E_π e^{η(q−⟨π,q⟩)}.
  - With |η(q−⟨π,q⟩)| ≤ ηR ≤ 1, `Real.abs_exp_sub_one_sub_id_le` (exists in the pinned Mathlib) gives E e^x ≤ 1 + η²Var. Then log(1+u) ≤ u.
  - Φ_0 = log A/η and Φ_T ≥ max_b G_T(b).
  - Dividing by T gives U ≥ max_b (1/T)Σ_t q̂^t(b).
  - **Computability.** β uses only q̂, π^t, η and T, all observed or algorithm-internal. It does not use P. **The bonus is computable from data.**
- **(F2) Mixture variance: CORRECT, and used in the right direction.**
  - π̂_h(s) is the t-average of ⊗π^t. So the law of (a_{−i}, s′) under b×π̂_{−i} is the t-average of the laws under b×π^t_{−i}.
  - The variance of a mixture is the average variance plus the variance of the means, which is ≥ the average variance.
  - Every use upper-bounds an average of conditional variances by the variance under the mixture policy: E1 → v^{ρ*}, E2/E3 → v^{π̂}. That is the true direction.
  - The linear identities (1/T)Σq̃^t(b) = E_{b×π̂_{−i}}[r + PV̄] and (1/T)Σm^t = T^{π̂}V̄ hold.
- **(F3) Near-supersolution total variance: CORRECT.**
  - **The per-step inequality.** v = E[(r+f′)²] − (f−Δ)². Using r² ≤ r and dropping −Δ²:
    v ≤ E[r(1+2f′)] + E P f′² − f² + 2fΔ.
  - **Telescope.** Eval_ρ(EPf²_{next} − f²)_1 = E f_{H+1}² − f_1² = −f_1² ≤ 0.
  - **Reward term.** Eval_ρ(r(1+2f′)) ≤ (1+2H)V^ρ_1 ≤ H + 2H², using r ≥ 0 and f ≤ H.
  - **Cross term.** 2fΔ ≤ 2HΔ⁺, using f ≥ 0. Then Eval(Δ)_1 = f_1 − V^ρ_1 ≤ H, using V^ρ ≥ 0. So Eval(Δ⁺) ≤ H + Eval(Δ⁻).
  - **Total.** H + 4H² + 2H·Eval(Δ⁻) ≤ 5H² + 2H·Eval(Δ⁻), using H ≥ 1.
  - **Hypotheses actually used.**
    - 0 ≤ f_t ≤ H on 1..H, f_{H+1} = 0;
    - r_{i,t} ∈ [0,1] on 1..H;
    - H ≥ 1.
    - V̄ ≥ 0 holds because U ≥ max_b avg q̂ ≥ 0.
  - **Note.** v here is the variance over the **joint** law of (a, s′). `Marl76.evalJ_variance_add_sq_le` uses only the transition variance with the exact value, so it is
    a proof pattern, not a reusable special case (suggestion S2).
- **§3.2 Upper side: CORRECT.**
  - **Unclipped case.** V^†_h = (1/T)Σq̃(b*) + E_{ρ*}P(V^†−V̄)_{h+1}, by brW/brQ and the Bellman recursion at the greedy b*. Then (1/T)Σq̃(b*) = (1/T)Σq̂(b*) + N ≤ U + N⁺.
  - **Clipped case.** V^† ≤ R_h, because r ∈ [0,1] on steps h..H.
  - **Δ^{ρ*} ≥ −N⁺.**
    - Unclipped: V̄ = U ≥ avg q̂(b*) = T^{ρ*}V̄ − N.
    - Clipped: R_h ≥ 1 + R_{h+1} ≥ r + V̄_{h+1}.
  - b* depends on the data, through π̂ and the true V^†. It is covered because E1 is union-bounded over **every** b, and no data-dependent index enters
    a union bound.
- **§3.3 Lower side: CORRECT.**
  - V̄ ≤ U = T^{π̂}V̄ + M + β. Induct.
  - Δ^{π̂} ≥ −M⁻ in both cases, since β ≥ 0.
- **§3.4 Events: CORRECT.**
  - **E1.** X = q̃ − q̂ has conditional mean 0 given **any** prefix, because the step law is rule ⊗ genEnv with a_{−i} ∼ ⊗π^t_{−i}. |λX| ≤ λR ≤ 1/4.
    Then E e^{λX} ≤ 1 + λ²EX² ≤ e^{λ²EX²}.
  - **E2±.** Y = π(b)(q̂−q̃), and E Y² ≤ π(b)Var_t(b). By `finite_conditional_total_variance`,
    Σ_bπ(b)Var_t(b) ≤ Var_{⊗π^t}(r+V̄).
  - **E3.** y = z/H² ∈ [0,1], and e^y ≤ 1 + (e−1)y ≤ 1 + 2y. Also Σ_bπ(b)E(q̂(b)−m^t)² = Var_{⊗π^t}(r+V̄), because m^t is the overall mean (law of total variance).
    Var_{π^t}(q̂) ≤ second moment about m^t.
  - **Event count.** HS(ΣA + 3m) ≤ 4HSΣA = K, using m ≤ ΣA when A_i ≥ 1. Each event fails with probability ≤ e^{−L} = δ/K.
  - **No conditioning on the future.** q̃, Var_t and m^t are functions of the prefix only, since V̄_{h+1} is from an earlier stage.
  - **No use of the true kernel by the algorithm.** P appears only in q̃, V^† and Var_t, which are analysis objects.
- **§3.5–3.6 Self-bounding: CORRECT.**
  - **Upper.** Ξ_1 ≤ λ(5H² + 2HΞ_1) + HL/(λT). With 2λH ≤ 1/2, Ξ_1 ≤ 10λH² + 2HL/(λT).
  - **Lower.** W ≤ 5H² + 2H(λW + HL/(λT)), so W ≤ 10H² + 4H²L/(λT).
  - **Lower-side sum.** Eval(β+M) ≤ HL/(ηT) + 2ηW + ηH³L/T + λW + HL/(λT).
  - All bounds hold pointwise in s with the same s on both sides.
- **§3.7 Arithmetic: CORRECT.**
  - With λ = η = √(L/(HT)) and x = √(H³L/T): λH² = x, HL/(λT) = x, and H²L/T = λH·x ≤ x/4.
  - So λW ≤ 10x + 4λHx ≤ 11x, and ηH³L/T = λH·x²/H ≤ x²/(4H).
  - Upper side 12x, lower side x + 33x + x + x²/(4H). Gap ≤ 47x + x²/(4H).
  - T ≥ 2500H³L/ε² gives x ≤ ε/50 ≤ H/50, so x²/(4H) ≤ ε/10⁴. Gap ≤ 0.9401ε < ε.
  - **Side conditions.** λH ≤ 1/4 ⇔ T ≥ 16HL, which follows from T ≥ 2500HL (because ε ≤ H). It holds on all of (0,H], including H = 1.
- **Sample count: CORRECT.**
  - N = HSTΣA ≤ 2501H⁴SΣA·L/ε², using H³L/ε² ≥ HL ≥ log 4 > 1.
  - Zero-sum at ε/2: factor 4. With A₁+A₂ ≤ 2max and log(4HS(A₁+A₂)/δ) ≤ log(8HS·max/δ), this gives C = 20008.
- **H-power: H⁴, not H⁵.** T = Θ(H³L/ε²) rounds per (h,s), times ΣA queries, times HS.
- **§6 Fallback (H⁵): SOUND.** It is not needed, since the main route verified.
  - Per step, the bound is R_h(√(logA/(2T)) + 2√(2L/T)) ≤ 3.54R_h√(L/T), and Σ_hR_h ≤ H², so gap ≤ 4H²√(L/T).
  - T = ⌈16H⁴L/ε²⌉ gives N ≤ 17H⁵SΣAL/ε².
  - There are fewer events (HS(ΣA+2m) ≤ K).
  - **Note.** When A_i = 1, the prescribed η = √(8log A/(TR²)) is 0. The uniform Hedge is fine, but the builder must not divide by η.

**Conclusion of §3.** I found no error, including no adaptivity error, no hidden kernel dependence, no misuse of variance or telescoping, and no H-power slip.
The proof is new reconstruction mathematics, so the builder's Lean must still be source-reviewed.

## 4. Lean design check (grep only)

- **Names confirmed, with the stated meanings.**
  - `MarlPrinted78`: `MarkovGame`, with fields `transition` then `reward`, so `⟨P, rew⟩` is right.
  - `PlayerPolicy`, `ProductPolicy`, `value`, `gap` (an iSup over s and i).
  - `Marl78Defs`: `JointPolicy`, `deviate` (the law of `update a' i b` with a′ ∼ π and b ∼ π′ independent, so the −i marginal is π's), `valueJ`, `bestResponseValueJ`, `gapJ`, `Query = Fin H × Fin S × JointAction`, `genEnv` (step `q.1+1`).
  - `Marl78Product`: `toJoint`, `valueJ_toJoint`, `deviate_toJoint_sum`, `gapJ_toJoint`, `jointProb_sum_split`.
  - `Marl76BestResponse`: `brQ`, `brW`, `brPolicy` (a greedy point mass; it needs `0 < A i`), `valueJ_brPolicy`, `bestResponseValueJ_eq_brPolicy`, `bestResponseValueJ_eq_of_one`.
  - `Marl76Eval`: `evalJ`, `evalJ_le_affine`, `valueJ_mem_Icc`, `evalJ_variance_add_sq_le` (transition variance only; see the note in §3).
  - `AdaptiveKLDefinitions`/`AdaptiveKL`: `seqLaw`, `seqLaw_succ_prob`, `sum_tuple_succ`, `interactionKernel` (rule ⊗ env per step), `interactionLaw`, `seqLaw_sum_prefix`, `seqLaw_sum_step`, `interactionLaw_sum_steps`.
  - `FiniteDistribution.variance`, `OnlineRL.finite_conditional_total_variance`.
- **Name correction.** `pointMass` is `StatisticalRL.EnvironmentStage.pointMass` (`Formalization/MDP/PointMassDefinitions.lean`), not a `Marl78` name.
- **Missed reuse (required fix 4).** Plan §4.1 says there is no discrete supermartingale or union bound on finite adaptive laws. But these exist:
  - `StatisticalRL.Ch7Rest.Rlhf.adaptive_prod_le`, `adaptive_markov` and `union_bound_sum` (`Formalization/RLHF/VPO/Adaptive.lean`). These are exactly the history-dependent kernel, nonnegative factors with conditional mean ≤ 1, Markov, and finite union bound.
  - The analogous `LCBQFinite.lemmaG` (`OfflineRL/FiniteLCBQ/Supermart.lean`).
  - P1a should bridge `seqLaw`'s probability to the product form these lemmas use, or move the lemma to `Probability/` and reuse it, rather than reprove it.
- **Generality of the algorithm model.** For an *existence* claim, a narrower class only strengthens the result. The class is still adequate for the witness:
  - randomized per-query laws (fresh a_{−i} draws);
  - full adaptivity on the prefix;
  - access to the reward table, ε and δ through the binders;
  - no access to P.
- **Size.** 2800–3800 lines is plausible against Marl76* (about 2390 lines) and Marl76+78 (about 4130 lines).
  - P4 (locality over the flat schedule) is the realistic overrun risk, possibly 1.5× its estimate.
  - Prove locality once for a generic "staged rule" (decoded state at τ depends only on the `Fin.castLE` prefix), as the plan's risk 1 suggests. Do not prove it per quantity.

## 5. Statement-index draft (§5)

- **Self-contained.** Every quantifier and hypothesis is explicit: C first; then m, S, H, A, the S/A binders, δ, ε, the reward and its range on 1..H; then ∃N, rule, out; then the count bound; then ∀P and the probability.
- **No hidden hypotheses.** It uses only definitions from `Marl78Defs`, `MarlPrinted78` and `AdaptiveKLDefinitions`, so the import rule is satisfied.
- It matches the chosen reading. Clause (a) outputs `ProductPolicy` and uses the book's product `gap`. Clause (b) outputs `JointPolicy` with `gapJ`.
- **Required edits.**
  - Rename to `Thm7_7_restricted` (fix 1).
  - Correct the "equivalent to one algorithm" sentence (fix 2).
  - Cite generative_model_model_based.tex:31 for known rewards.
  - Cite :476 for "uniformly over ε" (fix 3).
- **Optional.** Split into `Thm7_7_restricted_CCE` / `_NE` sharing C. This is not needed.

## 6. Required fixes

1. **Naming (Q1).** Use `Thm7_7_restricted`, with the same Prop.
   - Docstring and COVERAGE: "Restricted variant proved: existential guarantee with an explicit reconstructed witness; not shown to be Q-FTRL or model-based".
   - Add a C39 paragraph in the C32 style.
   - Drop "no restriction" language from the proposed C39 update.
   - *Justification:* §2.5. The literal claim names the witness, AGENTS.md treats a weaker export as `_restricted`, and C32/C33 are the precedent.
2. **One-algorithm remark (§1.3 item 7, docstring).** Replace "because A ≤ ΣA" with the correct argument: N = 0 on the overlap r ≡ 0, or a doubled C.
   - *Justification:* §2.4 counterexample A = (100,1).
3. **Line references.**
   - The "uniformly over ε ∈ (0,H]" sentence is :476, not :475.
   - The commented "KSHΣA" remark is :480–481, not :475.
   - Known rewards: generative_model_model_based.tex:31.
4. **P1a reuse.** Evaluate and reuse, or relocate to `Probability/`, `Rlhf.adaptive_prod_le` / `adaptive_markov` / `union_bound_sum` (`VPOAdaptive712.lean`, currently uncommitted) or `LCBQFinite.lemmaG`, and record the decision.
   - *Justification:* the plan's "nothing reusable" claim is wrong, and the project's guidance asks for a well-organized library.
5. **F3 as a library lemma.** State it with exactly the used hypotheses: 0 ≤ f ≤ H on the window, f at the end = 0, r ∈ [0,1] on the window, H ≥ 1, and v = the variance under the joint stage law of (a, s′).
   - Do not present it as a generalization of `evalJ_variance_add_sq_le`, which has a different v.

## 7. Optional suggestions

- **S1.** Add the one-line Lean lemma "`deviate π i π′` depends only on the −i marginal of π" (m = 2 suffices for §3.8). Use it together with `gapJ_toJoint` for the NE clause.
- **S2.** Keep the zero-sum reduction (P7) independent of the algorithm. Prove "ε/2-CCE of the shifted game ⇒ product of marginals is an ε-NE" as a standalone theorem about `gapJ`/`gap`.
- **S3.** Skip `Thm7_7_trivial_endpoint`. It adds nothing.
- **S4.** Build P1b in second-order form, so the H⁵ fallback stays a corollary, as the plan recommends.

## 8. Answers to Q1–Q7

- **Q1.** Use `Thm7_7_restricted`, with the same existential Prop (§2.5).
- **Q2.** §3.1–3.7 independently verified, including C = 20008, 2500, the gap of 47x + x²/(4H) < ε, and that x²/(4H) ≤ ε/10⁴ on all of (0,H].
- **Q3.** Constrain rewards only on 1..H. The algorithm must see the reward table, which is the book's convention: the sampler returns only s′.
- **Q4.** Yes. log(4HSΣA/δ) without ε is stronger than needed, and the fixed-λ Freedman proof attains it.
- **Q5.** Yes. The factor 2 is correct under the step-1 definitions and `deviate`'s marginal semantics. The +1 shift for player 2 is harmless (§1).
- **Q6.** The conjunction is acceptable, with the corrected justification (§2.4).
- **Q7.** No missed edge case.
  - m = 0: Query nonempty, gap 0, N = 0.
  - H = 1, A_i = 1 and δ → 1 (L ≥ log 4) work.
  - ε = H is trivially true and harmless.

## 9. Verdict

**GO WITH FIXES.**
- The mathematics is sound at the printed H⁴ rate with C = 20008.
- The statement reading is faithful or stronger in every quantitative respect.
- Fixes 1 (naming) and 2 (equivalence remark) must be applied before the statement entry lands. Fixes 3–5 are cheap and should be applied before P1 starts.
