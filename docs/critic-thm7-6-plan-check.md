# CHECK: Theorem 7.6 plan (`thm:sample-complexity-plug-in-marl`) and candidate C45

Public copy of the independent critic report; local paths removed.

**Scope.** This is an independent paper-proof check against the source only. No Lean was compiled.
- I reconstructed the printed statement from `marl.tex` before reading the plan.
- I then read the builder's private plan and its script `<builder plan folder>/check_thm7_6.py` and tried to refute both.
- I wrote my own stdlib-only script. It shares no code with the plan's script.

**Files written.** Only this file and `<reviewer check folder>/{critic_thm7_6.py,critic_thm7_6.out}`.

## 0. Pins

| File | SHA-256 |
| --- | --- |
| `source/upstream/tex/chapters/marl.tex` | `8fadfab2c41ecad62349e27478adf2018047ad24a363c63a9918279238d12ffb` (matches plan) |
| `source/upstream/tex/chapters/generative_model_model_based.tex` | `b7e7abfb2c2cb2c0dd82470db5ecac3a67d7163682246d499935d9130214ac4d` (matches plan) |
| the builder's private plan (as reviewed) | `30f98275a9748f038695fbff21b49988cc96656707095e7a29a5801afb003a1c` |
| `<builder plan folder>/check_thm7_6.py` / `.out` | `fbad1db5…b4596` / `44fc1533…729f0` (match plan §0) |
| `<reviewer check folder>/critic_thm7_6.py` | `a2f6bbb56dc2ed3a6c913018a707a2a335d29729306641e2ccbdd72d164eb054` |
| `<reviewer check folder>/critic_thm7_6.out` | `c6f0080a0d9949bffe60eac211241d3ff6efe75f66d0bee4fc238d600b5edf20` |

**Script.** Run with `cd <reviewer check folder> && python3 -I critic_thm7_6.py`. It is seeded and takes about 2 s.

## 1. My reconstruction of the printed statement (done before reading the plan)

### Statement, marl.tex:384–399

- **Citation.** The theorem is cited to zhang2020model-based and shi2024sample. The book gives no proof.
- **Hypotheses.**
  - δ ∈ (0,1).
  - π̂_NE and π̂_CCE are "the NE and CCE returned by the planning oracle in the above model-based plug-in algorithm".
  - 0 < ε ≤ √H.
- **Conclusion.** With probability ≥ 1−δ, both `gap(π̂_NE) ≤ ε` and `gap(π̂_CCE) ≤ ε` hold. This is a joint event.
- **Sample-size condition.** `N ≥ C₁H³ε⁻² log(SHN∏A_i/δ)` for a large enough universal constant C₁. N appears inside the log.
- **Notation.** `\mathsf{gap}` is the macro `\NEgap` (commands.tex:98).

### Objects

- **Model.**
  - General-sum m-player finite-horizon game with non-stationary P_h (:37–38).
  - Deterministic known rewards r_{i,h} ∈ [0,1] (:41–43).
  - Markov policies, joint or product (:71–87).
  - V^π_{i,h} (:96–106). V^{⋆,π_{−i}} is the sup over Markov π'_i of V^{π'_i×π_{−i}} (:119–126).
  - Simultaneous attainment over h is asserted at :128–129.
- **NE** (:213–221, label :220). A product π with `V^π_{i,1}(s) = V^{⋆,π_{−i}}_{i,1}(s)` for all s and i. This is a **step-1 condition only**.
- **CCE** (:230–238, label :237). The same condition with ≥, for a joint π.
- **Gap.** gap is the max over s and i at step 1 (:327–342).
- **Generative model.** One independent s' per query (:306–315).
- **Plug-in algorithm.**
  - N i.i.d. samples per (s, **a**, h) give P̂, and the empirical game keeps the true r (:358–374).
  - The planning step (:377) reads: compute "either a Nash equilibrium π̂_NE or a CCE π̂_CCE of the empirical game using an
    appropriate planning oracle".
  - The examples given are Nash value iteration for zero-sum games, an LP, and no-regret dynamics.
  - **No selection or causality property is stated.**

My reconstruction agrees with plan §1, with the line-reference corrections in §7 below.

## 2. Claim (1): transcription and the "any oracle" reading

**Verdict: CONFIRMED.**

- **Literal reading.** The only constraint the text puts on the oracle is that it returns an NE or a CCE of the empirical game, in the book's sense.
- **Data dependence.** Because the oracle is applied to the empirical game, it is a function of the data.
- **Quantification.** In a formal statement both oracles must be fixed deterministic maps from empirical games to policies, quantified
  outside the probability. The plan does this correctly. Putting "∀ oracle" inside the probability would be even weaker.
- **Joint conclusion.** The conjunction "NE and CCE jointly with probability ≥ 1−δ" is transcribed correctly.
- **Threshold.** Keeping N inside the log is correct.

## 3. Claim (2): the counterexamples

### CE1 (two-player zero-sum plus a dummy, h = 1 NE only)

**Verdict: VALID, but the plan's stated bound and construction description are wrong.**

- **The plan's wording is not an NE.** Plan §1 says to play "good" only at the s_j seen in P̂₁(·|s₀,·) and claims a gap of at least `1 − N/K`.
  - If the good set is only the support of the on-path row (s₀,(0,0)), the policy is **not** an h = 1 NE of the empirical
    zero-sum game.
  - The dummy player 2 has r₂ = −r₁. Player 2 can deviate at step 1 to the row (s₀,(0,1)), whose support contains states where player 1 plays "bad". Player 2 then gains.
  - My script, mode `onpath`, gives an empirical h = 1 gap of 1.0.
- **What the plan's script actually does.** It takes the union of all four rows.
- **The correct statement.** The good set must contain the supports of the on-path row and of every unilateral-deviation row:
  (0,0), (1,0) and (0,1). That is at most 3N states. The bound is then `gap ≥ 1 − 3N/K`, or `1 − 4N/K` with the plan
  script's union of all four rows.
- **Script output, mode `unilateral`.** The empirical h = 1 gap is 0 and the empirical perfect gap is 1, so the policy is not
  perfect. The true gaps are 0.867, 0.925 and 0.970, against bounds of 0.85, 0.925 and 0.97.
- **Alternative.** The bound `1 − N/K` holds if player 2's reward is identically 0, but that game is not zero-sum.
- **Conclusion.** CE1 refutes "any h = 1 NE oracle", even for zero-sum games. It does not refute Nash value iteration,
  which is perfect and causal. **Required fix:** restate CE1 with the unilateral-row union and the bound 1 − 3N/K.

### CE2 (coordination game, perfect product NE)

**Verdict: VALID. Re-derived by hand and checked numerically.**

- **The construction.** π plays risky at s₀ at step 1. At step 2 it plays (1,1) on B = supp P̂₁(·|s₀,(1,0)) and (0,0) elsewhere.
- **It is a perfect NE of the empirical game for every data set.**
  - **Step 2.** Both (1,1) and (0,0) are stage NE. At s_safe every profile is a stage NE.
  - **Player 1 at step 1.** Under π, player 1's empirical value is P̂(B) = 1. Deviating to safe gives ½.
  - **Player 2 at step 1.** Player 2 already receives 1, which is the maximum payoff, so the row (s₀,(1,1)) cannot help.
  - **Starts at h = 1 from s_j or s_safe.** These self-loop into stage NE.
- **True gap.** It is at least ½ − |B|/K ≥ ½ − N/K.
- **Script output.** For every sampled data set the maximum empirical perfect gap is 0. The minimum true gap equals the bound:
  0.375, 0.45 and 0.475.
- **The printed threshold can be met.**
  - Take S = 8N, H = 2, ε = ¼, δ = ½ and ∏A = 4. The condition reads `N ≥ 128·C₁·log(128N²)`, which holds for all large N and any C₁.
  - The plan writes `64N²·…`, but the argument is 128N². This does not matter.
  - My minimal N values are 2638 for C₁ = 1, 1 718 582 for C₁ = 400, 4 545 447 for C₁ = 10³, and 6 401 487 716 for C₁ = 10⁶.
  - In each case the gap is ≥ ½ − N/(8N−2) ≈ 0.375 > ε.
- **Both clauses fail.** CE2's π is also a CCE, so taking both oracles equal to it refutes the joint conclusion. Its probability is 0,
  which is below 1−δ.
- **Conclusion.** CE2 refutes the literal printed statement for **every** C₁. It also refutes the statement when the oracle is
  strengthened to return subgame-perfect equilibria.

### CE2′ (S ≪ N, all states seen)

**Verdict: Heuristic only. Do not cite it as a proof.**

- **What the numbers show.** The `√(S/N)` behaviour is a Monte-Carlo observation.
- **Equilibrium status.** The construction (smallest B with P̂(B) ≥ ½) is a valid perfect empirical NE.
- **What would be needed.** Turning it into a threshold refutation would need a lower bound on ½ − P(B), which is not proved.
  It is not needed for C45.
- **Recommendation.** Keep it out of SOURCE-ISSUES, or label it "numerical illustration".

### Is the issue under-specification or falsity?

**Classification: FALSE AS PRINTED, caused by an omitted hypothesis on the planning oracle.**

- **The equilibrium notion cannot rescue it.** No reading of the oracle that constrains only the *equilibrium notion* of its output
  (h = 1 as defined, or subgame-perfect) makes the statement true, by CE2.
- **The intended repair is only partly identifiable.**
  - Nash value iteration, the named zero-sum example, is backward induction and hence causal.
  - The book's single-agent analogue states the causal-decoupling mechanism explicitly (generative_model_model_based.tex:**2549**).
  - The text does not say that the LP or no-regret CCE methods are run stagewise.
- **Recommended wording.** Say "false as printed; restricted variant under a causal-oracle hypothesis that matches the
  backward-induction planners named at :377". Do not say "the intended theorem".

### The `0 < N` issue

**Verdict: REAL for the formalization, a convention issue in the book. Disclose it; it is not part of C45's falsity.**

- **In the book.** With N = 0 the estimator P̂ = (1/0)·Σ is undefined, and the condition reads `0 ≥ C·log 0`, which is −∞ in the
  extended-real convention. The algorithm clearly presupposes N ≥ 1.
- **In Lean.** `Real.log 0 = 0`, so the printed condition holds at N = 0 while the empirical game is junk.
- **Precedent.** Treat it like `Thm3_2_positiveN` (Ch3.lean:41) and add `0 < N`.
- **Log positivity.** With N ≥ 1, S ≥ 1, H ≥ 1, ∏A ≥ 1 and δ < 1, we get Λ > 0.

## 4. Claim (3): the causal-oracle restriction

**Definition (plan §2).** If two games agree in their rewards and kernels at every step t ≥ h, the outputs agree at step h. The
output is required to be an h = 1 NE (product) or CCE of every empirical game, and 0 < N is added.

**Verdict: ACCEPTABLE AND HONEST. Do not call it "weakest" in public docs.**

- **Honest.**
  - It constrains only the oracle, not the data or the conclusion.
  - It does not require perfectness. The plan's wording "output is an equilibrium of every empirical subgame" in the task
    brief is stronger than plan §2. The plan correctly requires only the h = 1 property, and the proof uses only that.
- **Necessary for this proof technique.**
  - The proof needs V̂^{π̂}_{h+1} and V̂^{ρ*}_{h+1} to depend only on the data at steps > h, for every h.
  - That requirement is equivalent to causality of π̂ at steps ≥ h+1. Nothing weaker is visible.
  - "Weakest honest restriction" is **not established**, since there is no lower-bound argument for non-causal oracles.
    Call it "a natural restriction matching the book's backward-induction planners". The phrase "the weakest" is not acceptable.
- **Satisfied by standard algorithms.**
  - These are causal by construction: Nash value iteration with a deterministic stage-game solver, a per-stage LP for a
    stage CCE, and stagewise no-regret run to an exact stage CCE or selected by a fixed rule.
  - My script checks one example numerically: a 2-player backward-induction NE oracle with a fixed 2×2 stage selector.
    Perturbing P̂₁ never changed steps ≥ 2 (0 of 150 cases), and the result was always a perfect empirical NE (gap ≤ 4e−16).
- **Not satisfied.**
  - Algorithms that average whole-game policies with weights depending on the step-1 data. An example is decentralized no-regret over the full game with
    visitation weights.
  - Randomized oracles. They are excluded as stated, which is minor. They could be added later with independent internal randomness.
- **Matches intent.** Plausibly yes, given :377 and :2549, but this is not certain. Say so.
- **Required correction for the oracle quantifiers.**
  - The plan's Lean sketch puts **both** oracles in one implication. The CCE conclusion is then only available when a
    causal NE oracle is also supplied.
  - For general-sum games no Lean witness of such an NE oracle exists, because Nash's theorem is missing from Mathlib. So the
    Lean-checked non-vacuity of the CCE clause would be lost.
  - **Fix.** Make the index entry a conjunction of three parts:
    - (a) a CCE-only clause, ∀ causal CCE oracle;
    - (b) an NE-only clause;
    - (c) the joint printed form.
  - Alternatively, prove (a) and (b) as separate library exports and derive (c).
  - Each clause keeps the printed threshold. The joint clause uses the joint union bound (§5).

## 5. Claim (4): the proof

**Verdict: CORRECT.** I re-derived every step independently.

- **(D) Decomposition using only the h = 1 CCE property.**
  - For correlated π̂, the best response is taken against the −i marginal: `deviate` replaces a_i inside each joint profile.
  - In the empirical game the greedy true best response ρ*_i satisfies `V̂^{ρ*}_{i,1} ≤ V̂^{⋆,π̂_{−i}}_{i,1} ≤ V̂^{π̂}_{i,1}`.
  - In the true game, `V^{ρ*}_{i,1} = V^{⋆,π̂_{−i}}_{i,1}` (Lemma BR).
  - The script checks (D), with a maximum violation of 9e−16, and greedy attainment, by assertion.
- **Causality and decoupling.** π̂_t depends on P̂_{≥t}, and br*_t depends on π̂_{≥t} and the true model. So V̂^{ρ}_{i,h+1} for
  ρ ∈ {π̂, ρ*_i} is a function of P̂_{≥h+1} only.
- **The Bernstein lemma applies.**
  - `futureValue_row_bernstein` is in `Formalization/Generative/FiniteHorizonAllLevelBernstein.lean:16`.
  - Its `hfuture` uses `completeFutureData`, which reads only stages strictly after h (`h < i.1.1`,
    FiniteHorizonEmpiricalContinuation.lean:80). That is exactly the needed premise.
  - It also requires `0 < N`, which is consistent with §3.
  - Its radius is `bernsteinRadius d N 1 (δ/k)`. By BernsteinFamily.lean:15 this equals `√(2 log(4k/δ) Var_d V / N) + 2‖V‖ log(4k/δ)/(3N)`,
    with the **true** variance. So ℓ = log(4k/δ) and ‖V̂‖ ≤ H, as the plan says.
  - No leave-one-out argument is needed. This is confirmed.
- **Self-bounding.**
  - The exact identity `D_h = Σρ[(P̂−P)V̂_{h+1} + P D_{h+1}]` holds. The script checks `|D_h| ≤ Eval(g)_h` with an absolute slack of 5e−16.
  - Variance transfer is available (`abs_sqrt_variance_sub_le_norm`; it is used in DRVI/DualDeviation.lean:212).
  - **Cauchy–Schwarz on Eval.** I re-derived it by induction using `(√x + √((K−1)y))² ≤ K(x+y)` and two applications of Jensen. The
    numerical maximum excess is 0.
  - **Total variance.** I re-derived `Eval(Var)_h + V_h² ≤ Y_h ≤ K_h²` from `(E_ρ q)² ≤ E_ρ q²` and `1 + 2(K−1) + (K−1)² = K²`. The
    numerical maximum of Eval(Var) − K² is −1.
  - **Combination.** `e ≤ √(2ℓ/N)(H^{3/2} + He) + 2H²ℓ/(3N)`. With x ≤ ½ this gives `e ≤ 2√(2ℓH³/N) + (4/3)H²ℓ/N`. Correct.
- **Arithmetic.**
  - `x² ≤ 6ε²/(C₁H) ≤ 6/C₁` uses ε² ≤ H. The second-order term uses ε ≤ √H ≤ H.
  - Hence `gap ≤ (4√(6/C₁) + 8/C₁)ε`.
  - My factors are 0.5099 at C₁ = 400, 0.8533 at 150 and 1.0598 at 100. So 400 works and the margin lies between 100 and 150.
  - **Wording.** "ε ≤ √H is exactly needed" overstates this. It is *used* (sufficient) and not shown necessary. Say "used".
- **Log absorption.**
  - Joint case: k = 4m'HS|𝒜|. With m' ≤ |𝒜|/2 we get 4k ≤ 8|𝒜|²HS, and `(SH|𝒜|/δ)³ ≥ 8|𝒜|²HS/δ` reduces to `H²|𝒜| ≥ 8`.
    So ℓ ≤ 3Λ for H ≥ 2 and |𝒜| ≥ 2.
  - **Tightness.** The supremum of ℓ/Λ is **exactly 3**. It is approached as δ → 1 at S = N = 1, H = 2 and |𝒜| = 2, where the ratio is
    `log(64/δ)/log(4/δ)`, and it is never attained for δ < 1. My grid gives 2.99999999856. The plan's 2.9986 is only a grid artefact.
  - The single-oracle supremum is 2.5.
  - The bound is tight but sound, and C₁ = 400 already absorbs the factor 3.
- **Trivial cases.**
  - H = 1, or A_i = 1: gap_i = 0.
  - m = 0 or S = 0: `gapJ` is `⨆` over an empty index in ℝ, which is 0 ≤ ε. This is benign, but the builder should confirm it.

## 6. Claim (5): existence and non-vacuity

- **Stage-CCE existence via separation: VALID.**
  - `geometric_hahn_banach_compact_closed` is at Mathlib `Analysis/LocallyConvex/Separation.lean:151` in the pinned
    toolchain v4.27.0-rc1 (local read-only Mathlib checkout).
  - It gives `f a < u < v < f b`. Since the cone contains 0, v < 0, and the cone condition forces the weights to have one sign.
  - The key identity is Σ_{i,b} w_{i,b} g_{i,b}(⊗q) = 0 with q_i ∝ w_i, or arbitrary when w_i = 0. The script checks it with a maximum
    error of 1.3e−16 over random games with 1–3 players and 1–3 actions each.
  - Backward induction with a stage-CCE selector gives a causal perfect CCE. The induction `Ŵ ≤ V̂` is re-derived and correct.
- **Nash's theorem / Brouwer / Kakutani: ABSENT.** A grep of pinned Mathlib finds no Brouwer, Kakutani or Nash fixed-point theorem. The only
  hits are Brouwer algebras and Riesz–Markov–Kakutani.
- **Disclosure: ACCEPTABLE**, on two conditions.
  - **(i) Wording.** Disclose it as "NE-oracle existence in general-sum games is classical (Nash) and not formalized; no hypothesis is added beyond the
    printed presupposition that the oracle returns an NE".
  - **(ii) Separate CCE clause.** The CCE clause must be separately stated (§4 fix), so that its hypothesis set has a Lean-checked witness without Nash.
    With the plan's bundled sketch this second condition **fails**. That is the main required correction.
- **Optional P8 (zero-sum, any perfect NE without causality): UNSUPPORTED, likely false. Do not build it without a separate check.**
  - Unique saddle values make V̂^{π̂} causal, but V̂^{ρ*_i} still depends on the opponent's later selection among
    empirically optimal stage strategies. That selection may be non-causal, which is the CE2′ mechanism.
  - Zhang et al. are recalled (not read) to need a "smooth planning oracle" for policy guarantees, which is consistent with this.
  - The zero-sum minimax non-vacuity of the NE clause, via separation, is fine as optional work.

## 7. Required corrections to the plan

1. **CE1.** The good set must include the unilateral-deviation rows (0,0), (1,0) and (0,1), and the bound is `gap ≥ 1 − 3N/K`.
   The plan's "1 − N/K" is wrong in the zero-sum version. It only holds with r₂ ≡ 0.
   Also fix the prose "Elsewhere … states self-loop": in the plan's script, P₁(s_j) → s₀.
2. **Line references.**
   - The decoupling prose is at generative_model_model_based.tex **:2549**. Line :2513 is commented-out text.
   - CCE is at :230–238, the gap at :327–342, and Thm 3.9 at :2551–2570, which is fine.
3. **Statement shape.** Split the oracle quantification as described in §4: a CCE-only clause, an NE-only clause, and the joint clause. A CCE non-vacuity
   corollary must instantiate the CCE-only clause.
4. **Wording.** Drop "weakest honest restriction" and "exactly needed". Mark CE2′ as numerical illustration only. Mark P8 as unsupported.
5. **Domain hypotheses.** Add `0 < S` and `∀ i, 0 < A i` as disclosed domain hypotheses rather than relying on vacuity. The sampling-law
   `Nonempty` fields need them anyway. Add `0 < N`.
6. **Arithmetic.** In the CE2 threshold arithmetic, the log argument is 128N², not 64N².
7. **Formal refutation.** `not_thm7_6_printed` must refute ∀ C₁ > 0, i.e. ∃ instance meeting the printed threshold. CE2 must use the same oracle for NE and CCE,
   B must be a function of the empirical game only, and the IsProductNE/IsCCE property must hold for **all** data, which is true.

## 8. C45 wording (proposed)

> **Candidate C45: Theorem 7.6 is false as printed for an unspecified planning oracle.** The NE and CCE notions
> (marl.tex:213–238) constrain only step h = 1, and the planning step (:377) puts no condition on which equilibrium of
> the empirical game is returned. Two counterexamples show the printed conclusion (:388–392) fails.
>
> - **(CE1)** In a two-player zero-sum game with H = 2, an h = 1 NE of the empirical game can play arbitrarily at states that no
>   empirical row reaches, giving a true gap of at least 1 − 3N/K.
> - **(CE2)** In a two-player general-sum game with H = 2 and S = 8N, a *subgame-perfect* product NE of the empirical game (hence also a CCE)
>   that selects its continuation equilibrium using step-1 samples has a true gap of at least ½ − N/(8N−2) ≥ 0.375 for every data set.
>
> CE2 meets the printed sample condition with ε = ¼ and δ = ½ for every C₁, so no universal constant works.
>
> **Restricted variant.** The proved variant assumes a *causal* oracle, meaning its step-h output depends only on the empirical model at steps ≥ h. This matches the
> backward-induction planners named at :377 and the decoupling stated for Theorem 3.9 at generative_model_model_based.tex:2549. It keeps the printed rate and
> threshold, and adds 0 < N.
>
> **Disclosures.** Existence of a causal NE oracle in general-sum games is classical (Nash) and not formalized. A causal CCE oracle is
> constructed in Lean.

## 9. Go / no-go

**GO** for P1–P7, conditional on corrections 1–7 in §7, above all #3, the split oracle clauses. Do not start P8.
- **Classification of C45.** False as printed, because of an omitted oracle hypothesis.
- **0 < N.** A disclosure-level domain convention.
- **The proof.** Sound at the printed rate with C₁ = 400.
