# CRITIC — Theorem 4.7 (case ii) and Lemma 4.15

Public copy of the independent critic report; local paths removed.

- Written: 2026-11-07 ~05:40 UTC
- Author: independent Claude critic subagent (did not build this code)
- Git HEAD: `6d98f9582477ca46a5af71c2d729326362c263a6` (branch `recovery-batch-ch5-online-lower-bound-20261106`, dirty tree; WIP files untracked)
- Mode: source-only reading. No Lean/lake/LSP was run by this critic, so compile status and `#print axioms` output are **not** independently verified here. The only numerics were a `python3 -I` Monte Carlo run in the scratchpad.
- Reconstruction and comparison (sections 1–5) were written before reading `the private independent check note (Thm4_7-issues)`. `the private preflight note (Thm4_7)`, `BUILD-LOG.md`, PROGRESS and other CRITIC files were not read.

## SHA256

| File | sha256 |
|---|---|
| `source/upstream/tex/chapters/generative_model_model_free.tex` | `7f4eb058e00480bc0694cac93ac41e22f4cfe48aa58a00c4ccf909f805e60b22` (matches `source/provenance.json:35`) |
| `source/provenance.json` | `3b7151be66aef083e3de0e1eb58133e39eeecccd80c2762f08a618ce2eec1c51` |
| `Thm47Wip/LbDefinitions.lean` | `71f2d0d165b76463a8e4f1d1efaba679b6b39fd845cc8edf45e1f7003097d5df` |
| `Thm47Wip/LbValues.lean` | `96d073596170343b22650e59a66bbd6f7e1d64ef0c59b8f53d0b5029763bc7da` |
| `Thm47Wip/LbProbability.lean` | `2c4005af1f6dae611e5c70077daaa3f9fa0df413034a91514515d31af8186f26` |
| `Thm47Wip/LbXiBasic.lean` | `c2e0a6b310c5151a4d3b8778f5aaca38557322e7f7b9ec97202a6d9bda7de475` |
| `Thm47Wip/LbZeta.lean` | `8ecec13be757da63b11d2aff6a2ce0f0e4cfb040974d60a10eec23a377375b6c` |
| `Thm47Wip/LbLemma415.lean` | `9008c362b8dfa435d19f466bcb56cba50beddad2aa0e159b9ec536b96d9b993c` |
| `Thm47Wip/LbPathwise.lean` | `de78ffb174e9c29d4c9318b70af3df46eefc0076053f11f7cdb552dfc7c144bb` |
| `Thm47Wip/LbState2.lean` | `abe27c5f77823b3c05df71e92ecc4ac06beea605bf0ac6fd91592a341aa4d298` |
| `Thm47Wip/LbStep5.lean` | `798de9d14bbab131adddcc7b44b9849f972239829fff1042b2229747a7b718bd` |
| `Thm47Wip/LbTheorem.lean` | `0a5f5f35c0d0d648842acfc0f8636ed28bfcfcf864598fb7443458a7a185762f` |
| `Thm47Wip/StatementProbe.lean` | `ca0e4342281f64c0ac693a23c671cc98a29b4aa7306d0886c4f3b884b4b97cf0` |
| `Formalization/ModelFree/QLearningSamplingDefinitions.lean` | `048bed00d9a023d73646c95285bfe4e43ba7d8e9dae4f757db86049ca9debe29` |
| `Formalization/ModelFree/QLearningIterateBounds.lean` | `594b96eede407a268bad69041146728a7456478c39c53990c53bef006a5b207e` |
| `Formalization/ModelFree/QLearningHardMDPDefinitions.lean` | `1a7d60642051ac230198f2d3a7ba6d893fd14010141edc5be55fa3ed173c5ab4` |

(`Thm47Wip/` = `<builder working folder>/Thm47Wip/`.)

## 1. Source reconstruction (independent)

**Algorithm (`alg:q-infinite`, :786–870).** Synchronous Q-learning. For t = 1..T, draw `s_t(s,a) ~ P(·|s,a)` independently for every (s,a). Then `Q_t = (1−η_t)Q_{t−1} + η_t T_t(Q_{t−1})`, where `T_t(Q)(s,a) = r(s,a) + γ max_{a'} Q(s_t(s,a), a')` and `V_t(s) = max_a Q_t(s,a)`. All entries update from `Q_{t−1}`.

**Theorem 4.7 (`thm:LB-example-Q-generative`, :969–982).** Assume `3/4 ≤ γ < 1` and `T ≥ c₃/(1−γ)²` for a sufficiently large constant `c₃`, `Q₀ ≡ 0`, and rates either (i) `η_t = 1/(1+c_η(1−γ)t)` or (ii) `η_t ≡ η ∈ (0,1)`. Then there exists a γ-discounted MDP with S = 4 and A = 2 such that `max_s E|V_T(s) − V⋆(s)|² ≥ c_lb / ((1−γ)⁴ T log² T)` for a universal `c_lb > 0`. On the natural reading, the MDP is chosen after γ, T and the rate schedule (it is written inside their scope). The proof's instance depends only on γ.

**Proof (Appendix C, :2707–3944), constant rates only (:2711).**
- **Step 1.** `M_hard` has S = {0,1,2,3}, `A_1 = {1,2}`, and every other `A_s = {1}`. States 0 and 3 are absorbing with rewards 0 and 1. From state 1 (both actions identical) and from state 2: stay with probability p, go to 0 with probability 1−p, reward 1. `p = (4γ−1)/(3γ)`. Lemma 4.14 gives `V⋆(1) = V⋆(2) = 3/(4(1−γ))` and `V⋆(3) = 1/(1−γ)`.
- **Step 2.** `V_t(0) = 0`. State 2 is a scalar chain with `E V_t(2) = (1−ρ^t)/(1−γp)`, where `ρ = 1−η(1−γp)`. State 3 is deterministic: `V_t(3) − V⋆(3) = −λ^t/(1−γ)`, where `λ = 1−η(1−γ)`.
- **Regimes.**
  - A, small: `η ≤ 4/((1−γ)T)`. Bias at state 2.
  - B, large: `η ≥ 1/((1−γ)²T)`. Variance at state 2.
  - C, moderate (strictly between). Over-estimation at state 1, using state 3 to absorb the initialisation term.
- **Step 5 (regime C).**
  - Auxiliary sequence `Q̂_t(a)`, initialised at `Q⋆(1,a)`, with `V̂ = max_a Q̂`.
  - Coupling: `Q_t(1,a) ≥ Q̂_t(a) − λ^t/(1−γ)`.
  - Recursion `Δ_{t,max} = Σ η(1−η)^{t−k} γp Δ_{k−1,max} + ξ_{t,max}`.
  - Lemma 4.15 gives `E ξ_{t,max} ≥ c/(√((1−γ)²T) log T)` for all `t ≥ τ̂`, where `τ̂ = max{τ : ρ^{T−τ+1} ≤ 6/7}`. The book proves it with Freedman, a truncation argument, `P{V̂_t ≥ 1/(4(1−γ))} ≥ 1/2`, and a window sum.
  - The scalar comparison sequence `x_t` and `max{a,b} ≥ (a+b)/2` over states 1 and 3 finish the bound.
- **Lemma 4.15 (:3429–3449).** In the Step-5 context (γ ∈ [3/4,1), T ≥ c₃/(1−γ)², moderate η, `M_hard`, `ξ` built from `Q̂`), there is a universal `c > 0` with `E ξ_{t,max} ≥ c/(√((1−γ)²T) log T)` for all `t ≥ τ̂`. The proof does not use `t ≤ T`.

Independent re-checks of the source (agreeing with C31):
- With `x_{τ̂} = 0`, the scalar sequence gives `x_T = c′(1−ρ^{T−τ̂})/(1−γp)`, not `ρ^{T−τ̂+1}`. Maximality of τ̂ gives `ρ^{T−τ̂} > 6/7`, so the printed `≥ 3c/28…` step fails. This is a genuine off-by-one in Step 5.4.
- In Step 4, `81/16 · (V⋆−E V_T)²/(V⋆−E V_{τ−1})² ≤ 81(1−γ)²(V⋆−E V_T)²`, not `/4`. The `≤ 1/2` conclusion survives.
- In `eq:square-zeta`(i) the coefficient is `(4γ−1)/(144(1−γ)) < 1/(48(1−γ))`.

These change only the unnamed constants.

## 2. Thm4_7_restricted versus the printed statement (case ii)

| Printed | Proposed Lean (`StatementProbe.lean:11–18`, export `qLb_thm47_constantRate`) | Verdict |
|---|---|---|
| ∃ "sufficiently large" `c₃`, universal `c_lb` | `∃ c₃ c_lb, 0<c₃ ∧ 0<c_lb ∧ ∀ γ …` (export: `c₃ = 16`, `c_lb = e^{−16}`) | faithful; constants precede γ, T, η |
| `3/4 ≤ γ < 1` | `3/4 ≤ γ → γ < 1` | exact |
| `T ≥ c₃/(1−γ)²` | `T : ℕ`, `c₃/(1−γ)² ≤ T` | exact |
| (ii) `η_t ≡ η ∈ (0,1)` | `∀ η, 0<η → η<1`, rates `fun _ ↦ η` | exact; case (i) omitted, so `_restricted` (C30) is correct |
| `Q₀ ≡ 0` | `(fun _ _ ↦ 0)` | exact |
| Algorithm `alg:q-infinite` | `qSampledIterate` = `qLearningIterate` over `qSamplesExtend`. Synchronous; iteration t+1 uses `Q_t` and draw `samples (t+1) s a` = zero-based coordinate t. The value is `actionMaximum (Q s)`. | exact |
| fresh independent draws `s_t(s,a) ~ P(·|s,a)` | `qSamplingLaw M T` = product of `rowMeasure`s over `(S×A)×Fin T` (`samplingLaw_marginal`, `samplingLaw_independent`) | exact |
| ∃ γ-discounted MDP, S = 4, A = 2 | `∃ M : DiscountedMDP (Fin 4) Bool, M.discount = γ`. Rewards in [0,1] come from the structure. | faithful (see 2.1) |
| `max_s E|V_T(s)−V⋆(s)|² ≥ …` | `∃ s : Fin 4, … ≤ ∫ (V_T(s) − V⋆(s))² ∂law` | equivalent: `max` over a finite nonempty set is ≥ x iff some s has value ≥ x; `|u|² = u²` |
| `V⋆(s)` | `M.trajectoryExpectedValue M.optimalGreedyPolicy s` | project-wide V⋆ convention (also used in Lemma 4.14 and Thm 4.3/4.4 entries); see NOTE N1 |
| `c_lb/((1−γ)⁴ T log² T)` | `c_lb / ((1−γ)^4 * T * Real.log T ^ 2)` (parses as `(log T)^2`) | exact |
| quantifier order of M | `∀γ ∀T ∀η ∃M ∃s` | matches the printed scope; the export's witness `qLbMDP γ` depends only on γ (stronger) |

### 2.1 Witness MDP `qLbMDP` (`LbDefinitions.lean:24–51`)
- Action `false` is source action 1 at every state, and action `true` at state 1 is source action 2. Both state-1 rows are `p / 1−p` with reward 1, as in the source.
- At states 0, 2 and 3, `true` is a dummy action: reward 0, deterministic move to 0.
- I checked by hand that from `Q₀ = 0` the dummy entries stay 0. `Q_t(0,·)` is 0 for both actions, so `Q_t(s,true) = (1−η)Q_{t−1}(s,true) + ηγ·0`. Because `Q_t(s,false) ≥ 0`, `V_t(s) = Q_t(s,false)` at s = 0, 2, 3. Every source recursion is reproduced. This is formalised in `qLb_pathwise` and `qLb_output_ae`, almost surely, after the support transfer.
- `V⋆` is unchanged: dummy `Q⋆ = 0 ≤` the others (`qLbMDP_optimal_values`).
- The instance is a genuine 4-state, 2-action MDP with rewards in {0,1}, so it lies in the theorem's class. Because the printed theorem is existential in M, any such witness suffices. This one is the book's instance up to the padding.
- C31(5) is correct: duplicating the single action at state 2 (as `qHardMDP` does) would change the Q-learning dynamics, because Q-learning would take a max of two independent copies. The WIP rightly avoids `qHardMDP` for Theorem 4.7.

### 2.2 Junk values
- `c₃ = 16` and `(1−γ)² ≤ 1/16` give `T ≥ 256` and `log T ≥ 1` (`qLb_T_facts`), so the denominator is strictly positive. There is no `x/0 = 0` vacuity.
- The integral is a Bochner integral. If the integrand were not integrable, it would equal 0, which makes a positive lower bound harder, not easier. Integrability holds anyway (finite discrete space).
- Natural-number subtraction does not appear in this statement.

## 3. Lemma4_15 versus the printed statement

| Printed | Proposed Lean (`StatementProbe.lean:21–33`, export `qLb_lemma415`) | Verdict |
|---|---|---|
| Step-5 context: γ ∈ [3/4,1), T ≥ c₃/(1−γ)², `4/((1−γ)T) < η < 1/((1−γ)²T)` | `∃ c c₃ …, ∀ γ hγ hγ1 T η, c₃/(1−γ)² ≤ T → 4/((1−γ)T) < η → η < 1/((1−γ)²T) →` | faithful; `η < 1` follows from `c₃ = 16` |
| `p = (4γ−1)/(3γ)`, `ρ = 1−η(1−γp)` | `let p …, let ρ …` (export uses `qHardP γ`, which is definitionally the same) | exact |
| `τ̂ = max{τ : ρ^{T−τ+1} ≤ 6/7}` | conjunct 1 asserts that the maximum exists (over ℕ); conjunct 2 quantifies over any `τhat` satisfying the membership and maximality predicates | faithful. `T+1−τ` in ℕ agrees with the integer exponent for τ ≤ T+1, and τ > T+1 gives `ρ⁰ = 1 > 6/7` (excluded). Integer τ < 0 never attains the maximum because τ = 0 qualifies. Existence is proved, not assumed. |
| `ξ_t(a)`, `ξ_{t,max}` from `Q̂` (`Q̂₀ = Q⋆(1,a)`, `V̂ = max Q̂`) on `M_hard`'s state-1 draws | `qLbXiMax γ η (qSamplesExtend (qLbMDP γ …) N d) t` under `qSamplingLaw (qLbMDP …) N` | exact. `qLbAuxIterate` and `qLbXi` match `eqn:Qhat-schumann` and `eqn:defn-xi-t` term by term (indexing checked: `P_k` = coordinate k−1). Only state-1 rows are used, and they equal the source rows. |
| "for all t ≥ τ̂" (proof does not need t ≤ T) | `∀ t N, τhat ≤ t → t ≤ N →` with the experiment run to horizon N | faithful and complete: every t ≥ τ̂ is covered by choosing N = t. The law of ξ_t does not depend on N ≥ t. |
| universal `c` | `∃ c` before ∀γ (export `c = 1/320`) | exact |
| bound `c/(√((1−γ)²T) log T)` | `c / (Real.sqrt ((1 - γ) ^ 2 * T) * Real.log T)` | exact; T ≥ 256 so there is no junk |

The entry may be **unsuffixed**. The export implies the printed lemma with nothing extra assumed. The C31(3) proof slips change only `c`.

## 4. Proof routes that differ from the book

1. **Lemma 4.15 without Freedman** (`LbLemma415.lean`, `LbZeta.lean`, `LbXiBasic.lean`). This route is sound.
   - `E ξ_max = E|ζ_t|/2`. This uses `E ξ_t(a) = 0` and the identity `max = (x+y+|x−y|)/2`.
   - Exact martingale moment recursions for `D_k = P_k(1|1,1) − P_k(1|1,2)`, which takes values in {−1,0,1} and is independent of the past:
     - second moment: `E S_{n+1}² = E S_n² + w²γ² q₂ E V̂_n²`;
     - fourth moment: `E S_{n+1}⁴ = E S_n⁴ + 6w²γ²q₂ E[S_n² V̂_n²] + w⁴γ⁴q₂ E V̂_n⁴`, with `q₂ = 2p(1−p)`. The odd terms vanish because `D³ = D` and `E D = 0`, and `D⁴ = D²`.
   - The book's tail estimate `P{V̂ ≥ 1/(4(1−γ))} ≥ 1/2` is replaced by a cleaner deterministic fact: `E V̂_n ≥ E Q̂_n(1) ≥ V⋆(1)`. The induction step is `E Q̂_{t+1}(1) = (1−η)E Q̂_t(1) + η(1+γp E V̂_t)`. Jensen then gives `E V̂² ≥ V⋆(1)²`, so `m₂ ≥ (4γ−1)/(8(1−γ)) · A ≥ ηh/12`, using `A = Σw² ≥ η/3` when `(1−η)^{2t} ≤ 1/3`.
   - Upper bounds `m₂ ≤ νA`, `m₄ ≤ 3ν²A² + νη²h²A ≤ (4/3)x² + (2/3)x³`, with `x = η/(1−γ)`.
   - The pointwise inequality `u² ≤ B|u| + u⁴/B²` with `B = 8√x` (x ≤ 1) or `B = 8x` (x > 1) gives `E|ζ| ≥ (5/768)·min(√x, 1)`. I re-derived each scalar inequality.
   - The result is log-free and stronger than the book's `c/(√((1−γ)²T) log T)`. The exported form follows because `1/(R log T) ≤ min(2/R, 1) ≤ min(√x, 1)`, with `R = √((1−γ)²T) ≥ 4` and `√x ≥ 2/R` from `η(1−γ)T > 4`.
   - Monte Carlo sanity check (4000 reps) on γ ∈ {0.75, 0.9, 0.99}: empirical `E ξ_max` was 0.12–0.25, against bounds of about 0.003.
2. **Step 5.4 repair** (`qLb_step5`, `LbTheorem` case C). This is sound and correctly fixes C31(4).
   - Write `e_t = E C_t`, where `C` is the common part with `V̂_t − V⋆ = C_t + ξ_{t,max}` pathwise. Then `e_{t+1} = (1−η)e_t + ηγp(e_t + E ξ_t)`.
   - `E ξ ≥ 0` always, so `e_t ≥ 0`. For t ≥ τ₀, `e_{t+1} ≥ ρe_t + ηγp b`.
   - Hence `(1−γp)(E V̂_N − V⋆) ≥ (1−γp)b + γp b(1−ρ^{N−τ₀}) ≥ b(1−ρ^{N−τ₀})`.
   - With `τ₀ = ⌊(T+1)/2⌋` we get `2t ≥ T`, so `(1−η)^{2t} ≤ (1−η)^T ≤ ρ^T ≤ 1/100`. From `ρ ≥ 2/3` and `ρ^T ≤ 1/100`, `ρ^{T−τ₀} ≤ 1/2` (`qLb_rho_tail`).
   - This avoids τ̂ and the off-by-one in the theorem's proof. It does not affect the Lemma 4.15 entry, which keeps the printed τ̂.
3. **Regime split A/B/C** (`η(1−γ)T ≤ 4`; else `η(1−γ)²T ≥ 1`; else C). It matches the book's three regimes exactly and covers all η ∈ (0,1). States: 2 for A and B, 1 or 3 for C via `max ≥ mean`.
   - Constants re-checked: A gives `(9/16)e^{−≈10.7}/(1−γ)² ≥ e^{−16}/((1−γ)⁴T log²T)`, since `(1−γ)²T log²T ≥ 16`. B gives `≥ 1/(96(1−γ)⁴T)`. C gives `≥ 9b²/(256(1−γ)²)`, with `b ≥ 10/(1536R)`, i.e. about `1.5·10⁻⁶/((1−γ)⁴T) ≥ e^{−16}/(…)`.
4. **A.e. support transfer** (`qLb_support_ae`, `qLb_valid_ae`). It is sound.
   - The indicator `1{prob(d i) = 0}` has integral `Σ_x prob(x)·1{prob x = 0} = 0`, so almost surely every draw has positive row probability.
   - The pathwise identities (for example, a draw from state 0 lands in 0) are only needed on that set. They feed `integral_congr_ae` and `integral_mono_ae`.
   - No hidden hypothesis: validity is derived, not assumed in any export.

## 5. Honesty

- `StatementProbe.lean`: the wrappers are `theorem Thm4_7_restricted_holds : Thm4_7_restricted := qLb_thm47_constantRate` and `Lemma4_15_holds := qLb_lemma415`. Both are pure term applications, and the export signatures match the Props textually (Lemma uses `let p` versus `qHardP γ`, which is definitional). Nothing is reproved.
- Grep of `Thm47Wip/*.lean` and all of `Formalization/` for `sorry|admit|axiom|opaque|implemented_by|unsafe|native_decide|@[extern|ofReduceBool` found nothing. There are two prose hits on the word "admit" in comments (`QLearningRobustDefinitions.lean:19`, `Obstructions/SingletonAction.lean:58`), and neither is a tactic.
- WIP imports are `Formalization.ModelFree.{QLearningHardMDPDefinitions, QLearningHardMDPValues, QLearningIndicatorCondExp, QLearningIterateBounds, QLearningPrefixFiltration}`, `Formalization.Probability.EmpiricalRow`, and Mathlib.
- I have **not** verified that the closure compiles or that `#print axioms` shows only `propext, Classical.choice, Quot.sound`. The lead must run `scripts/check.py` after the move.

## 6. Findings

**BLOCKING:** none.

**MAJOR:** none.

**MINOR**
- **M1. Module docstring line citations drift.** These are module and definition docstrings, not the statement-index ranges:
  - `LbDefinitions.lean:7,59` cite `eqn:Qhat-schumann` at 3348–3362; the actual range is 3316–3324.
  - `LbDefinitions.lean:8` cites `eqn:defn-xi-t` at 3410–3416; the actual range is 3405–3411.
  - `LbPathwise.lean:9` cites `eq:Qt-lower-bound-generative` at 3365–3370; the actual range is 3330–3334. Its proof range, 3567–3592, is correct.
  - `LbState2.lean:6` cites `eq:EV2` at 2985–3000; the actual range is about 3010–3021.
  - `LbState2.lean:8` cites `eq:Var-VT-2-LB-769` at 3205–3215; the actual range is about 3184–3195.
  - `LbXiBasic.lean:8` cites 3348–3420; it should start around 3316.
  - The statement-index ranges are correct: `969–982` and `3429–3449`.
  - Fix these before landing.
- **M2. Lemma 4.14 uses a different instance.** The `Lemma4_14` entry (`Statements/Ch4.lean:205–223`) is stated for `qHardMDP`, which uses the copy encoding, while Theorem 4.7 and Lemma 4.15 use `qLbMDP`. Lemma 4.14 is about values only, so the copy encoding is harmless there. Still, the book's Lemma 4.14 is about the same `M_hard` that Theorem 4.7 uses. Either add a sentence to the Lemma 4.14 docstring and COVERAGE pointing to `qLbMDP_optimal_values` as the matching instance used in Theorem 4.7, or note in the Theorem 4.7 docstring that the instance differs from the Lemma 4.14 encoding. In addition, `QLearningHardMDPDefinitions.lean`'s module docstring describes the copy encoding without the C31(5) warning that it is not suitable for Q-learning dynamics; add a cross-reference.

**NOTE**
- **N1.** `V⋆` is `trajectoryExpectedValue` of `optimalGreedyPolicy` (the greedy policy of the optimality fixed point, shown optimal among stationary randomized policies in `OptimalTrajectoryValue.lean`). This is the established project convention and is consistent with the other Ch4 entries. For this instance the value equals the printed closed forms (`qLbMDP_value`).
- **N2.** The export is strictly stronger than the print in three ways: the MDP depends only on γ (not on T or η), the regime-C bound and the internal Lemma 4.15 bound are log-free, and Lemma 4.15 holds for every t ≥ τ̂ with no t ≤ T restriction. Per AGENTS.md this is not a discrepancy and needs no SOURCE-ISSUES entry.
- **N3.** C30 (case (i) not proved in source) and C31 (1)–(5) were each re-derived independently, and each is correct as stated. I confirmed the C31(4) off-by-one: maximality of τ̂ forces `1−ρ^{T−τ̂} < 1/7`.
- **N4.** `c₃ = 16` in the export, against the book's implicit requirement `T ≥ 50/(1−γ)²` (for `eqn:schubert-winterreise`). The Freedman-free route does not need that requirement.

## 7. Docstring and disclosure requirements

- **`Thm4_7_restricted`** must:
  - cite `thm:LB-example-Q-generative`, `chapters/generative_model_model_free.tex:969–982`, and the proof range `:2707–3944`;
  - state that only case (ii) (constant `η ∈ (0,1)`) is covered, that case (i) is an open obligation, and point to `docs/SOURCE-ISSUES.md#C30`;
  - say that `max_s` is rendered as `∃ s`;
  - say that `V⋆` is the optimal greedy policy's trajectory value;
  - say that the witness is `M_hard` with dominated dummy actions (C31(5));
  - mention the C31 constant repairs (the proof does not follow the printed Step 5.4 or the printed Freedman route).
- **`Lemma4_15`** (unsuffixed) must:
  - cite `lem:lower-bound-E-xi-lower-Q`, `:3429–3449`, and the proof range `:3707–3944`;
  - state that the Step-5 context is written out (γ, T ≥ c₃/(1−γ)², moderate η, and `ξ` built from the auxiliary `Q̂` on the state-1 draws of the hard instance);
  - say that the existence of τ̂ is part of the Prop;
  - say that "∀ t ≥ τ̂" is encoded by running the experiment to any horizon N ≥ t;
  - point to C31(3) for the constant slips in the printed proof.
- **COVERAGE.md** should say "Theorem 4.7 case (ii) only; case (i) open (C30)". It must not mark Theorem 4.7 fully proved.

## VERDICT

- **`Thm4_7_restricted`**: ACCEPT (as a restricted entry), conditional on (a) the lead's compile and axiom audit after moving the files into `Formalization/ModelFree/` and (b) fixing M1 and M2 and adding the docstring disclosures in section 7. The `_restricted` suffix and the C30 link are required and correct.
- **`Lemma4_15`** (unsuffixed): ACCEPT, with the same conditions (a) and (b).
- **Wrappers** (`*_holds`): ACCEPT; they only apply the exports.

## Addendum (written after reading `the private independent check note (Thm4_7-issues)`)

My reconstruction agrees with every item of that check: P1–P8, the padding observation O1/P10, and P11 ("for all t ≥ τ̂" is true with no t ≤ T bound). Three further points:

- The proposed `Lemma4_15` encodes P11 the recommended way. It quantifies over any horizon `N ≥ t`, so there is no t ≤ T restriction and no suffix is needed.
- The check notes that the moderate regime is empty at γ = 3/4, because `4/((1−γ)T) = 1/((1−γ)²T)` there. `Lemma4_15` is then vacuous at γ = 3/4, exactly as the printed lemma is. This is not an issue.
- The check's c₃ ≥ 50 requirement comes from the book's Freedman route. The Lean route needs only c₃ = 16 (NOTE N4). This is not a discrepancy.

None of this changes the verdicts.
