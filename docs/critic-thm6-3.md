# CRITIC — Theorem 6.3 (`thm:infinite-offline`, VI-LCB) proposed entry `Thm6_3` and export `vilcb_infinite_offline`

Public copy of the independent critic report; local paths removed.

- Date (UTC): 2026-11-07 06:47 (start)
- Reviewer: independent Claude critic subagent (did not build this code)
- Git HEAD: `2c0775700810839103ae286eed80b7d91345a3c4` (branch `recovery-batch-ch4-qlearning-lb-20261107`)
- Mode: source-only review. No Lean, lake, compiler or lean-lsp was run. Compile and axiom evidence below is
  the builder's existing `probe.out` and olean timestamps, not reproduced by me.
- Read order: source and SOURCE-ISSUES first, reconstruction written, Lean read second. `the private preflight note (Thm6_3)`,
  `<builder working folder>/BUILD-LOG.md`, `docs/PROGRESS.md` and other CRITIC files were not opened before sections 1–4 were complete.

## 0. SHA256

| File | SHA256 |
|---|---|
| `source/upstream/tex/chapters/offlineRL.tex` | `67cf0d1ce6a3d7c6cc43aedb371c692a3da0508193d735609713b03c0186f1e4` (matches `source/provenance.json:39`) |
| `<builder working folder>/StatementProbe.lean` | `b83813af906eb12da2ac36b7fcb620b927fa871b3f8ae64241a6484dc28467ef` |
| `<builder working folder>/Thm63Wip/PenaltyDominance.lean` | `547747fddac4926b2f1114a643540a1118641f5949f0926be3bcb72e49b52092` |
| `<builder working folder>/Thm63Wip/Pessimism.lean` | `f45b53e2cd166162d0f9d4c9455ad03f82ff05cc933a82fa4ee58158417678e2` |
| `<builder working folder>/Thm63Wip/BonusSumScalar.lean` | `5cdb81fbe44219fd62b3500e9b6ee516073d29a65094f834a9ed8eb3c20a71e9` |
| `<builder working folder>/Thm63Wip/Deterministic.lean` | `d5e01c221d1b4338299927374cf81d269adcf4b9f06419bbdf99a09fe02f4eb7` |
| `<builder working folder>/Thm63Wip/Theorem.lean` | `523fdb46727e29cbb4531eacdb23599b12f9824acb1e38a2c801c181c3bad241` |

## 1. Source reconstruction (from `offlineRL.tex` alone)

**Setting.** `eq:sampling-offline-inf-iid` (`:28–39`): dataset of `N` triples, `(s_i,a_i) ~ d^b` independently and
`s_i' ~ P(·|s_i,a_i)` independently. Rewards known, in `[0,1]` (book convention). `N_{s,a}` (`:676–678`), `P̂`
with uniform row `1/S` for unseen pairs (`:685–695`).

**Penalty** `def:bonus-Bernstein-infinite` (`:811–822`):
`b(s,a;V) = min{ max{ √(c_b log(N/((1−γ)δ)) Var_{P̂_{s,a}}(V)/N_{s,a}), 2c_b log(N/((1−γ)δ))/((1−γ)N_{s,a}) }, 1/(1−γ) } + 5/N`,
with `b = 1/(1−γ) + 5/N` if `N_{s,a} = 0`. Note the penalty log has no `S` and no `4`.

**Algorithm** `alg:vi-lcb-infinite` (`:827–852`): `Q̂_0 = 0`; `Q̂_τ = max{r + γP̂V̂_{τ−1} − b(·;V̂_{τ−1}), 0}`,
`V̂_τ = max_a Q̂_τ`; output any `π̂(s) ∈ argmax_a Q̂_{τmax}(s,a)`.

**C⋆** `assumption:concentrate-infinite-simple` (`:127–139`): `C⋆ = max_{s,a} d⋆(s,a;ρ)/d^b(s,a)`, `0/0 = 0`,
`d⋆` the discounted state-action occupancy of "the optimal deterministic policy `π⋆`" from `ρ`. `C⋆ ≥ 1`
(`:143–149`); `C⋆ = ∞` possible when `d^b` misses a `π⋆`-reachable pair.

**Theorem 6.3** (`:899–920`). `γ ∈ [1/2,1)`, `0<δ<1`, `ε ∈ (0, 1/(1−γ)]`, any `ρ ∈ Δ(S)`,
`τmax ≥ (1/(1−γ)) log(N/(1−γ))`. With probability `≥ 1−2δ`, `V⋆(ρ) − V^{π̂}(ρ) ≤ ε`, "provided that `c_b > 0`
is some sufficiently large numerical constant and `N ≥ c₁ S C⋆ log(NS/((1−γ)δ))/((1−γ)³ε²)` for some large enough
universal constant `c₁`".

**Proof skeleton** (`:1031–1623`, appendix `:3489` Lemma 6.4, `:3541` Lemma 6.5, `:3630` Lemma 6.6, `:4277` Lemma 6.7):
1. Lemma 6.2 (`lem:monotone-contraction`) + stopping rule: `‖Q̂ − Q̂⋆_pe‖ ≤ 1/N`. The theorem's `τmax` rule implies
   the lemma's `log(N/(1−γ))/log(1/γ)` rule since `log(1/γ) ≥ 1−γ`.
2. Lemma 6.4 (`lem:offline-prelim`): `‖V̂ − V̂⋆_pe‖ ≤ 1/N`, `|b(V̂⋆_pe) − b(V̂)| ≤ 2/N`.
3. Events: Lemma 6.5 count event (prob `> 1−δ`, log `SN/δ`) ∩ Lemma 6.6 Bernstein event (prob `≥ 1−δ`,
   log `4N/((1−γ)δ)`, for every `Ṽ` with `‖Ṽ − V̂⋆_pe‖ ≤ 1/N`, `‖Ṽ‖ ≤ 1/(1−γ)`) → `1−2δ`.
4. Step 1 (`eq:infitnie-bernstein-b-bound-diff`): `|(P̂−P)Ṽ| + 5/N ≤ b(Ṽ)` for `c_b` large; zero-count pairs trivially.
5. Step 2: `Q̂ ≤ r + γPV̂` (two cases), then the min-argument gives `Q^{π̂} ≥ Q̂`, so `V^{π̂} ≥ V̂`.
6. Step 3: `V̂(s) ≥ r(s,π⋆) − 2b⋆(s) + γP_{s,π⋆}V̂` (`eq:infinite-v-lower`) and Bellman for `V⋆` along `π⋆` give
   `ρᵀ(V⋆−V̂) ≤ 2⟨d⋆_ρ,b⋆⟩/(1−γ)`.
7. Step 4: split `S_small/S_large` at `N d^b(s,π⋆(s)) ≤ 8 log(NS/((1−γ)δ))`; small: `d⋆(s) ≤ C⋆ d^b`, `b⋆ ≤ 1/(1−γ)+5/N`;
   large: count event gives `N_{s,π⋆} ≥ N d^b/12`; Cauchy–Schwarz and Lemma 6.7 (`Σ d⋆ Var ≤ 2/(γ²(1−γ)) + 4⟨d⋆,b⋆⟩/(γ²(1−γ))`,
   premises `0 ≤ V̂ ≤ 1/(1−γ)`, `V̂ − γP⋆V̂ + 2b⋆ ≥ 0`); self-bounding gives `⟨d⋆,b⋆⟩ ≤ 70√(c_b S C⋆ log/((1−γ)N))`,
   so the gap is `≤ 140√(c_b S C⋆ log(NS/((1−γ)δ))/((1−γ)³N))`.

**Quantifier consequence.** The final step needs `N ≥ 140² c_b S C⋆ log/((1−γ)³ε²)`, and Step 4.2 needs
`N ≳ c_b S C⋆ log/(1−γ)`, so the source's `c₁` scales with `c_b`. The only correct reading is
`∃ c_b₀ ∀ c_b ≥ c_b₀ ∃ c₁` (or "fix a large `c_b`, then a large `c₁`"). A single `c₁` for all large `c_b` is false
(counterexample in finding N1).

Source-proof checks I made (no new source error found): Step 4.1/4.2 thresholds are consistent
(`N d^b > 8 log(NS/((1−γ)δ)) ≥ 8 log(SN/δ)` ⇒ the max in the count event is attained by `N_{s,a}`); the
`α₁` bound with `γ ≥ 1/2` (`2/γ² ≤ 8`, `4/γ² ≤ 16`) is correct; Lemma 6.7's appendix steps (i)–(v) are valid under
its displayed premises; the `5/N` absorption in `eq:infinite-bernstein-large-result-middle` uses `N_{s,a} ≤ N`.
Known source issues touching this proof: C10 (Lemma 6.2 needs `γ ≥ 1/2`; satisfied here), C19 (Lemma 6.5 needs
`N ≥ 2`; implied by the sample size), C23 (Lemma 6.6 covering bound assumes `N ≥ 5`; repaired in the library),
Lemma 6.6 zero-count scope, Lemma 6.7 restricted scope (premises to be discharged by the parent).

## 2. Lean statement as read

`Thm6_3` (`StatementProbe.lean:13–38`):
`∃ cb₀ > 0, ∀ cb ≥ cb₀, ∃ c₁ > 0, ∀ S A [Fintype, Nonempty] (M : DiscountedMDP) (db : FiniteDistribution (S×A)) (p : Params S A),
p.γ = M.discount → p.r = M.reward → p.cb = cb → 1/2 ≤ γ → ∀ τmax : ℕ, (1/(1−γ)) log(p.N/(1−γ)) ≤ τmax →
∀ ρ πstar, (πstar is Q⋆-greedy) → ∀ ε, 0 < ε → ε ≤ 1/(1−γ) → C⋆(M,ρ,πstar,db) ≠ ⊤ →
c₁ · S · C⋆.toReal · log(p.N·S/((1−γ)p.δ)) / ((1−γ)³ε²) ≤ p.N →
∀ Ω μ [IsProbabilityMeasure], ∀ X : Ω → Fin p.N → (S×A)×S, Measurable X → iIndepFun (X · i) μ →
(∀ i, law(X_i) = Σ_x ofReal(db(x.1)·P(x.2|x.1)) δ_x) →
1 − 2p.δ ≤ μ.real {ω | ∀ π̂, (π̂ greedy for (p.input (X ω)).iter τmax) → ρ·V^{greedy⋆} − ρ·V^{π̂} ≤ ε}`.

`Params` (`VILCBDatasetDefinitions.lean:73–87`) carries `0 ≤ γ < 1`, `0 < N`, `r ∈ [0,1]`, `0 < c_b`, `0 < δ < 1`.
`Input.bonus` (`VILCBDefinitions.lean:45–49`) is the printed penalty with the printed zero-count branch and the printed
log `log(N/((1−γ)δ))`. `iter τ = pess^[τ] 0`. `dataCount`/`dataPhat` match `:676–695` including the uniform row.
`concentrability` (`LCBQDefinitions.lean:105–108`) is `⨆_{(s,a)} ofReal d⋆(s,a)/ofReal d^b(s,a)` in `ℝ≥0∞`
(`0/0 = 0`, `x/0 = ⊤`), with `d⋆` the actual discounted joint occupancy of `detPolicy πstar` from `ρ`.

## 3. Comparison table

| Item | Source | Lean | Verdict |
|---|---|---|---|
| Quantifiers on constants | `c_b` sufficiently large, `c₁` large enough universal | `∃cb₀>0 ∀cb≥cb₀ ∃c₁>0` before all data; proof `cb₀ = 96`, `c₁ = 10⁴ c_b` | Faithful; only correct reading (N1) |
| `γ` | `γ ∈ [1/2,1)` | `M.discount < 1` (structure) and `1/2 ≤ M.discount`; `p.γ = M.discount` | Match |
| `r` | known reward, in `[0,1]` | `p.r = M.reward`, both bounded in `[0,1]` by structure | Match |
| `δ` | `0<δ<1`, same `δ` in penalty, events and `1−2δ` | `p.δ` in `Params`, used by penalty, by both events and in `1 − 2p.δ` | Match |
| `N` | dataset size, implicit `N ≥ 1` | `p.N : ℕ`, `0 < N` in `Params` | Match (N2 disclosure) |
| `τmax` | `τmax ≥ (1/(1−γ)) log(N/(1−γ))` | same, `τmax : ℕ` cast to `ℝ` | Match |
| `ρ` | any `ρ ∈ Δ(S)` | any `FiniteDistribution S` | Match |
| `π⋆` | "the optimal deterministic policy" | any `πstar` with `Q⋆(s,πstar s) = max_a Q⋆(s,a)`; `C⋆` computed from that `πstar` | Equivalent/stronger (every optimal deterministic policy is `Q⋆`-greedy and conversely) |
| `C⋆` | max ratio, `0/0 = 0`, may be `∞` | `ℝ≥0∞` sup with `C⋆ ≠ ⊤` hypothesis, then `.toReal` | Faithful; the guard only removes the case where the printed `N ≥ ∞` is unsatisfiable (and blocks the junk `⊤.toReal = 0`) |
| `ε` | `ε ∈ (0, 1/(1−γ)]` | `0 < ε`, `ε ≤ 1/(1−γ)` | Match |
| Sample size | `N ≥ c₁ S C⋆ log(NS/((1−γ)δ))/((1−γ)³ε²)` | `c₁·|S|·C⋆·log(N·|S|/((1−γ)δ))/((1−γ)³ε²) ≤ N` | Match, same log argument |
| Data law | iid triples, `(s,a) ~ d^b`, `s' ~ P(·|s,a)` | `iIndepFun` coordinates, each with law `Σ d^b(x.1)P(x.2|x.1) δ_x` on `⊤` σ-algebra | Match |
| Penalty | `:811–822` incl. zero-count | `Input.bonus` | Match |
| Algorithm / output | `Q̂_{τmax}`, `π̂ ∈ argmax` | event quantifies over every greedy `π̂` of `(p.input (X ω)).iter τmax` | Stronger (covers any tie rule) |
| `V⋆(ρ)`, `V^{π̂}(ρ)` | value functions | `ρ.expectation` of `trajectoryExpectedValue` (actual infinite-trajectory values); `V⋆` as the value of the library's `Q⋆`-greedy policy | Match under library convention (N4) |
| Probability | at least `1−2δ` | `1 − 2p.δ ≤ μ.real{…}`; event is measurable (finite discrete codomain) | Match |
| Junk values | — | `N ≥ 1` ⇒ all logs have argument `> 1`; `(1−γ)³ε² > 0`; `C⋆.toReal` guarded; `x/0` only in zero-count branch which is defined explicitly | No junk exploitation found |

## 4. Proof route check (WIP files)

- **Penalty dominance** (`PenaltyDominance.lean:bonus_dominates`). Uses `ℓ = log 4 + L ≤ 3L` from `L ≥ log 2` (`γ ≥ 1/2`,
  `δ < 1`, `N ≥ 1`), then `c_b ≥ 96` ⇒ `32ℓ ≤ c_b L`, giving `√(8ℓ v/n) ≤ ½√(c_b L v/n)` and `26ℓ/((1−γ)n) ≤ ½·2c_bL/((1−γ)n)`;
  clip by `|(P̂−P)V| ≤ 1/(1−γ)` for `0 ≤ V ≤ 1/(1−γ)`. Zero-count pairs: `b = 1/(1−γ) + 5/N` and the box bound,
  so no Lemma 6.6 bound is needed there. Correct and matches `:1174–1194`.
- **Step 4.2 upper bound** (`bonus_le_of_lemma66`): variance transfer with `24ℓ ≤ 72L`, `72/c_b ≤ 1`, `√(a+W²) ≤ √a + W`,
  `5/N ≤ W` via `N_{s,a} ≤ N`. Correct.
- **Lemma 6.6 event and `V̂`.** `goodSet` (`BernsteinInfiniteData.lean:115–121`) quantifies over every fixed point
  `Q⋆_pe` and every `Ṽ` within `1/N` of its value and bounded by `1/(1−γ)`. `run_facts` discharges both premises for
  `V̂ = value (iter τ)` from `lem_monotone_contraction_corrected` (`γ ≥ 1/2`) + `source_stopping_threshold` +
  `exists_fixed_point_preliminary_facts` (Lemma 6.4) and `iter_mem_box`. Event level is `p.δ`, matching the source.
- **Pessimism** (`iter_le_reward_add`): the source's two cases are merged soundly via `Q̂ ≤ Q̂⋆_pe = max(tilde, 0)`
  and `tilde ≤ r + γPV̂` (needs `1/N + 2/N ≤ 5/N` and `γ ≤ 1`), `0 ≤ r + γPV̂`. `value_le_trajectoryValue` replaces the
  source's arg-min over `(s,a)` by an arg-min over `s` of `V^{π̂} − V̂`; valid (`W(t) ≥ γ P W ≥ γ W(s₀)` ⇒ `W(s₀) ≥ 0`).
- **Lower bound** (`reward_add_sub_le_value`): `1/N + 2/N + 1/N ≤ 5/N` absorbs Lemma 6.4 and the iterate error; matches
  `eq:infinite-v-lower` with `2b⋆`.
- **Occupancy reduction** (`occupancy_reduction`): uses the proved flow equation `d = (1−γ)ρ + γ dP_π`
  (`discountedStateOccupancy_flow`) instead of the Neumann-series limit; gives `(1−γ)⟨ρ,Δ⟩ ≤ 2⟨d,b⟩` with no sign
  condition. Sound; equivalent to `eqn:brahms-reduction`.
- **Lemma 6.7 premises** (`lemma67_instance`): `0 ≤ V̂ ≤ 1/(1−γ)`, `b⋆ ≥ 0`, and `V̂ − γP⋆V̂ + 2b⋆ ≥ 0` derived from
  `eq:infinite-v-lower` plus `r ≥ 0`; `γ > 0` from `γ ≥ 1/2`. This is exactly the discharge that the `Lemma6_7_restricted`
  disclosure says the parent must do.
- **Per-state bound** (`state_term_le`): split at `N d^b ≤ 8L₂` (source `S_small`), small uses `d⋆(s) ≤ C⋆ d^b(s,π⋆)`
  (`dstarState_le`, via joint occupancy of a deterministic policy) and `b⋆ ≤ 1/(1−γ) + 5/N`; large uses the count event
  with `Ls = log(SN/δ) ≤ L₂`, which forces `n ≥ N d^b/12 > 0`. Correct.
- **Summation and self-bounding** (`step4_abstract`, `self_bound`): `x ≤ 50Y + √(Y(192+384x))` with
  `Y = c_b S C⋆ L₂/((1−γ)N)`; the sample size with `c₁ = 10⁴c_b` gives `Y ≤ ((1−γ)ε)²/10⁴`, and `(1−γ)ε ≤ 1` from
  `ε ≤ 1/(1−γ)`. I checked `self_bound` by hand: if `2x > t`, then for `x ≤ 1` the right side is `< 0.23x²`, for `x > 1`
  it is `< 0.0192 + 0.0384x`, both below `(0.99x)²`. Conclusion `2x ≤ (1−γ)ε` ⇒ gap `≤ ε`.
- **Events** (`Theorem.lean`): `N ≥ 2` derived from the sample-size condition (`two_le_N_of_sample_size`, needs
  `c_b L₂ ≥ 48`, `S C⋆ ≥ 1`, `(1−γ)³ε² ≤ 1`); Lemma 6.5 at `p.δ` (strict `> 1−δ`) and Lemma 6.6 at `p.δ`; union bound
  on complements; the target set contains `E5 ∩ E6`. Correct `1 − 2δ`.
- **Wrapper honesty.** `Thm6_3_holds` is a single term applying `vilcb_infinite_offline` with `cb₀ = 96`, `c₁ = 10000*cb`;
  the hypothesis `c₁ * |S| * …` with `c₁ := 10000*cb` is syntactically `10000 * cb * |S| * …`. No restatement or reproof.
- **Forbidden tokens.** `grep -nE 'sorry|admit|axiom|opaque|implemented_by|unsafe|native_decide|@[extern|ofReduceBool|set_option'`
  over the 6 WIP files: no hits. Over `Formalization/` (the library import closure): only two prose hits in docstrings
  (`QLearningRobustDefinitions.lean:19` "admit mass", `SingletonAction.lean:58` "does admit"), no code.
- **Compile/axiom evidence (builder's, not reproduced).** `probe.out`: both `Thm6_3_holds` and `vilcb_infinite_offline`
  depend only on `[propext, Classical.choice, Quot.sound]`. Every `.lake/build/lib/lean/Thm63Wip/*.olean` is newer than
  its source (01:32–01:45 local), `probe.out` (01:46) is newer than `StatementProbe.lean` (01:45).

## 5. Findings

### BLOCKING
None.

### MAJOR
None.

### MINOR
- **M1 (docstring disclosures missing).** The probe docstring of `Thm6_3` is one line (label + line ranges). It
  does not disclose the readings listed in section 6. Under AGENTS.md this is a reading aid, so it should state
  them before integration.
- **M2 (line ranges).** `Thm6_3` cites `:899–920` (correct: `\begin{theorem}` at 899, `\end{theorem}` at 920) and proof
  `:1031–1626`. The proof text ends at `:1623` (1624–1626 are blank lines before `\section{Model-free offline RL}`). The
  appendix proofs it relies on are not cited: Lemma 6.4 `:3489–`, Lemma 6.5 `:3541–`, Lemma 6.6 `:3630–`, Lemma 6.7
  `:4277–4342`. Cosmetic.
- **M3 (integration hygiene).** The probe lives in `namespace StatisticalRL.Statements.Ch6Probe` and imports
  `Thm63Wip.Theorem`. On integration: `Thm6_3` goes into `Formalization/Statements/Ch6.lean`, which already imports every
  definition module it uses (`VILCBDatasetDefinitions`, `LCBQDefinitions`, `DiscountedOccupancy`, `OptimalTrajectoryValue`).
  `Thm6_3_holds` goes into `Ch6Proofs.lean`; the five WIP modules move under `Formalization/OfflineRL/` with library names; the
  WIP oleans in `.lake/build/lib/lean/Thm63Wip/` are deleted; and `scripts/check.py` / the axiom audit is re-run. My compile
  and axiom evidence is the builder's `probe.out`, not reproduced (I ran no Lean, by brief).

### NOTE
- **N1 (quantifier order is necessary).** `∃cb₀ ∀cb≥cb₀ ∃c₁` is the correct reading. A single `c₁` for all large `c_b` is
  **false**. Counterexample: `S = {s}`, `A = {a₁,a₂}`, `r(a₁)=1`, `r(a₂)=0`, self-loop, `γ = 1/2`, `d^b = δ_{(s,a₁)}` (so `C⋆ = 1`),
  `ρ = δ_s`, `δ = 1/4`, `ε = 1 ≤ 1/(1−γ) = 2`. Fix any `c₁`. Take any `N ≥ 8c₁ log(8N)` and `c_b ≥ N/(2 log(N/((1−γ)δ)))`. Then
  `b(s,a₁;·) = 2 + 5/N` (the linear term is clipped at `1/(1−γ)`), `b(s,a₂;·) = 2 + 5/N` (zero count), so every iterate is
  `Q̂ ≡ 0`, `π̂ ≡ a₂` is greedy, and `V⋆(ρ) − V^{π̂}(ρ) = 2 > ε` surely, while `1 − 2δ = 1/2`. I checked it numerically
  (`python3 -I`, scratchpad): for `c₁ = 9.6·10⁵` (`N = 204324848`, `τmax = 40`) and `c₁ = 10⁷` (`N = 2327387740`, `τmax = 45`),
  `Q̂_{τmax} = (0,0)`. The proof's `c₁ = 10⁴c_b` matches the source's own dependence (`c₁ ≥ 140²c_b` at `:1621`).
- **N2 (`N ≥ 1`).** `Params.N_pos` makes `N ≥ 1` a structural premise. The printed condition has `log(NS/…)` undefined at `N = 0`,
  so the source implicitly has `N ≥ 1`. Under Lean junk values at `N = 0` (`log 0 = 0`, `5/0 = 0`) the condition would hold and the
  conclusion can fail, so excluding `N = 0` is required. It is not a hidden restriction of the printed result. `N ≥ 2` (C19) is
  derived from the sample size, not assumed.
- **N3 (`C⋆ ≠ ⊤`).** When `C⋆ = ∞` the printed condition `N ≥ c₁ S·∞·…` has no solution, so the theorem says nothing there.
  The guard therefore loses no printed content and blocks the junk `⊤.toReal = 0`. `C⋆ ≥ 1` is proved (`one_le_concentrability`),
  not assumed.
- **N4 (`V⋆` encoding).** `V⋆(ρ)` is `ρ.expectation (trajectoryExpectedValue optimalGreedyPolicy)`, the value of the library's
  `Q⋆`-greedy deterministic policy, which is the chapter-wide convention also used by the LCB-Q entries (`optValue`). This is
  standard, and equal to the optimum by the library's optimality development. It is not re-derived here.
- **N5 (stronger forms).** The event covers **every** greedy `π̂` (any tie rule), and `π⋆` ranges over **every** `Q⋆`-greedy
  policy with `C⋆` computed from that `π⋆`. Both are at least as strong as the printed "the" `π̂` / "the" `π⋆`. Every optimal
  deterministic stationary policy is `Q⋆`-greedy, so no printed instance is lost.
- **N6 (no new source issue).** Steps 1–4 and Lemma 6.7's appendix proof check under the theorem's hypotheses. C10 does not
  apply (`γ ≥ 1/2`). C19 is discharged (`two_le_N_of_sample_size`). C23 is repaired inside the library Lemma 6.6. The
  Lemma 6.6 positive-count scope is enough because zero-count pairs are handled by the box bound, and on `S_large`
  `N_{s,π⋆} > 0`. The `Lemma6_7_restricted` premises are discharged for `V̂`, `b⋆` (`lemma67_instance`). The source remark at
  `:1184–1186` (`P̂Ṽ, PṼ ∈ [0,1/(1−γ)]`) is only valid for `Ṽ ≥ 0`, but it is only used at `Ṽ = V̂ ≥ 0`, which is what the
  Lean uses. Not a statement issue.
- **N7 (route differences, all sound).** (a) Pessimism uses an arg-min over states of `V^{π̂} − V̂`, not over pairs. (b) The
  occupancy reduction uses the flow equation instead of the Neumann limit. (c) Constants are `c_b ≥ 96`, `c₁ = 10⁴c_b`
  instead of the source's `70/140` bookkeeping. (d) The Case 1/Case 2 split is merged via `Q̂ ≤ max(tilde, 0)`. None of these
  changes the statement.
- **N8 (dependency drift).** `git diff --stat bf6db8b HEAD` over `Formalization/OfflineRL`, `Formalization/MDP`,
  `Formalization/Probability` and `Statements/Ch6.lean` is empty, so the library the WIP was built against is the one at HEAD.
  (Cross-check done after sections 1–4 were written: the builder's `the private preflight note (Thm6_3)` reconstruction agrees with mine on
  every point above, and nothing in it changes my findings.)

## 6. Docstring / disclosure requirements (for the `Thm6_3` entry and the export)

The `Thm6_3` docstring should state:
1. Source `thm:infinite-offline`, `chapters/offlineRL.tex:899–920`, proof `:1031–1623`, with the appendix lemmas it uses.
2. The reading of "c_b sufficiently large … c₁ large enough universal" as `∃c_b₀ ∀c_b ≥ c_b₀ ∃c₁` (`c₁` depends on `c_b` only),
   and that a `c₁` uniform in `c_b` is false (N1). The proof gives `c_b₀ = 96`, `c₁ = 10⁴c_b`.
3. `C⋆` is computed in `ℝ≥0∞` with `0/0 = 0`; the hypothesis `C⋆ ≠ ⊤` only removes the case where the printed condition is unsatisfiable.
4. `π⋆` is any `Q⋆`-greedy deterministic policy; the event covers every greedy output `π̂` (any tie rule).
5. `N ≥ 1` comes from `Params` (N2); data are `N` iid triples with law `d^b ⊗ P`; the same `δ` is used in the penalty, the
   events and `1 − 2δ`.
6. `V⋆` is the trajectory value of the library's optimal greedy policy (N4).

This is the **printed result**, not a `_corrected` or `_restricted` variant. No `SOURCE-ISSUES.md` entry is needed for `Thm6_3`
itself. Optionally, the C10, C19 and C23 entries could each gain one line saying they are discharged in the Theorem 6.3 proof.

## VERDICT

**PASS (faithful original statement; honest proof).** `Thm6_3` matches `thm:infinite-offline` in every hypothesis and in the
conclusion, under the only correct quantifier reading. Its additions (`C⋆ ≠ ⊤`, `N ≥ 1`, every greedy `π̂`, every `Q⋆`-greedy
`π⋆`) remove no printed content. The proof route is sound step by step. The wrapper only applies `vilcb_infinite_offline`.
No forbidden tokens were found in the WIP files or the library import closure. The builder's output reports only
`propext`, `Classical.choice`, `Quot.sound`.
Conditions before recording it as proved: M1 docstring disclosures, and M3 integration with a fresh compile and axiom audit
(I did not reproduce them).
