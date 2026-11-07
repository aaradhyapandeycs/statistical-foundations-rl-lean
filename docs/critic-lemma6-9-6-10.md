# CRITIC: Lemma 6.9 (`lemma:Q-recursion-pessimistic-Q`) and Lemma 6.10 (`lemma:pessimistic-Q`)

Public copy of the independent critic report; local paths removed.

- Date: 2026-11-07 02:29 UTC
- Reviewer: independent Claude critic subagent (did not build this code)
- Git HEAD: `6d98f9582477ca46a5af71c2d729326362c263a6` (branch `recovery-batch-ch5-online-lower-bound-20261106`; LCBQ files are untracked working-tree files)
- Mode: source-only review. No Lean, lake, LSP or compiler was run. Numerics were run with `python3 -I` in the session scratchpad, outside the project.
- Reading order: the source reconstruction and the comparison below were written before I read any PREFLIGHT, BUILD-LOG, PROGRESS or other CRITIC file. I read `docs/SOURCE-ISSUES.md` (C18, C20, C22, C24), which the brief allows.

## SHA-256

| File | SHA-256 |
|---|---|
| `source/upstream/tex/chapters/offlineRL.tex` | `67cf0d1ce6a3d7c6cc43aedb371c692a3da0508193d735609713b03c0186f1e4` (matches `source/provenance.json`) |
| `<builder working folder>/StatementProbe.lean` | `17ae06c9f6efee65267cb144897a107acac121eec78ce188a955ade8cfeac5c8` |
| `Formalization/OfflineRL/LCBQDefinitions.lean` | `1baec0102770ae977b805b7bbc22513ba3e9343c0863d0b4b98a648c6b14f39f` |
| `Formalization/OfflineRL/LCBQPathwise.lean` | `4573150b4801d00a71f62f5d0bdaf3395ec8726dc25100daaabe48e99c74c1c6` |
| `Formalization/OfflineRL/LCBQPessimism.lean` | `1899ca068b252187fe22ba1f3d7fe5142ca6f4fac49907c8b8bcd025ad51e323` |
| `Formalization/OfflineRL/LCBQRecursion.lean` | `3faa7801f320fc56140eb13c256bb6fdee171a4221343d5c52f84ad5586b698f` |
| `Formalization/OfflineRL/LCBQMartingale.lean` | `9dbbacda5e611415bbaa9e85020f6e55e1684ad28637070cdf3426fe20ca8616` |
| `Formalization/Probability/AzumaFiltrationSource.lean` | `d77f1abc656514324cebc35f02874414cc6da4368bc16997d83d0c691df40d99` |
| `docs/SOURCE-ISSUES.md` (read only) | `0c190bfeaa600d15afd32aac859dc997803556ffa61949be2040436b3546748f` |

## 1. Source reconstruction (from the .tex only)

**Data model** (`eq:sampling-offline-inf-iid`, :28–39; model-free use at :1631). Independent triples: `(s_i,a_i) ~ d^b` and `s_i' ~ P(·|s_i,a_i)`. The algorithm draws a fresh triple at each of `T` iterations (:1711), so it consumes `T` iid triples.

**Parameters** (:1663–1689). `δ ∈ (0,1)`, `H = ⌈(4/(1−γ)) log(SAT/δ)⌉`, `η_n = (H+1)/(H+n)`, `b_n = c_b √(H log(SAT/δ)/(n(1−γ)²))`, and `c_b > 0` a universal constant. `ι := log(SAT/δ)` (:1849–1852).

**Algorithm** `alg:q-infinite-lcb` (:1701–1745). Initialise `Q ≡ 0`, `V ≡ 0`, `n ≡ 0` and an arbitrary deterministic `π̂`. For `t = 1..T`: draw `(s_t,a_t,s_t')`, set `n(s_t,a_t) += 1` and `n := n(s_t,a_t)`. Update `Q(s_t,a_t) ← (1−η_n)Q(s_t,a_t) + η_n{r + γV(s_t') − b_n}`. Set `V_old ← V` and `V(s_t) ← max{V_old(s_t), max_a Q(s_t,a)}`. If `V(s_t) > V_old(s_t)`, set `π̂(s_t) ← argmax_a Q(s_t,a)` with "an arbitrary deterministic" tie rule. The analysis policy `π_t` is defined at :1826–1832 (`eq:analysis-policy-lcbq`), and `π̂ = π_T`.

**Notation** (:1810–1854). `Q_t, V_t` are the iterates at the end of iteration `t`, `n_t(s,a)` counts visits among the first `t` iterations, and `k_i(s,a)` is the time of the `i`-th visit. `η_i^n` comes from onlineRL.tex :1995–2010, and `Σ_{i=1}^n η_i^n = 1` for `n ≥ 1`. The bounds `0 ≤ V_t ≤ 1/(1−γ)` hold (:1844).

**Lemma 6.9** (:1866–1893). There is a constant `c_b` large enough such that, with probability **at least** `1−δ`, simultaneously for all `(s,a)`, all `1 ≤ t ≤ T` and all deterministic `π`:
- (a) `Q⋆(s,a) − Q_t(s,a) ≤ γ Σ_{i=1}^{n} η_i^{n} P_{s,a}(V⋆ − V_{k_i−1}) + β_n` with `n = n_t(s,a)`, where `β_n = 3c_b√(Hι/(n(1−γ)²))` for `n ≥ 1` and `β_0 = +∞`;
- (b) `Q^π(s,a) − Q_t(s,a) ≥ γ Σ_{i=1}^{n} η_i^{n} P_{s,a}(V^π − V_{k_i−1})`.

The proof (:4415–4528) does the following:
1. It unrolls `Q_t = Σ η_i^n{r + γV_{k_i−1}(s'_{k_i}) − b_i}`.
2. It writes the error identity `(Q^• − Q_t) = γΣ η P(V^• − V_{k_i−1}) + γΣ η (P − P_{k_i})V_{k_i−1} + Σ η b_i`.
3. It applies Azuma "for fixed ℓ", with a union over `ℓ ≤ T`, to get the radius `2√(H log(2SAT²/δ)/(ℓ(1−γ)²))`, then sets `ℓ = n`.
4. It bounds the weighted penalty: `c_b√(Hι/(n(1−γ)²)) ≤ Σ η_i^n b_i ≤ 2c_b√(…)`.
5. It absorbs the log factor when `c_b` is large. Both inequalities need `|dev| ≤ c_b√(Hι/(n(1−γ)²))`.
6. It takes a union bound over `(s,a,t)`. Part (b) holds for all π, including data-dependent π, because the deviation term does not depend on π.

**Lemma 6.10** (:1907–1916). With probability **exceeding** `1−δ`, `Q_t ≤ Q⋆` and `V_t ≤ V^{π_t} ≤ V⋆`, for all `(s,a)` and all `1 ≤ t ≤ T`. The printed statement does **not** repeat the "c_b large enough" premise. The proof (:4530–4672) runs on the event of Lemma 6.9:
1. Set π = π⋆ in (b) to get a lower recursion. Induction on `t` then gives `Q_t ≤ Q⋆` and `V_t ≤ V⋆`.
2. For `V_t ≤ V^{π_t}`, take the last strict increase `τ_s`. Then `V_t(s) = Q_{τ_s}(s,π_t(s))`. Apply (b) with `π = π_t` and `t = τ_s`. With `m = min_s(V^{π_t} − V_t)`, this gives `m ≥ min{0, γm}`, so `m ≥ 0`.
3. `V^{π_t} ≤ V⋆` is standard.

### Independent checks on the printed proof

- **Azuma at random visit times (T1).** The printed proof applies Azuma to `Σ_{i≤ℓ} η_i^ℓ (P_{s,a} − P_{k_i})V_{k_i−1}` "for fixed ℓ". It names no filtration. It also does not address that `k_i` is undefined when `i > n_T(s,a)`: the data are finite, and if `d^b(s,a) = 0` the pair may never be visited. The step can be repaired in two standard ways. One is zero-padding, which gives a martingale in `𝔽_{k_i∧(T+1)}` with the same bounds, by optional sampling for the iid stream. The other is to condition on the label sequence, as the Lean does. This is an omitted argument, not a false step, and the statement is unaffected.
- **Log absorption corner.** The proof needs `4 log(2SAT²/δ) ≤ c_b² ι`. For `T ≥ 2`, `ι > log(SAT) ≥ max(log 2, log T)`, so `log(2SAT²/δ) ≤ 3ι` and `c_b ≥ √12` suffices. For `S = A = T = 1` and `δ > 1/2`, `ι = log(1/δ) < log 2`, and no universal `c_b` makes the printed chain valid. The conclusion still holds there, because at `T = 1` the deviation term is `0` (`V_0 = 0`). This is a printed-proof corner, not a statement error.
- **Union-bound accounting.** The proof states "1−δ/(SAT)" for each fixed `(s,a,t)`, although the event does not depend on `t`, and then takes a union over `t`. The total is still ≤ δ. Harmless.
- **Lemma 6.10 needs the c_b premise.** As a standalone statement for an arbitrary universal `c_b > 0`, it is false (numerical check below). The premise is inherited from the context (Theorem 6.8 :1764, Lemma 6.9 :1884).
- **Strictness.** Lemma 6.9 is printed as "≥ 1−δ" and Lemma 6.10 as "> 1−δ". Taken alone, the printed proof of 6.10 delivers only ≥. Strictness is still available because the Azuma tail bound, as formalised, is strict.

### Numerical counterexample: Lemma 6.10 with small c_b

Script: scratchpad `lcbq_cex.py`, run with `python3 -I`; exact enumeration of all `3^T` data sequences.

Setup: `S = {0,1}`, `A = {•}`, `P(·|0) = (½,½)`, `P(·|1) = (0,1)`, `r = (0,1)`, `γ = ½`, `d^b = (½,½)`, `T = 3`, `δ = 0.01`. This gives `ι = 6.397`, `H = 52`, `Q⋆ = (2/3, 2)`.

| `c_b` | `P(∃t: Q_t ≰ Q⋆)` |
|---|---|
| 1e-4 | 0.0625 |
| 1e-3 | 0.0625 |
| 1e-2 | 0 |
| 0.1 | 0 |
| 4 | 0 |

For `c_b ≤ 10⁻³`, the failure probability `1/16` exceeds `δ`, so the printed Lemma 6.10 without the c_b premise fails. The Lean entry's `∃ cb₀, ∀ cb ≥ cb₀` is necessary, not cosmetic.

## 2. Lean model fidelity (`LCBQDefinitions.lean`)

| Item | Source | Lean | Verdict |
|---|---|---|---|
| ι | `log(SAT/δ)` | `iota S A T δ = log(card S·card A·T/δ)` | match |
| H | `⌈4ι/(1−γ)⌉` | `horizon γ ι = ⌈4/(1−γ)·ι⌉₊` | match (`ι > 0` and `H ≥ 1` once `T ≥ 1`; `iota_pos`, `horizon_pos`) |
| η_n | `(H+1)/(H+n)` | `onlineQRate H n` | match |
| η_i^n | onlineRL :1995 | `onlineQRateWeight H n i` (n≥1 branch `η_i Π_{j>i}(1−η_j)`) | match |
| b_n | `c_b√(Hι/(n(1−γ)²))` | `penalty cb γ ι H n`, evaluated at `k = count+1 ≥ 1` | match |
| Q update | `(1−η_n)Q + η_n(r + γV(s') − b_n)`, with the new `n` | `step`: `k := count+1`; uses pre-update `σ.V x.2` | match (`V(s')` read before the V update, as in the pseudocode) |
| V update | `max{V_old(s_t), max_a Q(s_t,a)}`, only at `s_t` | `max (σ.V s) (actionMaximum (Q' s))`, only at `s` | match |
| policy | strict increase → `argmax_a Q(s_t,·)` on the updated Q | `σ.V s < v → sel (Q' s)` | match |
| tie rule | "arbitrary deterministic rule" | `sel : (A → ℝ) → A` with `∀ f a, f a ≤ f (sel f)`, quantified ∀ | see MINOR-1 |
| init | `Q=V=n=0`, arbitrary det. `π₀` | `init π₀`, ∀ π₀ | match |
| indexing | iteration `t` reads sample `t` | `run (t+1)` reads `data ⟨t⟩` | match |
| `k_i − 1` | time before the `i`-th visit | `visitTime data sa (i−1)` (zero-based sample index), so `V_{k_i−1} = (run (visitTime … (i−1))).V` | match: `run u` has processed samples `0..u−1` |
| `n_t(s,a)` | visits among the first `t` | `(run t).count s a` (`run_count`: `= Nat.count visitPred t`) | match |
| `β_0 = ∞` | (a) is vacuous at `n = 0` | guard `0 < n →` in (a); no guard in (b) | match ((b) at `n = 0` reads `0 ≤ Q^π`, true since `r ≥ 0`) |
| Q⋆ | Bellman optimality fixed point | `M.optimalityFixedPoint` | match |
| V⋆ | optimal value | `trajectoryExpectedValue optimalGreedyPolicy`; `optValue_eq`: `= max_a Q⋆`; `trajectoryValue_le_optimalGreedy` | match (stationary-policy convention, standard) |
| Q^π, V^π | policy values of a deterministic π | `trajectoryExpectedQ/Value (pointMass ∘ π)` | match |
| data law | `T` iid triples, `d^b ⊗ P` | `X : Ω → Fin T → (S×A)×S`, measurable, `iIndepFun`, marginals `Σ_x db(x.1)P(x.2|x.1) δ_x` | match |
| T = 0 | — | `ι = log 0 = 0` is junk but never used: the event is vacuous (`1 ≤ t ≤ 0`), the probability is 1 ≥ 1−δ, and 1 > 1−δ | harmless |
| δ range | `δ ∈ (0,1)` | `0 < δ`, `δ < 1` | match |
| γ range | `γ ∈ [0,1)` | structure fields | match |

## 3. Statement comparison

### Lemma 6.9 (`Lemma6_9` in the probe)

| Aspect | Source | Probe | Verdict |
|---|---|---|---|
| c_b large | "provided c_b > 0 large enough" | `∃ cb₀ > 0, ∀ cb ≥ cb₀` (cb₀ = 4), uniform over S, A, M, d^b, sel, π₀, T, δ, Ω | faithful, strongest natural reading |
| probability | "at least 1−δ" | `1 − δ ≤ μ.real {…}` | match (the library proves `<`; the wrapper weakens it with `.le`) |
| scope | all (s,a), all 1≤t≤T, all det. π | `∀ t, 1 ≤ t → t ≤ T → ∀ s a`; `∀ π : S → A` inside the event | match; data-dependent π are covered because ∀π sits inside the event |
| (a) constants | `3c_b√(Hι/(n(1−γ)²))`, weights `η_i^n`, `P_{s,a}(V⋆ − V_{k_i−1})` | `3 * cb * √(H*ι/(n*(1−γ)²))`, `onlineQRateWeight H n (i+1)`, `expectation (V⋆ − (run (k i)).V)`, sum over `range n` | match (zero-based shift of `i`) |
| (b) | `Q^π − Q_t ≥ γΣ η P(V^π − V_{k_i−1})` | same, as `≤` with the sides swapped | match |
| measurability | — | the event is `X⁻¹(B)` with `B ⊆` a finite type (σ-algebra ⊤), so `μ.real` is not an outer-measure loophole | OK |

### Lemma 6.10 (`Lemma6_10` in the probe)

| Aspect | Source | Probe | Verdict |
|---|---|---|---|
| c_b | not printed in the lemma (ambient) | `∃ cb₀ > 0, ∀ cb ≥ cb₀` | **necessary** (counterexample above); see MAJOR-1 for disclosure |
| probability | "exceeding 1−δ" | `1 − δ < μ.real {…}` | match (strict, as printed) |
| conclusions | `Q_t ≤ Q⋆`, `V_t ≤ V^{π_t} ≤ V⋆`, all (s,a), 1≤t≤T | all three, with `π_t = (run t).policy` | match |
| tie rule | arbitrary deterministic | ∀ `sel` row-selectors with the argmax property | MINOR-1 |

## 4. Proof route and honesty

- **Label conditioning** (`LCBQMartingale.lean`). The law of `X` is `Π_t (d^b ⊗ P)` (`hlaw`, from `iIndepFun_iff_map_fun_eq_pi_map`). It is regrouped as `Σ_l Π d^b(l_t) · ν_l`, where `ν_l = ⊗_t P(·|l_t)`.
- Under `ν_l`, `martSum` is the sum over sample indices `u` of `w_u (V_u(y_u) − P_{l_u}V_u)`. The weight is `w_u = γη^n_{rank+1}·1{u is among the first n visits}`, which depends on the labels only. `V_u` depends only on `y_{<u}` (`run_congr_prefix`). So the increments are revealed-prefix martingale differences: adapted, centred and bounded by `w_u/(1−γ)`.
- `azuma_filtration_strict` gives the radius `2√(H log(2/δ')/(n(1−γ)²))`, using `Σ w²/(1−γ)² ≤ 2H/(n(1−γ)²)`. This uses `γ² ≤ 1`, and `sum_visits_le` handles `n > n_T(s,a)` because padding is implicit.
- A union over the `SAT` triples `(s,a,n)` with `δ' = δ/(SAT)` gives conditional failure `< δ`. Averaging over labels gives failure `< δ`. This is **sound**. It is tighter than the printed `log(2SAT²/δ)`, and it closes the T1 gap rather than validating the printed step. The file docstring says so honestly.
- **Deterministic part** (`LCBQRecursion.lean`). `error_identity` combined with `penalty_sum_bounds` and `martSum_le_of_martingaleEvent` (`cb ≥ 4`: `4(log 2 + ι) ≤ 8ι ≤ cb²ι` for `T ≥ 2`; the `T = 1` case uses `martSum = 0`) gives (a) and (b). The `n = 0` branch of (b) uses `policyFixedPoint_bounds` (`Q^π ≥ 0`).
- **Lemma 6.10** (`LCBQPessimism.lean`) follows the printed induction and the last-strict-increase/minimum argument. `run_policy_lastIncrease` and `actionMaximum_eq_sel` use `hsel`.
- **Wrappers.** `Lemma6_9_holds` applies `lemma69_prob`, weakens `<` to `≤`, and repackages the conjunction. `Lemma6_10_holds` is a direct `exact lemma610_prob`. Neither proves anything a second time. I did not compile them, so the defeq between `detPolicy π` and `fun x => pointMass (π x)`, and the `let` unfolding, is unverified by me.
- **Forbidden tokens.** I grepped the Formalization import closure of `LCBQMartingale` and `LCBQDefinitions` (69 modules, comments stripped) and the probe for `sorry`, `admit`, `axiom` declarations, `opaque`, `implemented_by`, `unsafe`, `native_decide`, `@[extern` and `ofReduceBool`. There are **0 hits**. The probe contains only `#print axioms` lines. I did not run the axiom audit.

## 5. Findings

**BLOCKING:** none.

**MAJOR-1 (disclosure; naming of `Lemma6_10`).** Printed Lemma 6.10 has no `c_b` premise. For small universal `c_b > 0` it is false: the exact enumeration above gives failure probability `1/16 > δ = 0.01` at `c_b ≤ 10⁻³`. The probe's `∃ cb₀ ∀ cb ≥ cb₀` is necessary. Under the AGENTS.md rule ("export assumes more → `_restricted`/`_corrected`" plus a `SOURCE-ISSUES` entry), this needs an explicit decision. Two acceptable options:
- (i) Keep the name `Lemma6_10`. The docstring must say that "c_b sufficiently large" is the standing assumption of the analysis of Theorem 6.8 (:1764) and Lemma 6.9 (:1884), and a SOURCE-ISSUES note should record that the lemma as printed omits it, with the counterexample.
- (ii) Rename the entry `Lemma6_10_restricted` and add the same note.

I lean to (i), since the lemma sits inside the proof of Theorem 6.8, but the docstring and the note are required either way. The mathematics of the Lean entry is correct. The issue is only how the entry is presented.

**MINOR-1 (tie-rule scope).** `sel : (A → ℝ) → A` covers every tie rule that is a function of the current Q-row, including every rule that is a function of the argmax set. It does not cover rules that depend on the state, the time or the history. The proof uses only `hsel` pointwise, so generalising to `sel : S → (A → ℝ) → A`, or to an iteration-indexed selector, would be cheap. Otherwise, disclose it in the docstring, consistent with the precedent in C20. Lemma 6.9 is unaffected, because its Q and V iterates do not depend on `sel`.

**MINOR-2 (printed-proof gap T1; suggested SOURCE-ISSUES note).** The printed proof applies Azuma "for fixed ℓ" at random visit times without a filtration or a convention for undefined `k_i`. It also has the `S = A = T = 1`, `δ > ½` log-absorption corner. The statement is unaffected, and the Lean route avoids both problems. Text is suggested below.

**NOTE-1.** The probe docstrings cite `:1866–1893` and `:1907–1916` for the statements and `:4415–4528` and `:4530–4672` for the proofs. These match the pinned file (the statement begins at `\begin{lemma}` on 1866 and 1907).

**NOTE-2.** Lemma 6.9 carries the `hsel` premise even though the Q and V iterates do not depend on it. This is harmless: a valid selector always exists for nonempty finite A, so it is not a restriction in substance.

**NOTE-3.** The probe's `#print axioms` output was not observed by me. Proof-evidence claims must rest on the lead's actual build log.

## 6. Suggested SOURCE-ISSUES text

> ## Candidate C28: Lemma 6.10 omits the c_b premise; Lemma 6.9 proof applies Azuma at undefined random visit times
>
> **Source:** `chapters/offlineRL.tex`, Lemma 6.9 `lemma:Q-recursion-pessimistic-Q` (:1866–1893, proof :4415–4528) and Lemma 6.10 `lemma:pessimistic-Q` (:1907–1916, proof :4530–4672).
>
> (1) Lemma 6.10 does not repeat Lemma 6.9's requirement that `c_b` be large enough, and its proof depends on Lemma 6.9. As a standalone claim for an arbitrary universal `c_b > 0`, it fails. Counterexample: `S = {0,1}`, one action, `P(·|0) = (½,½)`, `P(·|1) = δ_1`, `r = (0,1)`, `γ = ½`, `d^b` uniform, `T = 3`, `δ = 0.01`. Exact enumeration gives `P(∃t: Q_t ≰ Q⋆) = 1/16 > δ` for `c_b ≤ 10⁻³`. The premise is the standing assumption of Theorem 6.8 (:1764). The formal entry states it as `∃ c_b₀, ∀ c_b ≥ c_b₀` (`c_b₀ = 4`).
>
> (2) The proof of Lemma 6.9 (:4476–4491) applies Azuma–Hoeffding "for fixed ℓ" to `Σ_{i≤ℓ} η_i^ℓ (P_{s,a} − P_{k_i})V_{k_i−1}`. It names no filtration, and `k_i` is undefined when `i` exceeds the number of visits within `T` iterations. The step can be repaired, by zero-padding with optional sampling or by conditioning on the state-action labels. The latter is the formal route, with the union over `(s,a,n)` at radius `2√(H log(2SAT/δ)/(n(1−γ)²))`. Separately, the absorption `log(2SAT²/δ) ≲ ι` fails for `S = A = T = 1`, `δ > ½`; the conclusion still holds there because the martingale term vanishes at `T = 1`.
>
> Neither point changes Lemma 6.9 or Theorem 6.8.

## 7. Advisory: the untested Step-3 definitions (:1970–2018)

- `dWeight` matches `d_j(s,a) = [ρᵀP_{π⋆}^j](s)·1{a = π⋆(s)}`, assuming `occupancyStateAt (detPolicy π) ρ j` is `ρᵀP_π^j`, which its name and definition suggest.
- `alphaSeq`, `thetaSeq` and `xiSeq` match `κ^j Σ_{t=1}^T ρᵀP^jΔ_t`, `κ^j Σ_t Σ_s [ρᵀP^j](s) min{β_{n_t(s,π⋆(s))}, 1/(1−γ)}` (via `betaTrunc`: `n = 0 ↦ 1/(1−γ)`, matching `β_0 = ∞`) and `κ^{j+1}ρᵀP^{j+1}Δ_0`. `κ = γ(1+1/H)³` matches.
- In `psiSeq` and `phiSeq`, iteration `t` corresponds to `Fin T` index `t−1`: they use `data t` for `(s_t,a_t)`, `t.val+1` for `n_t`, and `delta … t.val` for `Δ_{t−1}`. The factors `γκ^j`, `(1+1/H)` and `(1+1/H)²` sit where the source puts them. Inner sums use `Δ_{k_i−1}` via `visitTime`. All of this matches.
- The ratio `d_j/d^b` uses real `x/0 = 0`. This is irrelevant almost surely, as documented.
- `concentrability` is `⨆_{(s,a)} ofReal(d⋆)/ofReal(d^b)` in `ℝ≥0∞`. That gives `0/0 = 0` (as printed) and `x/0 = ∞`. It uses the normalised `(1−γ)Σγ^t` occupancy, consistent with prelim :146–172.
- Caveat: `πstar` is a free parameter, so consumers must instantiate it with an optimal deterministic policy. These definitions have not been exercised by any theorem I inspected. Fidelity looks right, but this is advisory only.

## VERDICT

- **Lemma 6.9 (`Lemma6_9`, wrapper `Lemma6_9_holds`): PASS.** It is a faithful translation of the printed statement: constants, weights, visit times, all deterministic π, `∃cb₀ ∀cb ≥ cb₀`, and probability `≥ 1−δ`. The proof route is sound and the wrapper only applies the export. This is conditional on the lead's compile and axiom evidence.
- **Lemma 6.10 (`Lemma6_10`, wrapper `Lemma6_10_holds`): PASS WITH REQUIRED DISCLOSURE (MAJOR-1).** The mathematics is correct and the strict `> 1−δ` matches the print. The necessary `c_b` premise is absent from the printed lemma and must be disclosed, via a docstring plus a SOURCE-ISSUES note (or the `_restricted` naming). The tie-rule scope (MINOR-1) should be generalised or disclosed.
