# CHECK — the builder's private plan (asynchronous Q-learning, `thm:infinite-horizon-asyn`) — independent critic

Public copy of the independent critic report; local paths removed.

Date 2026-11-07. Source-only paper check. No Lean, lake or lean-lsp was run. I wrote only this file and
`<reviewer check folder>/{check.py,check.out}`, run with `python3 -I check.py` (≈5 s, stdlib only).
The cited works (li2024q, paulin2015concentration) were not consulted.

Pin: `source/upstream/tex/chapters/generative_model_model_free.tex` sha256
`7f4eb058e00480bc0694cac93ac41e22f4cfe48aa58a00c4ccf909f805e60b22`, which matches `source/provenance.json:35`.

**Overall verdict: GO**, with the required corrections in §6. None of them changes the mathematics of the plan. Two
of them change the draft `Prop` (an import-policy violation and the quantifier shape of the index entry).

---

## 0. My reconstruction of the printed statement (done before reading the plan)

- **Model** (`:1898–1906`). There is a single trajectory from an initial state `s_0`:
  `a_t ∼ π_b(·|s_t)`, `r_t = r(s_t,a_t)`, `s_{t+1} ∼ P(·|s_t,a_t)`. The pairs `(s_t,a_t)` form a homogeneous chain
  with kernel `K((s,a),(s',a')) = P(s'|s,a)π_b(a'|s')`.
  - `s_0` is not said to be random or stationary, so the theorem must hold for every `s_0`.
  - Rewards satisfy `r ∈ [0,1]`, the book-wide convention, which is a field of `DiscountedMDP`.
- **Algorithm** (`:1928–1946`, `:1977–2001`). For `t = 1..T`, only entry `(s_{t-1},a_{t-1})` is updated:
  `(1−η_t)Q_{t-1} + η_t(r + γ max_{a'} Q_{t-1}(s_t,a'))`.
  - The output is `Q_T`.
  - `:1937` describes `η_t ∈ (0,1)`.
- **Uniform ergodicity** (`:2012–2015`). The definition is delegated to Paulin. `μ_{π_b}` is "its stationary
  distribution", which presupposes uniqueness; uniqueness is implied by uniform ergodicity.
- **Key quantities.**
  - `μ_min = min μ` (`:2024–2028`).
  - `t_mix = min{t : max_{(s,a)} TV(P^t(·|s,a), μ) ≤ 1/4}` (`:2034–2039`). The range of `t` is unstated.
- **Rate** (`:2054–2058`). `η_t ≡ c₁ log³T/((1−γ)Tμ_min)`, "for some universal constants `0 < c₁ ≤ 1`".
- **Theorem** (`:2062–2086`).
  - Quantifiers: `∀ δ ∈ (0,1)`, `ε ∈ (0,1]`, `γ ∈ [1/2,1)`.
  - Hypotheses: Assumption, `T ≥ c₂ log²(SAT/δ)/μ_min · max{log³T/((1−γ)⁴ε²), t_mix/(1−γ)}` with `c₂` "sufficiently
    large universal", and `0 ≤ Q_0 ≤ 1/(1−γ)`.
  - Conclusion: `max|Q_T − Q⋆| ≤ ε` with probability `≥ 1−δ`.
- **Proof.** Omitted (`:2126`). The heuristic uses windows of length `Θ̃(t_mix/μ_min)` and Paulin Thm 3.14.
- The lower bound `thm:LB-asynQ` is inside `\begin{comment}` (`:2133–2157`).

---

## 1. Transcription (plan §1) — **CONFIRMED**

The plan's §1.1–1.5 match my reconstruction line by line. Specifically:

- the pair kernel and the initial pair law `ν = δ_{s_0} ⊗ π_b(·|s_0)`;
- the update, the output `Q_T` and the `:1937` constraint;
- the ℕ-indexed `t_mix` (0 allowed);
- the rate `0 ≤ t ≤ T`;
- the budget with natural logs;
- the omitted proof and the commented-out lower bound.

The line numbers are correct: `:1902`, `:1937`, `:2000`, `:2013`, `:2026`, `:2037`, `:2056`, `:2063`, `:2126`,
`:2133–2157`.

The reading of `t_mix` as a min over ℕ is the stronger choice. If `t ≥ 1` is intended, that value is `max(t_mix,1)`
because `d` is nonincreasing. The budget is monotone in `t_mix`, so the ℕ-reading theorem implies the `t ≥ 1` one.

---

## 2. C34 failures and the weakest correction (plan §2) — **CONFIRMED**

Re-checked with my own script.

### 2.1 Failure at `T = 1` (`S = A = 1`)

- The chain is constant, so `d(0) = 0` and `t_mix = 0`.
- The budget's right side is `0` for every `c₂` and `δ`.
- `η = 0`, so `Q_1 = Q_0 = 0`, while `Q⋆ = 2`. The error is 2 > ε = 1.
- Under the `t ≥ 1` reading (`t_mix = 1`) it still fails for `δ` close to 1. Script rows: `c₂ ∈ {1, 10⁵, 10⁹}`.
- Under the `:1937` reading, the rate value 0 violates `η ∈ (0,1)`, so the literal instance is ill-posed. Either way
  the printed statement is not true as stated.

### 2.2 `μ_min = 0`

Take `S = 1`, `A = 2` and `π_b = δ_0`. The chain is constant and uniformly ergodic with `μ_min = 0`. The pair `(s,1)`
is never updated, so `Q_T(s,1) = 0 ≠ 2` for every rate (script: `η ∈ {0.05, 0.5}`).

### 2.3 Is "`2 ≤ T` and `0 < μ_min`" the weakest correction?

It is the weakest natural one.

- `0 < μ_min` is necessary for every rate.
- Given `0 < μ_min`, the plan's proof (verified in §3) covers every `T ≥ 2`.
- With `SA ≥ 2` and `c₂ ≥ 1`, the budget already excludes `T = 1`. In that case `d(0) = max_x(1−μ(x)) ≥ 1/2`, so
  `t_mix ≥ 1`, and the right side is at least `4c₂log²2 ≈ 1.92c₂` (script).
- The strictly weakest form would therefore be `2 ≤ T ∨ 2 ≤ SA` (together with `1 ≤ T`). The uniform `2 ≤ T`
  matches `Thm4_6` (`:896`) and is acceptable if disclosed.

### 2.4 Is anything else needed?

**No.** None of the following needs to be added:
- **Stationary initial state:** Lemma V is uniform over the initial law (§3.4).
- **Extra `γ` range:** `γ ≥ 1/2` is used only for `h⁴ ≥ 16`.
- **Extra `ε` range:** `ε ≤ 1` is used only in (A1) and (A3).
- **`A ≥ 2`:** never used.
- **Uniqueness of `μ`:** implied by uniform ergodicity.
- **`η < 1`:** derived in (A2).

Uniform ergodicity itself is redundant given `d(t_mix) ≤ 1/4` on a finite chain, but it is printed, so keep it.

---

## 3. The proof (plan §3) — **CONFIRMED** (re-derived independently)

### 3.1 One-step identity and unrolling (U)

Re-derived. At a visit, substituting `r(z) = Q^+(z) − γP_zV^+ − Q^+_res(z)` gives the plan's one-step identity
exactly. The unrolled weights are `w_i = η1_i(1−η)^{N_{(i,t]}}` and `Σw_i = 1−Π`.

Script (300 random asynchronous runs, arbitrary comparator):
- (U) holds to 1e-9;
- `Σw = 1−Π` holds;
- `w_i = c_i^{(n)}` holds with `n = N_{(τ,t]}`;
- `Σ c_i² ≤ η` holds.

### 3.2 Filtration and the `n`-indexed weights — correct

- `N_{(τ,i]}(z) = #{j ∈ (τ,i] : X_{j−1} = z}` depends on `X_τ..X_{i−1}`, so `c_i^{(n)}` is `F_{i−1}`-measurable in
  the pair-chain filtration `F_i = σ(X_0..X_i)`.
- On `{N_{(τ,t]} = n}`, every visit `i` has `N_{(τ,i]} ≤ n` and `N_{(i,t]} = n − N_{(τ,i]}`. So `w_i = c_i^{(n)}`
  holds identically on that event. The union over the deterministic indices `(σ,z,k,t,n)` is legitimate.
- **Do actions and next states arrive together?** In the pair chain, `X_i = (s_i,a_i)` is revealed at once. The
  increment `D_i = V^+(s_i) − P_zV^+` is `F_i`-measurable. Given `F_{i−1}`, `s_i ∼ P(·|X_{i−1})`, and `a_i` plays no
  role in `D_i`. Therefore, on a visit:
  - `E[D_i|F_{i−1}] = 0`;
  - `E[D_i²|F_{i−1}] = Var_{P_z}V^+`.
- **Predictable second moment.** At the `m`-th visit, `c = η(1−η)^{n−m}`, and later visits contribute 0. So
  `W ≤ γ²Var·η²/(1−(1−η)²) ≤ γ²ηVar`, deterministically.
- **Why the existing coordinate layout does not work.** In `infiniteTrajectoryLaw`, `(a_{t}, s_{t+1})` share one
  coordinate. There, `1{X_{i−1} = z}` is not predictable for `D_i`, and `c^{(n)}` inherits that. The pair filtration
  (or an interleaved `s_0,a_0,s_1,a_1,…` filtration) is required. The plan's diagnosis is right.
- **Interface match.** The use matches `freedman_source_bound` (`FreedmanExactAssembly.lean:236`):
  - `X n` is `ℱ(n+1)`-measurable;
  - `μ[X n|ℱ n] = 0`;
  - the a.e. cap is `W ≤ σ₂`;
  - with `K = 1`, `max(W, σ₂/2) ≤ σ₂` and `log(2K/δ₁) = L`.

  The bound becomes `γ√(ρVar) + γρh/6`, and `qChi_*Residual_bounds` lower bound
  `γ√(ρVar) + (2−γ)ρh ≥` this. The union size is `2·SA·K_ep·T·(T+1) ≤ 4SAT³`. Also
  `L = log(16SAT³/δ) ≤ 4ι ≤ 7ι` because `ι ≥ log T ≥ 32`.

### 3.3 Epoch contraction `M_{k+1} ≤ (γ+θ)M_k + θR` — correct

- For `t ∈ [τ_{k+1},T]`, every `i−1 ∈ [τ_k,t−1]`, so `(V_{i−1}−V^+)(s_i) ≤ u_{i−1} ≤ M_k`.
- On `G_F`, `ξ − (1−Π)Q_res ≤ ΠQ_res ≤ ΠR`. This uses `Q_res ≥ 0` from (C2).
- `Π ≤ e^{−ηN} ≤ e^{−ηm} = θ` because `N_{(τ_k,t]} ≥ N_{(τ_k,τ_{k+1}]} ≥ m`.
- The `max(0,·)` handles a negative bracket.
- The right side is `≥ 0`, so it bounds `M_{k+1}`.
- Closed form: `a^K h + θR/(1−a)`, where `a = γ+θ ≤ 1−(1−γ)/2`. Script: 3000 random cases hold.
- `M_0 ≤ h` from `Q_t ∈ [0,h]` (A4) and `Q^+ ≥ 0`. The `−` side is symmetric with `Q^- ≤ h`.
- The `θ` checks hold:
  - `ηm ≥ c₁log²T/32 ≥ log(8h²/ε)` (needs `log T ≥ 32/c₁` and `h²/ε ≤ √T`);
  - `K_ep ≤ 3h log T`;
  - `ℓ ≥ T/(4h log T)`.

### 3.4 Lemma V — correct; needs **no** stationary start

My derivation:

1. `|λK^k(z) − μ(z)| ≤ Σ_x λ(x)TV(K^k(x,·),μ) ≤ d(k)` for **any** initial law `λ`.
2. `d` is nonincreasing. This uses only `K^{t+1}(x,·) − μ = Σ_y K(x,y)(K^t(y,·) − μ)`, not stationarity.
3. `d(t) ≤ d̄(t)` uses stationarity of `μ` (μ is a mixture of rows), not of `X_0`. Also `d̄ ≤ 2d`, and
   submultiplicativity holds via the `D⁺/D⁻` decomposition.
4. From these, `d(kt̄) ≤ (2d(t̄))^k ≤ 2^{−k}` and `Σ_{m<b} d(m) ≤ 2t̄`.
5. With `bμ(z) ≥ 8t̄`:
   - `EV ∈ [¾,5/4]bμ`;
   - `EV² ≤ EV(1 + 2(bμ+2t̄)) ≤ (5/4)(21/8)(bμ)² = (105/32)(bμ)²`;
   - `E e^{−λ'V} ≤ exp(−¾x + (105/64)x²)` uniformly in `λ`.
6. Peeling blocks with the conditional block law `K(X_{s−1},·)` (or `ν` at `s = 0`) gives the bound
   `exp(J(−x/2 + 105x²/64))`. At `x = 16/105` this is `exp(−J/26.25)`.
7. Constants:
   - `b ≤ 9t̄/μ_min`;
   - `J ≥ ℓ/(2b) ≥ ℓμ_min/(18t̄)`;
   - `J ≥ 54ι` requires `ℓ ≥ 972t̄ι/μ_min`, which (A3) supplies with `c₂ ≥ 3888`.

Script, under arbitrary initial laws (all point masses plus random ones, 23 mixing random chains):
- `EV/(bμ) ∈ [0.914, 1.121]`;
- `EV²/(bμ)² ≤ 1.376`;
- submultiplicativity and monotonicity hold to 1e-15.

Only stationarity of `μ` (`μK = μ`) and `d(t_mix) ≤ 1/4` are used. Lemma V holds from **any** initial state, in
particular `ν`.

### 3.5 Reuse of the Theorem 4.6 χ² comparators — consistent

`qChi_upperResidual_bounds` and `qChi_lowerResidual_bounds` take `ρ ≥ 0`, a fixed point of `qRobustBellman±` with
offset `2ρ·effectiveHorizon`, and `hspan`. They do not need `A ≥ 2`.

`qComparisonFacts_stability_source` needs `0 < ρ`. This holds because `η > 0` and `L > 0`.

The offset term `2ρh²` in (C3) comes from the shift `b = 2ρh`. The builder must re-check its exact closure lemma, but
this is library-level and does not affect the paper proof.

### 3.6 Arithmetic (A1)–(A4) and §3.7 — correct

- `T ≥ 16c₂log⁵T` with `c₂ > C_thr` forces `log T > Λ`, because `T/log⁵T` is unimodal (decreasing, then
  increasing).
- `C_thr(1) = 1.4708·10⁵ < 1.5·10⁵` (script).
- The final error is `9ε/16 < ε`.

Nit: the plan writes `c₂ := max(C_thr, 3888)` while (A1) needs `c₂ > C_thr` strictly. It is harmless because `e^Λ` is
not an integer, but state `c₂ ≥ C_thr + 1` (or simply `1.5·10⁵` at `c₁ = 1`).

---

## 4. Constants and quantifiers — **ACCEPTABLE**

The printed text says "for some universal constants `0 < c₁ ≤ 1`" for the rate and "some sufficiently large universal
constant `c₂`" for the budget. The natural reading is `∃ c₁ ∈ (0,1], ∃ c₂ > 0`, which matches the existing `Thm4_6`
entry (`∃ c₁ c₂ c₃`).

| Reading | Status |
|---|---|
| `∀ c₁ ∃ c₂(c₁)` (proved) | Strictly stronger; implies `∃c₁∃c₂` |
| `∃ c₂ ∀ c₁` | **False** |

Why `∃ c₂ ∀ c₁` is false. Fix any `c₂`. Take the one-pair instance with `T = e^{40}`, which satisfies the budget at
`c₂ = 1.5·10⁵`. Its error is `≈ 2e^{−c₁log³T}`, which equals 1.876 > 1 at `c₁ = 10⁻⁶` (script).

So `c₂` must depend on `c₁` in every true reading. The growth `e^{32/c₁}` is a proof artifact; the true necessity is
only about `exp(c₁^{−1/3})`. It is acceptable: a fixed `c₁` gives a fixed universal `c₂`, e.g. `c₂ = 1.5·10⁵` at
`c₁ = 1`.

---

## 5. Draft `Prop` and module plan (plan §4) — **GO after corrections**

- **(R1, required) Import policy.** The draft uses `eventTV` from `RobustRL/TVCore.lean`. That file imports
  `Formalization.ModelFree.QLearningFinitePinskerCoarsening`, a proof module, and no `Statements/*.lean` file imports
  it. `Statements/Ch4.lean` must import definition modules only.
  - Fix: define the TV used in the entry (half-L1 or the event-sup) in `AsyncQ/Definitions.lean`, or move `eventTV`
    to a definitions-only module.
  - Prove its agreement with `eventTV` in a proof module.
  - Note: `eventTV` also needs `DecidableEq (S×A)`, so the entry needs `open Classical` or explicit binders.
- **(R2, required) Shape of the index entry.** AGENTS.md says the entry states the printed result; an export that
  concludes more is not a discrepancy.
  - The `_corrected` entry should therefore be the printed `∃ c₁, 0 < c₁ ∧ c₁ ≤ 1 ∧ ∃ c₂, 0 < c₂ ∧ …` with **only**
    the two C34 premises added.
  - The `∀ c₁ ∃ c₂` form belongs in the library theorem, and `Ch4Proofs.lean` derives the entry (e.g. at `c₁ = 1`).
  - If the lead prefers the `∀` form in the entry, the docstring and C34 must say so explicitly.
- **(R3, recommended) Other draft details.** Everything else in the draft is faithful:
  - stationarity is kept;
  - uniform ergodicity is `∃ C r, 0 ≤ r < 1, TV ≤ Cr^t`, where `C ≥ 0` is forced at `t = 0`;
  - `IsLeast` over ℕ for `t_mix`;
  - `μ_min` is attained;
  - `s₀` is universally quantified, which matches the printed arbitrary initial state;
  - `Q⋆ = M.trajectoryExpectedQ M.optimalGreedyPolicy` and `Q₀ ∈ [0, effectiveHorizon]`, as in `Thm4_6`;
  - rewards are in `[0,1]` via `DiscountedMDP`.
- **Finite path law vs. the infinite law.** `pathLaw` on `Fin (T+1) → S×A` with mass
  `1{x₀.1 = s₀}·π_b(a₀|s₀)·∏P(s_{i+1}|s_i,a_i)π_b(a_{i+1}|s_{i+1})` is a direct, checkable transcription of
  `:1900–1903` truncated at `T`. `Q_T` depends only on `X_0..X_{T−1}, s_T`.
  - A bridge to `infiniteTrajectoryLaw` is **not required for honesty**, provided the docstring gives the product
    formula and `pathLaw` is a genuine definition (no fallback).
  - The bridge is **recommended** (non-blocking, outside the index): `pathLaw` should equal the pushforward of
    `infiniteTrajectoryLaw M πb s₀` (`InfiniteTrajectory.lean:69`, coordinates `(a_t, s_{t+1})`) under
    `x_i = (s_i, a_i)`, using `infiniteTrajectoryLaw_prefix`.
  - The bridge shows consistency with the Ch2 model used elsewhere.
- **Module plan.** The modules and the reuse list are reasonable. The pair-chain filtration must be the one used at
  the Freedman interface, not the `traj` coordinate filtration.
  - Freedman needs `Filtration ℕ`. Saturate indices `> T` and shift by `τ`.

---

## 6. Required corrections before builders start

1. (R1) Remove the dependency of the statement file on `TVCore` (a proof-module import). Define TV in the AsyncQ
   definitions module and add the decidability or classical instances.
2. (R2) Make the index entry the printed `∃ c₁ ∃ c₂` form plus `2 ≤ T` and `0 < μ_min`. Keep `∀ c₁` in the library
   export.
3. Write `c₂ ≥ C_thr(c₁) + 1` (strict threshold) and keep `c₂ ≥ 3888` and `≥ 2586`.
4. Specify the Freedman filtration as the pair-chain `F_i = σ(X_0..X_i)` on `Fin (T+1) → S×A`, shifted by `τ` and
   saturated beyond `T`.
5. Disclosure (C34 text; the lead edits it):
   - `t_mix = 0` admits `T = 1` for every `δ`;
   - `2 ≤ T` is uniform, while the strictly weakest form is `2 ≤ T ∨ 2 ≤ SA`;
   - `μ_min > 0` is necessary for every rate;
   - `∃ c₂ ∀ c₁` is false, so `c₂ = c₂(c₁)`.

Verdict: **GO.** Statement transcription, C34 counterexamples, weakest correction, filtration argument, epoch
contraction, Lemma V (arbitrary initial law), comparator reuse and constants all survive independent re-derivation. The
draft `Prop` needs corrections (R1) and (R2) before it is committed.
