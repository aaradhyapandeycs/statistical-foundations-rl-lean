# CHECK — Theorem 6.17 `thm:lcbq` plan (independent critic, source only, no Lean)

Public copy of the independent critic report; local paths removed.

Reviewed: the builder's private plan (UNREVIEWED) and `<builder plan folder>/cex_check.py`.
Source: `source/upstream/tex/chapters/offlineRL.tex`, sha256 `67cf0d1ce6a3d7c6cc43aedb371c692a3da0508193d735609713b03c0186f1e4`
(matches provenance). No Lean, lake or lean-lsp was run. The cited paper (shi2022pessimistic) was not consulted.
My own script is `<reviewer check folder>/check.py` (`python3 -I check.py`, stdlib, about 4 s). Its
output is in `check.out`. I wrote no other files.

## 0. My reconstruction from the source, done before reading the plan

- **Setting** (`:2943–3007`). There are K iid trajectories `s_1~ρ^b`, `a_h~π^b_h`, `s_{h+1}~P_h`. Rewards are known
  and lie in `[0,1]` (`prelim.tex:682`). `C⋆ = max d⋆_h(s,a;ρ)/d^b_h(s,a)` with `0/0 = 0`. The text does not say
  which optimal policy defines `d⋆`. The goal is `V⋆_1(ρ) − V^{π̂}_1(ρ) ≤ ε` for `ε ∈ (0,H]`.
- **What the prose fixes** (`:3132–3148`):
  - single pass over k = 1..K;
  - at each step h, one update at `(s_h^k,a_h^k)` using `s_{h+1}^k`;
  - the update `Q ← (1−η_n)Q + η_n(r + V_{h+1}(s') − b_n)`, where n is the per-(h,s,a) visit count;
  - `η_n = (H+1)/(H+n)`, called "a common choice";
  - `b_n = Θ̃(√(H³/n))`, introduced with "for instance";
  - **output "π̂ obtained by acting greedily with respect to the Q-function estimate Q^lcb"** (`:3145`).
- **What the prose leaves open**:
  - the initialisation;
  - the V update (never written);
  - the tie rule;
  - the stage order within an episode;
  - the constant and log power inside Θ̃.
  The box `:3150–3173` is commented out, marked `\yc{to update}`, and is a VI-LCB copy (backward h, model-based). It
  carries no authority beyond `V_{H+1} = 0`.
- **Theorem** (`:3176–3192`). For all `δ ∈ (0,1)`, `ε ∈ (0,H]` and ρ, with probability at least 1−δ the output
  satisfies gap ≤ ε, provided `K ≥ c_a H⁵ S C⋆ log³(SAK/δ)/ε²` for some sufficiently large numerical `c_a`. No proof is
  given anywhere. The infinite-horizon analogue `alg:q-infinite-lcb` (`:1700–1748`) fixes zero init, monotone V and
  the strict-increase policy rule. Its remark `:1696` says that rule is "adopted primarily to facilitate the
  analysis; other choices may also be used".

## 1. Claim (1): transcription and U1–U6

**Verdict: CONFIRMED, with one correction.**
- Locators, the formula, the rate, the "at least 1−δ" wording and the label warning (`thm:lcbq` vs `theorem:lcbq`)
  all match the source.
- U1, U2, U4, U5 and U6 are genuinely unspecified.
- U6 is correct and matters. Under backward order, the stage-(h+1) update in episode k rewrites `V_{h+1}(s_{h+1}^k)`,
  which is exactly the entry that stage h then reads. The martingale step then breaks. Under forward order, stage h
  reads `V_{h+1}^{k−1}`.

**Correction (U3).** The output is *not* unspecified. `:3145` fixes it as greedy with respect to Q^lcb, most
literally the final Q. Only the tie rule is open. The plan's strict-increase rule from `alg:q-infinite-lcb` gives
`π̂_h(s) = argmax Q_h^{k'}(s,·)` at the last strict V-increase k′, which is generally not greedy for the final Q.
- In Step 3 the pessimism chain needs this rule, because Q can decrease while monotone V does not.
- Importing the rule is defensible, given remark `:1696` and the explicit infinite-horizon algorithm. It is still a
  departure from the literal `:3145` reading and must be disclosed as such. It is not merely "U3 filled".
- The plan's own "open obligations" already list final-greedy (T1), so this is a disclosure fix, not a proof gap.
- My small random-MDP simulation (§5 of `check.out`, S = 3, A = 2, H = 3, K = 4000) shows near-identical gaps for
  final-greedy and strict-increase, and for forward and backward order. This is weak evidence only; there is no
  counterexample and no proof.

## 2. Claim (2): the C33 counterexample family

**Verdict: CONFIRMED (re-derived and re-checked independently).**

Re-derivation. Take `H = S = 1`, `r = (1, 1/2)`, `π^b(a⋆) = p`, `ε = 1/4`, `C⋆ = 1/p` and
`b_n = c_b ι^a/√n`.
- `η_1 = 1` and the weights sum to 1, so `Q(a) = r(a) − β(N_a)` exactly, with `b_N ≤ β(N) ≤ 2b_N` and β decreasing.
  My check covers n ≤ 600 and H ∈ {1,2,5,10}.
- Take `p = c_a/(4c_b²ι^{2a−3})`, `K = ⌈16c_aι³/p⌉ ≈ 64c_b²ι^{2a}` and `δ = 2Ke^{−ι}`. Then `log(SAK/δ) = ι` and the
  printed condition holds.
- On `{N⋆ ≤ 2pK}`, which has probability `≥ 1 − e^{−pK/3}` by Chernoff, every visited
  `Q(a⋆) ≤ 1 − c_bι^{a−3/2}/√(32c_a)`. Meanwhile `Q(a₂) ≥ 1/2 − 2c_bι^a/√(K/2) ≈ 1/2 − 0.354 > 0`.
- Every strict V-increase therefore selects a₂ strictly, and so does the final-greedy rule. The gap is 1/2 > ε, with
  probability ≈ 1 > δ.

Numerical check:
- My own grid is `a ∈ {1.6, 2, 3}`, `c_a ∈ {1, 10², 10⁴, 10⁶}` and `c_b ∈ {0.25, 1, 10, 10³}`, with my own ι search.
  All 48 points give valid counterexamples. For a = 1.6 with tiny `c_b/√c_a`, ι is astronomically large, but it is
  finite.
- The literal simulation gives the wrong arm 6/6 times under the strict-increase rule and 12/12 under final-greedy
  for a = 2. It gives 0 wrong for a = 1 and for a = 1/2.
- At a = 3/2 the bias is `c_b/√(32c_a)`, independent of ι. The mechanism needs `c_a < c_b²/32`.
- The threshold is sharp up to constants. With `L = Mι³` the bias scales as `√M`, so no fixed `c_a` covers unbounded
  M.

**Classification (my decision).** The printed statement is **under-specified, not false**:
- "The algorithm with the Θ̃ penalty" does not denote a single algorithm.
- The universal reading ("every Θ̃(√(H³/n)) penalty works") is **false**, refuted for every log power above 3/2.
- The existential reading ("some Θ̃ penalty works") is **true**, by the plan's §4 for L ∈ [ι, ι³].
- C33 should say exactly this. It should not say "the statement is false". It also needs its threshold sharpened:
  - the current text reads "Θ̃ hides ι² or more" (that is, an outside factor ι², L = ι⁴);
  - the sharp version is "outside factor ι^a with a > 3/2, i.e. L = ι^{2a} > ι³, for every c_a";
  - at L = ι³ the outcome depends on `c_a` versus `c_b²`.
  State it in terms of L (the power inside the square root) to avoid the current ι vs ι² ambiguity. C33's own note
  that the counterexample was "not yet independently re-derived" can now be discharged by citing this check.

## 3. Claim (3): explicit variant, name and L range

**Verdict: ACCEPT with disclosures.**

- Zero init, arbitrary deterministic π₀, `V_{H+1} = 0`, `η_n = (H+1)/(H+n)`, monotone V and the Q-row selector all
  come from `alg:q-infinite-lcb` or the prose. Forward order is the natural reading of `:3132`. Final-policy output
  is natural. Each choice is a least-committal or analysis-required completion.
- The strict-increase rule is the one choice that contradicts a literal reading (`:3145`). See §1. The name
  `Thm6_17_restricted` is honest *only if* the docstring and C33 state four things:
  - (i) the output rule is the strict-increase rule of `alg:q-infinite-lcb`, not final-greedy;
  - (ii) the stage order is forward;
  - (iii) the penalty is restricted to `c_b√(H³L/n)`, `ι ≤ L ≤ ι³`;
  - (iv) the universal Θ̃ reading is false (C33).
  `_corrected` is not needed, because the printed hypotheses and conclusion are kept.
- **The L range is legitimate and hides no choice.**
  - L is universally quantified, and `c_a = 10⁶c_b²` is uniform in L. The entry is therefore stronger than fixing
    any one penalty.
  - It covers log arguments like `log(SAKH/δ) ∈ [ι, 2ι]`.
  - The upper end ι³ is the maximal polylog range admitting a uniform `c_a(c_b)` (§2).
  - **Wording correction:** the plan says this is "exactly the range on which the printed statement can hold". Only
    the upper end is established. Nothing shows that L < ι fails; it is merely not proved, because pessimism needs
    `ι₁ ≤ c_b²L`. Reword this as "the upper end is sharp; the lower end is what the proof needs".
- The quantifier shape `∃c_b₀ ∀c_b ≥ c_b₀ ∃c_a` is stronger than the existential printed reading. That is fine.
- Disclose that `d⋆` uses a deterministic Q⋆-greedy π⋆, quantified universally as in prior entries. A stochastic
  optimal policy can have a smaller C⋆, so this is a mild restriction of Definition `assumption:concentrate-finite`.
- `0 < K` and `C⋆ ≠ ⊤` are domain or junk-value guards, not restrictions.
- Rewards in [0,1] are carried by `EnvironmentStage` (`Formalization/MDP/EnvironmentDefinitions.lean:14–15`).

## 4. Claim (4): paper proof

**Verdict: SOUND. I re-derived every step and found no gap.**

- **Step 0.**
  - `C⋆ ≥ 1` holds, given `C⋆ < ∞`.
  - The corner holds: `SAK < e·δ` forces S = 1, A = 2, K = 1, and then `1 ≥ c_a ι > 1`.
  - `H ≤ K` holds.
  - `ι₁, ι₂, ι₃ ≤ log 6 + log K + ι ≤ 4ι` for ι ≥ 1. This uses `log K ≤ ι` and `H ≤ K`.
- **Step 1.** (i)–(v) hold.
  - Forward order gives stage parallelism.
  - `V ∈ [0, H−h+1]` by induction, because the Q-target is ≤ r + V.
  - In the unrolling, `η_1 = 1` kills the initial term.
- **Step 2.**
  - Lemma G is the standard tower or exponential-supermartingale argument on the product space. Here
    `N^{k−1}` and `V^{k−1}` are functions of `x_{<k}`, and conditionally on `(s_h^k,a_h^k)` the next state
    `s_{h+1}^k` has law `P_h`.
  - **E1:**
    - Hoeffding gives `e^{λ²ω²H²/8}`;
    - `Σ ω² ≤ 2H/n`;
    - the optimum at `λ = 2nt/H³` gives `exp(−nt²/H³)`;
    - `t = √(H³ι₁/n)`;
    - there are 2HSAK events, each with failure probability `δ/(6HSAK)`;
    - `√(H³ι₁/n) ≤ b_n ≤ β(n)` needs `c_b² ≥ 4 ≥ ι₁/L`, which holds.
  - **M1:**
    - `E Z = a_k` and `E Z² ≤ C⋆H a_k`;
    - `e^{−x} ≤ 1−x+x²/2`;
    - with `λ = 1/(C⋆H²)` the factor is `1 − 1/(2H)`;
    - `(1 − 1/(2H))^{−1} ≤ 1 + 1/H`.
  - **M2:**
    - `λZ ≤ 1/H ≤ 1`;
    - `e^x ≤ 1+x+x²`;
    - the factor is `1 + 1/H`.
  - **Cnt:** `E e^X ≤ e^{(e−1)d^b}` and `e − 1 ≤ 2`. The per-trajectory indicators are iid.
  - The total failure probability is `δ/3 + δ/3 + δ/3`.
  - Clipping `f^k = min(D^+, H)` makes the predictable functions bounded with no gate.
- **Step 3.**
  - On E1 (lower side), `Q_h^k ≤ r + Σ η P V^{k_i−1} ≤ r + P V^k_{h+1}` by monotonicity. For n = 0, `Q = 0 ≤ r + PV`.
  - At a strict increase, `V = Q(s, sel) ≤ r(s,π̂) + P V^k_{h+1}`. Otherwise V and π̂ are frozen and the right-hand
    side grows.
  - Backward induction gives `V^K ≤ V^{π̂}`.
  - Finally `Δ^K ≤ Δ^{k−1}` gives `gap ≤ G_1/K`.
- **Step 4.**
  - (a): `Δ ≤ D(·,π⋆)` and `Δ ≤ H`.
  - (b): `D^{(n)} = Σ η P Δ^{k_i−1} + Σ η(PV − V(s′)) + Σ η b`, which is ≤ via the upper side of E1.
  - (c): the regroup over counts 0..N−1 is correct. The tail is `Σ_{n≥i} η_i^n ≤ 1+1/H` (checked numerically). Also
    `Σ 2β ≤ Σ 4b_n ≤ 8c_b√(H³LN)`.
  - (d): `Σ w ≤ SC⋆`, `w√(2Kd^b) ≤ √(2KC⋆d⋆)` and `Σ√d⋆ ≤ √S`.
  - (e): `G_h ≤ (1+1/H)³G_{h+1} + R`, with coefficients 2, 2 + 4 = 6 and 16 (using 1 + 1/H ≤ 2).
  - (f): `(1+1/H)^{3H} ≤ e³ < 21`.
- **Step 5.** I recomputed the four terms (42, 504, 336√2 ≈ 475.2, 672). The total coefficient is 0.4756 at c_b = 2
  and decreases toward 0.47518. So it is `< 0.48ε`, and therefore ≤ ε.
- **The printed rate `H⁵SC⋆log³(SAK/δ)/ε²` follows.** The export only needs `K ≥ c_aH⁵SC⋆L/ε²`, and `L ≤ ι³` turns
  that into the printed condition. Per AGENTS.md this is not a discrepancy.

Minor proof-writing notes for the builder:
- In E1, state the per-(h,s,a,n) event as concerning the *first n visits*, so that it can be reused at every k with
  `N^k = n`.
- In M1, f^k is defined on all (s,a). Only `a = π⋆_h(s)` carries `d⋆` mass, but the bound `E Z² ≤ C⋆H a_k` is fine
  as written.

## 5. Required corrections before or with the build

1. **Disclose the output rule (§1, §3).** The strict-increase rule departs from the literal `:3145` "greedy w.r.t.
   Q^lcb". Put this in the `Thm6_17_restricted` docstring and C33. Keep final-greedy and backward order as open
   obligations.
2. **Update the C33 classification** to: "under-specified; the universal Θ̃ reading is false for L = ι^{2a}, a > 3/2,
   for every c_a; a = 3/2 needs `c_a ≳ c_b²`; true for L ∈ [ι, ι³] (proof route reviewed)". Remove "the statement is
   false" wording and the unsharp "ι² or more".
3. **Reword the plan's L-range claim** as "upper end sharp, lower end proof-driven".
4. **Disclose the deterministic π⋆ in C⋆.**
5. **Run the usual statement audit** of the Lean `Thm6_17_restricted` before proofs. Check that
   `LCBQFinite.output` is defined literally as the forward fold, and prove `run_episode_parallel` as a lemma.

## 6. Go / no-go

**GO** for a Lean build of the explicit variant and `Thm6_17_restricted`, conditional on corrections 1–4 being
recorded (documentation only; no mathematical change) and on the pre-proof statement audit (5). The proof plan
(Steps 0–5) has no gap that I could find. The C33 counterexample is independently confirmed.
