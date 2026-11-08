# CHECK: plan for Theorem 4.7 case (i) (`thm:LB-example-Q-generative`)

Public copy of the independent plan check; local paths removed. The plan checked here is the builder's private plan; it is not published.

Independent plan check, 2026-11-08. Source-only: no Lean, lake, check.py or lean-lsp was run, and nothing under
`Formalization/` was touched. Scratch scripts (`sweep.py`,
`mc.py`) are in the reviewer's private check folder. They are sanity checks only; the verdict rests on the derivations below.

## Pins

| Item | Value |
|---|---|
| Plan checked | the builder's private plan, sha256 `9dbb17a35dd669b978c4a507a737342046faac742353d16e6e5a137621882bbb` (verified, 319 lines) |
| HEAD | `58bb234219e157a6d4cec61b9786caf6b0eefb4d`, on branch `recovery-batch-thm711-smooth-20261108`. The plan names `recovery-batch-thm711-groundwork-20261108`, which is wrong (fix 6). |
| `generative_model_model_free.tex` sha256 | `7f4eb058e00480bc0694cac93ac41e22f4cfe48aa58a00c4ccf909f805e60b22` (matches the plan) |
| Source read before the plan | `:940–1100` (theorem `:969–982`, discussion `:996–1003`), Appendix C opening `:2707–2830`, scope sentence `:2711` |
| Also read | AGENTS.md; SOURCE-ISSUES C30, C31; COVERAGE row `:119`; `Statements/Ch4.lean` `Thm4_7_restricted`; `Ch4Proofs.lean`; `QLearningLowerBound{Definitions,Xi,Zeta,AuxMoments,Pathwise,Theorem}.lean` (signatures and the moment induction); `QLearningIterateBounds.lean` (`qLearningIterate`); `scripts/static_gates.py` G3; `scripts/progress_dashboard.py`; `docs/named-result-status.json` |

## Verdict: GO WITH FIXES

The mathematics holds. I tried to refute the strong reading (`c₃ = 16` and `c_lb = 10⁻⁹`, both independent of
`c_η`) and failed. Every step of Sections 3.1–3.4 re-derives, with the same or better constants. All the
required fixes are about the Lean design, the documentation and the ledger. None changes the mathematics or the
statement.

## 1. Printed statement and quantifier reading

The text at `:969–982` is: assume `3/4 ≤ γ < 1` and `T ≥ c₃/(1−γ)²` for a sufficiently large constant `c₃`,
`Q₀ ≡ 0`, and rates (i) `η_t = 1/(1+c_η(1−γ)t)` "for any constant `c_η > 0`", or (ii) `η_t ≡ η ∈ (0,1)`. Then
"there exists" a γ-discounted MDP with `S = 4` and `A = 2` such that
`max_s E|V_T(s)−V⋆(s)|² ≥ c_lb/((1−γ)⁴ T log² T)` "for some universal constant `c_lb > 0`".

- **Literal reading.** "Universal" `c_lb`, together with "any constant `c_η`", reads as `c_lb` independent of
  `c_η`. `c₃` is "sufficiently large", so on the weakest reading it could depend on `c_η`. The plan proves the
  strongest form (`c₃ = 16` universal), which implies every weaker reading. The MDP is introduced after the
  rates, so it may depend on `γ`, `T` and the schedule. The witness `qLbMDP γ` depends only on `γ`, so the
  stronger order (∃M before the schedule) also holds.
- **`c_η → 0`.** Then `D = c_η ε → 0`, `η_t ≈ 1`, and the plan is in Case C (`D ≤ 1`,
  `Σ ≈ κT ≥ (4ε/3)(16/ε²) ≫ 1/2`). Here `η_T/ε ≥ 1` once `c_η εT ≤ 1/ε − 1`, so `s = 1`, and the bound is of
  order `1/ε²`, which is far above the target. There is no degeneration.
- **`c_η → ∞`.** Then `D > 1` (Case A), and `u = (1+L)/c → 0`, so `Π_κ(0,T) → 1` and the state-2 bias is about
  `V⋆² = 9/(16ε²)`. This is far above the target. There is no degeneration.
- **Intermediate `c` (Case A, `u > 1`).** This is the only regime where uniformity is in question. It is handled
  by `ε > 1/(1+L)`, so the `L²` in the printed bound is exactly what is needed. The dependence on `L` is real but
  uniform in `c` (details below).

**Case A, re-derived.** Write `ε = 1−γ ≤ 1/4`, `κ = 4ε/3 ≤ 1/3`, `D = cε > 1`, so `c > 1/ε ≥ 4`.

1. Every factor satisfies `κη_j ≤ κ/(1+D) < 1/6 ≤ 1/3`. Since `log(1−x) ≥ −x/(1−x) ≥ −3x/2` on `[0,1/3]`, we get
   `Π_κ(0,T) ≥ exp(−(3/2) Σ κη_j)`.
2. `η_j ≤ 1/(Dj)` and `H_T ≤ 1+L`, so `Σ κη_j ≤ κ(1+L)/(cε) = 4(1+L)/(3c)`. Hence
   `Π ≥ exp(−2(1+L)/c)`. ✓
3. Bias: `V⋆ − E v_t = (1−κη_t)(V⋆ − E v_{t−1}) + (κV⋆ − 1)η_t`, and `κV⋆ = 1`, so `V⋆ − E V_T(2) = V⋆ Π_κ(0,T)`.
   By Jensen, `E(V_T(2)−V⋆)² ≥ (9/(16ε²)) e^{−4u}` with `u = (1+L)/c`.
4. The ratio to `1/(ε⁴TL²)` is `R = (9/16) ε² T L² e^{−4u}`.
   - If `u ≤ 1`: `R ≥ (9/16)·16·1·e^{−4} = 9e^{−4} ≈ 0.165`. This uses `ε²T ≥ 16` and `L ≥ 1`. ✓
   - If `u > 1`: `c < 1+L` and `c > 1/ε`, so `εL > L/(1+L) ≥ 1/2`, i.e. `ε²L² ≥ 1/4`. Since `c > 4`,
     `4(1+L)/c < 1+L`, so `e^{−4u} ≥ e^{−(1+L)} = 1/(eT)`. Then `R ≥ (9/16)(1/4)/e = 9/(64e) ≈ 0.0517`. ✓

   So `R ≥ min(9e^{−4}, 9/(64e)) = 9/(64e)`, which is far above `10⁻⁹`, uniformly in `c`.

## 2. Cases B and C

**(A3) `w_k^{(t)} ≤ η_t` when `D ≤ 1`.**

- Base: `w_t^{(t)} = η_t`.
- Step: `w_k^{(t+1)} = (1−η_{t+1}) w_k^{(t)} ≤ (1−η_{t+1})η_t`. We need `(1−η_{t+1})η_t ≤ η_{t+1}`, i.e.
  `η_t ≤ η_{t+1}/(1−η_{t+1}) = 1/(D(t+1))`, i.e. `D(t+1) ≤ 1+Dt`, i.e. `D ≤ 1`. ✓
- Hence `S₂(t) ≤ η_t Σ_k w_k^{(t)} ≤ η_t`, since `Σ_k w_k^{(t)} = 1 − Π_1(0,t) ≤ 1`.

**(A4) `S₂(t) ≥ η_t/2` when `D ≤ 1`.**

- Base: `S₂(1) = η_1² ≥ η_1/2` if and only if `η_1 = 1/(1+D) ≥ 1/2`, if and only if `D ≤ 1`. ✓ (This is the
  only place in (A4) where `D ≤ 1` enters.)
- Step: `S₂(t+1) = (1−η_{t+1})² S₂(t) + η_{t+1}²`. Since `η_t ≥ η_{t+1}`, this is
  `≥ (η_{t+1}/2)[(1−η_{t+1})² + 2η_{t+1}] = (η_{t+1}/2)(1+η_{t+1}²)`. ✓
- This is stronger than the `S₂ ≥ η̄/3` that `qLb_scalar_m2` needs, and no burn-in is needed.

**Case B** (`D ≤ 1`, `Σ ≤ 1/2`).

- `Π_κ(0,T) ≥ e^{−3/4}`, so the state-2 error is `≥ (9/(16ε²)) e^{−3/2} = (9e^{−3/2}/16) ε²T · 1/(ε⁴T)`.
- With `ε²T ≥ 16` this is `≥ 9e^{−3/2}/(ε⁴T) ≈ 2.008/(ε⁴T) ≥ 2/(ε⁴TL²)`. ✓

**Case C** (`D ≤ 1`, `Σ > 1/2`).

1. **Bound on `c`.** `Σ_{j=2}^T η_j ≤ (H_T − 1)/D ≤ L/(cε)`, so `Σ ≤ κη_1 + 4L/(3c) ≤ 1/3 + 4L/(3c)`.
   `Σ > 1/2` then forces `4L/(3c) > 1/6`, i.e. `c < 8L`. ✓
2. **Product.** `Σ_{j≥2} κη_j > 1/2 − 1/3 = 1/6`. With `1−x ≤ 1/(1+x)` and `∏(1+x_j) ≥ 1+Σx_j`, this gives
   `Π_κ(1,T) ≤ 6/7`. ✓
3. **Decomposition (P5) and (P6).**
   - `Q̂_t(a) − V⋆ = (1−η_t)(Q̂_{t−1}(a) − V⋆) + η_tγ[(P_t−p)V̂_{t−1} + p(V̂_{t−1}−V⋆)]`, using `1 − V⋆ = −γpV⋆`. ✓
   - `E C_t = (1−η_t)e_{t−1} + η_tγp(e_{t−1} + m_{t−1}) = (1−κη_t)e_{t−1} + η_tγp m_{t−1}`. ✓
   - `m_t ≥ max_a E ξ_t(a) = 0`. ✓
4. **Induction.** The claim is `e_t ≥ (γpb/κ)(1−Π_κ(1,t))` for `1 ≤ t ≤ T`.
   - Base: `Π_κ(1,1)` is an empty product, so it equals 1 and the right side is 0. Also
     `e_1 = (1−κη_1)·0 + η_1γp·m_0 = 0`. ✓
   - Step (`t ≥ 1`, so `m_t ≥ b`, and `1−κη ≥ 0`):
     `e_{t+1} ≥ (γpb/κ)[(1−κη_{t+1})(1−Π(1,t)) + κη_{t+1}] = (γpb/κ)(1 − (1−κη_{t+1})Π(1,t)) = (γpb/κ)(1−Π(1,t+1))`. ✓
   - Only `m_1, …, m_{T−1}` are used, so (M) is needed only for `1 ≤ k ≤ T−1 ≤ N = T`.
5. **Lower bound on `e_T`.** `γp/κ = (4γ−1)/(4ε) ≥ 1/(2ε)`, so `e_T ≥ b/(14ε) = 5s/(21504ε)`. ✓
6. **Coupling (P1), re-derived.**
   - Base: `G_0 = 1/ε ≥ V⋆ = Q̂_0 − Q_0`.
   - Step: `Q_t − Q̂_t ≥ −(1−η_t)G_{t−1} − η_tγP_tG_{t−1} ≥ −(1−εη_t)G_{t−1} = −G_t`. This needs
     `η_t ∈ [0,1]` and `P_t ∈ {0,1}`. ✓
   - `G_T = V⋆(3) − V_T(3)` is deterministic. So
     `E[V_T(1) − V⋆] + G_T ≥ E V̂_T − V⋆ = e_T + m_T ≥ e_T`. One of the two terms is `≥ e_T/2`, and then
     `max_s E(·)² ≥ (e_T/2)² = 25s²/(43008² ε²)`. ✓
7. **`η_T/ε` and the final constant.** `εTL ≥ 64` gives `1 + cεT < 1 + 8εTL ≤ 9εTL`. So
   `η_T/ε ≥ 1/(9ε²TL)`, and this is `≤ 1/144 ≤ 1`, so `s² ≥ 1/(9ε²TL)`. The bound is
   `≥ 25/(9·43008²) · 1/(ε⁴TL) = 1.5017·10⁻⁹/(ε⁴TL) ≥ 1.5·10⁻⁹/(ε⁴TL²)`. ✓
   (`43008² = 1 849 688 064`.)

**Exhaustiveness.** Case A (`D > 1`), Case B (`D ≤ 1`, `Σ ≤ 1/2`) and Case C (`D ≤ 1`, `Σ > 1/2`) cover every
case.

**Scratch sanity (not evidence).**

- `sweep.py` asserts every inequality above for `ε ∈ {1/4, …, 1/200}`, `T ∈ {T₀, 4T₀, 30T₀}` with
  `T₀ = ⌈16/ε²⌉`, and `c ∈ [10⁻⁶, 10⁸]` including `c = 1/ε` exactly. No assertion failed. The minimum of
  (proved lower bound)/(target) is 828 in Case C and more than 10⁹ in Cases A and B.
- `mc.py`, Monte Carlo with 600 runs, gives `max_s MSE·ε⁴TL²` between 1.04 and 857 over 7 configurations,
  including `D = 1`, `c = 0.01` and `c = 1000`.

## 3. Do the case (ii) moment lemmas transfer?

**Mathematically, yes.** The moment route uses exactly these ingredients:

- deterministic weights `0 ≤ w_k ≤ η̄` (used in `t2` of `qLb_zeta_moment_bounds` via `w² ≤ η²`);
- `η̄/3 ≤ S₂ ≤ η̄` (the inputs to `qLb_scalar_m2` and `qLb_scalar_m4`);
- `0 ≤ V̂ ≤ h` and `E V̂ ≥ V⋆`;
- the martingale facts `E D = E D³ = 0` and `E D² = E D⁴ = 2p(1−p)`, with `D_{n+1}` independent of the past.

None of these uses a constant `η` beyond the weight bound, and that bound is replaced by (A3). The closed form
`qLb_weight_sq_sum` and the burn-in `(1−η)^{2t} ≤ 1/3` are used only to get `S₂ ∈ [η/3, η]`, and (A3) and (A4)
replace them.

The source's `p(V̂ − V⋆)` drift is absorbed into `C_t`. `ξ` is driven only by the centred draws, so
`E ξ_t(a) = 0` still holds with time-varying deterministic weights.

**Structurally, more is rate-specific than the plan's reuse table suggests.** These declarations are tied to
`qLbAuxValue γ η` with a constant `η`, or to the weight `η(1−η)^{t−k}`. They cannot be reused and must be
re-proved for `qLbv*`:

- `qLbZetaPartial`, `qLbXi_sub`, `qLbZetaPartial_succ`, `qLbZetaPartial_congr`, `qLb_zeta_sq_succ`,
  `qLb_zeta_four_succ`;
- `qLbAuxIterate_bounds`, `qLbAuxValue_bounds`, `qLbAuxIterate_congr`, `qLbAuxValue_congr`,
  `qLb_auxIterate_integral_ge`, `qLb_auxValue_integral_ge`;
- `qLb_integral_xi`, `qLb_integral_xiMax`;
- `qLb_zeta_moment_bounds`, `qLb_xiMax_lower`, `qLb_pathwise`, `qLb_state2_mean`.

These are genuinely reusable:

- `qLb_sq_le_abs_quartic`, `qLb_scalar_step4`, `qLb_scalar_m2`, `qLb_scalar_m4`, `qLb_scalar_final`;
- `qLb_integral_mul_state1`, `qLb_integral_mul_centered`, `qLb_integral_mul_Dpow`, `qLb_integral_D(_sq)`;
- `qLbD*`, `qLbAgree1/2`, `qLb_agree1_of_past`, `qLb_integral_state1/2`, `qLb_max_eq`;
- the product-law file, `qLbMDP_*` values, `qLbValid`, `qLbMDP_next`, `qLb_valid_ae`, `qLb_T_facts` (whose
  `16` hard-codes `c₃ = 16`, which suits the plan).

`qLb_caseA_scalar` is constant-rate specific. It can serve only as a pattern.

## 4. Combined entry `Thm4_7`

- **Faithfulness.** The disjunctive hypothesis, with `∃ cη > 0, ∀ t, η t = 1/(1+cη(1−γ)t)` or
  `∃ η₀ ∈ (0,1), ∀ t, η t = η₀`, quantified after `γ` and `T`, matches "either (i) … or (ii)". `c_η` and `η₀` may
  depend on `γ` and `T`, which is at least as strong as "any constant". `η 0` is constrained (to 1, or to `η₀`)
  exactly as printed ("for all `t ≥ 0`"), and `qLearningIterate` never reads it, because step `t+1` uses
  `η (t+1)`. So this is harmless.
- **Combining constants.**
  - From `max(c₃ᵢ)/(1−γ)² ≤ T` we get each `c₃ᵢ/(1−γ)² ≤ T`.
  - `min(c_lbᵢ)/X ≤ c_lbᵢ/X` holds for `X = (1−γ)⁴T log²T ≥ 0`, which is always true, so even Lean's
    `x/0 = 0` cannot break it.
  - With both exports at 16, `c₃ = 16`, and `c_lb = min(e^{−16}, 10⁻⁹) = 10⁻⁹`, since `e^{−16} ≈ 1.1·10⁻⁷`. ✓
- **Restrictions carried from `Thm4_7_restricted`.** Its only restriction is "case (ii) only". Its other items
  are encodings, not restrictions:
  - dominated dummy actions (C31(5)), which give an honest 4-state, 2-action MDP;
  - `∃ s` for the max over the finite state set;
  - `V⋆` taken as the trajectory value of the optimal greedy policy;
  - natural log and `T : ℕ`.

  C31's items change only the unnamed constants or the proof, and the export does not assume the
  `eq:logT_ub` WLOG. So a suffix-free `Thm4_7` is correct, provided those encoding disclosures are copied into its
  docstring (fix 2).
- **C30.** C30 can be closed as "the source omits the argument for case (i), deferring it to li2024q. The printed
  statement is true with universal constants, and a self-contained formal proof is supplied." No `_corrected`
  suffix is needed. Keep C30 as a recorded gap ("proof outside the monograph"), as is done for C34 and C35; do not
  delete it.
- **Harmonic sums and log base.** These are internal to the proof, and the statement needs no disclosure for them.

## 5. Lean design

- Parallel `qLbv*` definitions are the right call, because generalising in place would change proved
  signatures.
- Strongly recommended: define `qLbvZetaPartial` with an abstract weight function (`w : ℕ → ℝ`), and prove the
  moment recursions and the induction once for any `w` with `0 ≤ w k ≤ η̄`. This avoids proving
  products-of-schedule algebra inside the probabilistic file.
- **Size.** The existing case-(ii) tree is 2,383 lines. With the re-proof list in Section 3, I estimate
  1.8k–2.6k lines, not 1.4k–2.0k. Re-proving Zeta, the rate-specific parts of AuxMoments, the moment induction
  and Pathwise alone comes to about 700–800 lines, before rates, Cases A, B and C, and the assembly. This is
  feasible, and the overrun is not a blocker.

## Required fixes

1. **Reuse table.** Mark every declaration in the first list of Section 3 as re-proved for `qLbv*`, not reused.
   Re-estimate file 4 at 450–650 lines and the total at 1.8k–2.6k.
2. **`Thm4_7` docstring.**
   - Copy the encoding disclosures of `Thm4_7_restricted`: dummy actions (C31(5)), `∃ s` for the max, the `V⋆`
     convention, natural log, `T : ℕ`, the Algorithm `alg:q-infinite` sampling law, `Q₀ ≡ 0`.
   - State that `c_η` and `η₀` are quantified after `γ` and `T`, and that `η 0` is unused.
   - Cite C30 and C31, which are both existing anchors, so gate G3(d) passes.
   - Keep the `.tex:969–982` range so that G3(a) passes.
3. **(M) and the moment induction.** State them for `1 ≤ t ≤ N`, and run the `n`-induction for `n ≤ t`. Take
   the weight bound `w ≤ η̄` and `η̄/2 ≤ S₂ ≤ η̄` (or `/3`) as hypotheses on an abstract weight, and discharge
   them from (A3) and (A4) with `D ≤ 1`.
4. **Ledger.**
   - Replace the `proved_variants` record "Theorem 4.7, case (ii) (restricted variant)" in
     `docs/named-result-status.json` with a `certified_named_results` record for
     `StatisticalRL.Statements.Ch4.Thm4_7` (`_holds`), whose `lean_export` lists both exports.
   - Either delete `Thm4_7_restricted` and its `_holds` from the index, or keep it with its docstring changed to
     "implied by `Thm4_7`; retained for history". It must not keep a ledger record of its own.
   - Update the COVERAGE row `:119`, PROGRESS (ownership and ledger count) and C30 together, in the same change,
     after the critic review.
5. **Case C, step 7, in the build.** Prove `1 ≤ εTL` explicitly. It follows from `εT ≥ 16/ε ≥ 64` and `L ≥ 1`,
   and the plan uses it silently.
6. **Pin.** Correct the branch name in Section 0 to `recovery-batch-thm711-smooth-20261108` (HEAD `58bb234`).

## Answers to the plan's open questions

1. **Case A.** Correct. `R ≥ min(9e⁻⁴, 9/(64e)) = 9/(64e) ≈ 0.0517`.
   - `ε²L² ≥ 1/4` follows from `ε > 1/c > 1/(1+L)` and `L ≥ 1`.
   - `exp(−4(1+L)/c) ≥ 1/(eT)` follows from `c > 4`.
   - The uniformity in `c_η` is real. The `L` dependence is uniform in `c` and is absorbed by the printed `log²T`.
2. **(A3) and (A4).** Correct, and both need exactly `D ≤ 1`: (A3) through `D(t+1) ≤ 1+Dt`, and (A4) through its
   base case `η_1 = 1/(1+D) ≥ 1/2`. The moment route needs only `0 ≤ w ≤ η̄`, `S₂ ∈ [η̄/3, η̄]`, `0 ≤ V̂ ≤ 1/ε` and
   `E V̂ ≥ V⋆` (which gives `E V̂² ≥ V⋆²`). The fourth-moment step uses `w² ≤ η̄²` together with `γ² ≤ 1`.
3. **Case C, step 4.** Correct. In the base case `Π_κ(1,1) = 1` and `e_1 = 0` because `m_0 = 0`. The step
   identity `(1−κη)(1−Π(1,t)) + κη = 1 − Π(1,t+1)` holds.
4. **`c < 8L`.** Correct, using `κη_1 ≤ κ ≤ 1/3` and `Σ_{j≥2} η_j ≤ (H_T−1)/(cε) ≤ L/(cε)`.
5. **Quantifier reading.** The strong reading is the literal one. The combined disjunctive entry matches the
   printed sentence, and `η 0` is harmless (see Section 4).
6. **Retiring C30.** Yes, with no suffix. Record C30 as resolved ("source argument omitted; printed statement true
   with universal constants; formal proof supplied"). Do not delete it.
7. **Tooling.** There is no gate conflict. G3 requires exactly one `X_holds` per entry and a unique ledger
   `lean_statement` per record, and it does not require every entry to have a ledger record. The dashboard counts
   unique source IDs, but `corrected_variant_count` would double-count if the restricted record stays. Hence
   fix 4.
