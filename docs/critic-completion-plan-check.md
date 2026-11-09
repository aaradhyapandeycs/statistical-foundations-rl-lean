# Completion plan check (independent plan critic, 2026-11-09)

Public copy, scrubbed. The plan it reviews is an internal planning document and is not published; its item
numbers (#1–#39, U1–U23) and batch names (P1, P2, P3a, P3b, T) are quoted here as in the plan. The original
section 7 (worker briefs) is omitted. In this check "C1–C7" in section 3 number its **category corrections**;
they are not source-issue ids (those link to `SOURCE-ISSUES.md#Cnn`). Category correction: the check's P:66
locator for the time-invariant-policies sentence is line 76 of `chapters/prelim.tex`.

Date: 2026-11-09. Read-only critic. Branch `recovery-batch-fhlb-thm39-sb2a-20261108`, HEAD `c0d94c4`
(dirty tree). No Lean, lake, git change, download or repo edit other than this file.
Every category below was re-decided from the TeX under `source/upstream/tex/chapters/` and from the
current statement files, not from the plan's tables. Nothing here certifies a proof.

Source hashes re-checked (sha256 prefix): intro `6bfa41c0bcb9`, prelim `2d27bb720d49`, MB `b7e7abfb2c2c`,
MF `7f4eb058e004`, bandits `d31856ba43a2`, onlineRL `393a4d26c228`, offlineRL `67cf0d1ce6a3`,
robust `95ce19a9bcdb`, marl `8fadfab2c41e`, fed `c9df1d9f6187`, inference `82707713adb6`, RLHF `e60115c355d4`.
All match the plan.

**Provenance discrepancy (fix P-0).** The plan pins `docs/NEXT.md` at `e079aa355c12` and `docs/COVERAGE.md`
at `ceee3766b792`. The files on disk hash to `d2bf1010fff1` and `e0168d7b1991`
(`gen_nodes.py --check`: current). The 39 NEXT items are the same list, so no item is lost, but the plan
must re-pin both hashes before builders start.

All 40+ Lean names the plan cites exist (grep for `theorem|def <name>`), including
`not_eq_Vk_Itrue_printed`, `onlineActualT6UCB_le_policy_difference`, `log_gibbs_div`, `optCalValue_eq`,
`drviIterate_error`, `exists_stationary_trajectory_optimal`, `event_sq_gap_le_klDiv`.

---

## 1. Verdicts

| Batch | Verdict | Blocking fixes |
|---|---|---|
| P1 (Ch1–2) | **GO WITH FIXES** | F-P1-1 … F-P1-7 |
| P2 (Ch3–5) | **GO WITH FIXES** | F-P2-1 … F-P2-8 (Remark 5.9 proof route is wrong as written; ice-cream premise misread) |
| P3a (Ch7 robust/RLHF) | **GO WITH FIXES** | F-P3a-1 … F-P3a-5 (U14 as sketched would be near-vacuous) |
| P3b (Ch7 MARL/inference) | **GO WITH FIXES** (start after C/D land, as planned) | F-P3b-1 … F-P3b-3 |
| T (tooling/docs) | **GO WITH FIXES** | F-T-1 … F-T-7 (status semantics; no out-of-scope rows without a user decision) |

Corrections: **7 category corrections** (§3) and **32 required fixes** (§5: P1 7, P2 8, P3a 5, P3b 3,
T 7, plan-wide 2), 39 in total.

---

## 2. Per-item category review

### 2.1 The 39 NEXT items

| # | Item | Plan | Critic | Notes |
|---|---|---|---|---|
| 1 | `eq:defn-Vpi-inf` P:96–109 | P | **P ✓** | The table promises "equals the Bellman fixed point", but the sketch omits it. Either drop it from the table or add the conjunct. `V^π(ρ)` is a definition (N). |
| 2 | `eq:defn-Qpi-inf-horizon` + U2 | P | **P ✓** | Q bounds are not printed (stronger). Fine. |
| 3 | `eq:defn-dpi-occupancy…` + U7 | P | **P ✓** | The normalization claim at P:158 is the real content. The sketch quantifies U7 over every deterministic `f`, which is correct. |
| 4 | `eq:bellman_consistency-V` + U3 | P | **P ✓** | Uniqueness is printed only for the Q equation (P:209). Correct as sketched. |
| 5–7 | `eq:dh-pi-defn`, `eqn:defn-d1rho-finite`, `eq:dhstar-finite` | P | **P ✓, sketch fix** | See F-P1-3: the d⋆ indicator holds for *every deterministic* policy. Do not restrict it to greedy stages. |
| 8–9 | `eq:Bellman-finite-pi/opt` + U8 | P | **P ✓, sketch fix** | See F-P1-3: Q⋆ := Q^{π⋆} for an *arbitrary* optimal deterministic π⋆ (P:739–744). |
| 10 | Remark 2.1 | N | **N ✓** | "Generally loses log M" is qualitative. |
| 11 | `eqn:ice-cream` | P | **P ✓, sketch fix** | Wrong premise; see F-P2-2. |
| 12 | Remark 3.1 | N | **N ✓** | |
| 13 | Remark 3.2 | N | **N ✓** | |
| 14 | Remark 4.4 | I | **I ✓** | `Lemma4_15` has the conjunct `∃ τ, ρ^{T+1−τ} ≤ 6/7 ∧ maximal` in Lemma 4.15's regime. The "implied" row must name that regime. |
| 15 | Remark 4.5 | I+N | **Correction C2** | Sentence 3 is not purely explanatory. "leading respectively to (1−γ)⁻³ and (1−γ)⁻⁴" asserts rates. The A ≥ 2 side is `Thm4_6` (upper) and `Thm4_7`/`Thm4_7_case_i` (lower). The A = 1 side holds only through the identity "Q-learning with one action = TD" (O4), which is not formalized. Keep the node **partial** with the headline "sentences 1–2 proved (`Remark4_5`); sentence 3: rates are `Thm4_1`/`Thm4_6`/`Thm4_7`; the A=1 ↔ TD identification (O4) is not formalized". It may become implied only after O4. Recommend promoting O4 (150–300 lines) into P2. |
| 16 | Remark 5.1 | O | **O ✓** | Cited; no statement given. |
| 17 | Remark 5.2 | N | **N ✓** | |
| 18 | Remark 5.3 | O | **O ✓, rationale fix** | See C5. |
| 19 | Remark 5.4 | N | **N ✓** | |
| 20 | Remark 5.6 | I | **I ✓ (corrected)** | The W₃ bound is the third conjunct of `Lemma5_7_K2_corrected` (K ≥ 2, C8, C12). The row must say "implied by the corrected entry" (F-T-3). |
| 21 | Remark 5.7 | N | **N ✓** | |
| 22 | Remark 5.8 | I+N | **I+N ✓ (corrected)** | T₆^low ≲ KH² is the simplified clause of `Lemma5_9_K2_corrected`, under the printed large-K condition. "≈" and "crucial for asymptotic optimality" are heuristic. |
| 23 | Remark 5.10 | I | **I ✓ (corrected)** | `Lemma5_14_corrected` has the `max (err h k) 0` and `errSq` conjuncts (verified in Ch5.lean:816ff). |
| 24 | Remark 5.11 | N | **N ✓** | |
| 25 | Remark 5.13 | P | **P ✓** | Identification verified against ON:879–893 and W1Definitions/T3Definitions: T₆^ucb = `onlineActualT6UCB` (Var of the optimistic continuation), T₆^low = `onlineActualT6Policy` (Var of V^{π^k}), T₆^diff = `onlineActualT6Difference` (⟨P,(V^k−V^{π^k})²⟩). The export is deterministic and hypothesis-free. The `_corrected` suffix is justified by C8 (the objects exist only under the zero-count completion). The docstring must cite C8. |
| 26 | `eq:Vk-Itrue` | P (optional) | **Correction C6: optional / K** | Printed form refuted with C17 recorded, and the corrected coupling is consumed by `MVP_regret_corrected`. The node is already honest. An entry needs defs from proof-heavy Decoupling modules (`OnlineMVPActualEpisodeFixedProfile`, `…FutureCode`, `…ActualStage`, `…ZeroTerminal`, `SourceOptimism/AdaptiveHistoryMass`): five new G2 edges into proof modules. Move it to the end of P2 as optional. If built, state the membership `V_h^k ∈ X_{h,I^true}` (terminal-zero family) as an explicit conjunct, not only the stage-table equality. |
| 27 | Remark 6.1 | O | **O ✓** | |
| 28 | Remark 6.3 | I/K | **I/K ✓, with C7** | `Remark6_3` already exists and its docstring already cites `offlineRL.tex:175–185` first, so the mis-filing is purely a generator issue. However the last sentence (:184, "many bounds continue to hold", li2024settling) is cited-only and explicitly not covered. The node can be "proved (sentences 1–3)" plus a separate O/cited note. It must not get a blanket closed status. |
| 29 | Remark 6.6 | N | **N ✓** | |
| 30 | Remark 6.7 | N | **N ✓** | |
| 31 | Remark 6.8 | N | **N ✓** | The COVERAGE row must cite the exact Lean definition lines that implement "greedy only at s_t on strict increase" (`OfflineRL/LCBQDefinitions`, `FiniteLCBQ`). |
| 32 | Remark 6.9 | O | **O ✓** | |
| 33 | Remark 7.3 | O | **O ✓** | |
| 34 | `eq:convex.Cdelta` | in flight + O | **✓** | Not re-reviewed here (items C/D/E have their own checks). |
| 35 | `eq:reward-policy-eq` | P | **P ✓, sketch fix** | Inline `Z` (F-P3a-1). |
| 36 | `eq:Jstar` | P | **P ✓, sketch fix** | Wrong hypothesis and a missing line (F-P3a-2). |
| 37 | `eq:RBMLE_online` | N/K | **N/K ✓** | Step definition; C44 covers existence. |
| 38 | `eq:RLHF-policy` | I/K | **I/K ✓ (restricted)** | Clause (a) of `Eq_online_RBMLE_restricted` is exactly for r = r^{(t+1)} (a minimizer). Inherit `_restricted` and "uniqueness not claimed". |
| 39 | Remark 5.9 | P+N | **P ✓, proof-route fix** | See §2.3 and F-P2-1. |

Counts after review: P 15 (the plan's 16, minus #26, which moves to optional), N 11, I 6 (#15 leaves I), partial 1 (#15), O 5.

### 2.2 U1–U23

| U | Plan | Critic | Notes |
|---|---|---|---|
| U1 | P | **P ✓** | Stationary class (P:66). `exists_stationary_trajectory_optimal` matches the sketch verbatim. |
| U2, U3, U7, U8 | joints | **✓** | |
| U4 | P | **P ✓** | It quantifies over every optimal deterministic f. The builder needs "Q^f = optimalityFixedPoint for every optimal f" (mutual domination with `optimalGreedyPolicy`). |
| U5 | P | **P ✓** | Exports are `LipschitzWith M.discountConstant`. The wrapper converts to sup-norm `‖·‖` on `S → A → ℝ`, and the Prop must use that Pi sup norm, not an L² norm. |
| U6 | P | **Correction C1 → N** | `eq:defn-Var-Psa-V`/`eq:matrix-VarP-V-expression` *define* `Var_P(V)`. `FiniteDistribution.variance` (Probability/VarianceDefinitions.lean:14) is literally `E[f²] − (E f)²`. "That is, the variance of V_{s'}" is `variance_eq_expectation_centered_sq` (Probability/Variance.lean:30); cite it in the N row. Drop the entry from P1. |
| U9 | P | **P ✓, sketch fix** | Bochner/lintegral and line-range errors (F-P1-1). |
| U10 | P | **P ✓** | `0 < γ` is needed because the printed bound divides by γ. At γ = 0 the printed expression is undefined, and in Lean (`x/0 = 0`) it would be false. State it as a domain condition in the docstring (not a source issue). Write `(I − γP_π)⁻¹` as a standard matrix inverse or Neumann sum in the Prop, not an internal resolvent def. |
| U11 | P (flag R-U11) | **Correction C3 → P `_restricted`** | See R-U11 (§4). |
| U12 | P | **P ✓, add conjunct** | BD:66 also claims `Regret(T) ≥ 0` (the mean-reward choice "ensures non-negativity"). Add it (F-P2-5). |
| U13 | P | **P ✓, export fix** | The randomized-π export exists: `robustPolicyQ_eq_reward_add_rowInf` (DRVI/RobustQ.lean:155), for every stationary randomized π, with `RowAttains`. Use it instead of `robustBellman_eq_robustQ` (an `rfl` about the operator). No `_restricted` is needed. |
| U14 | P | **P ✓, object fix** | See F-P3a-3: the sketch states it about `optQ` (defined as `robustQ (optFix)`), which makes "fixed point" nearly definitional. The book's Q^{⋆,σ} is the trajectory object `robustPolicyQ … (detPolicy f)`. |
| U15 | P | **P ✓** | `_restricted`: uniqueness on supp ρ only. Correct. |
| U16 | P | **P ✓, add conjunct** | RLHF:90 also claims J⋆(r₁) = J⋆(r₂) + E_ρ c (F-P3a-4). |
| U17 | P | **P ✓, spec fix** | `bestResponseValueJ` exists only at step 1 (`⨆ π', valueJ G (deviate π i π') i 1 H s`). See F-P3b-1. |
| U18 | P | **P ✓, spec fix** | Reading fixed in F-P3b-2. |
| U19 | P | **P ✓** | The outer-measure reading is sound: for non-measurable convex A, pick a measurable B ⊇ A with Q(B) = Q*(A). Then P*(A) ≤ P(B) ≤ Q(B) + TV, and symmetrically. In Lean, `μ A` is already the outer measure, so no special encoding is needed. |
| U20 | P (tiny) | **✓** | |
| U21 | in flight | **✓** | Not reviewed. |
| U22 | O optional | **✓** | |
| U23 | O | **✓** | |

Additional N items the plan omits; add them to the T list (all qualitative, no entry):
- P:66, "typically sufficient to restrict attention to time-invariant policies";
- P:225–228, "linear systems … can be solved";
- RLHF:74, "Z formidable to compute";
- OFF:1792–1793, "substantially smaller than … Q-learning … pertains only to ρ".

### 2.3 Remark 5.9: paper verification

The claim (ON:3299–3311) is **true** on the printed domain: p a probability vector, 0 ≤ v ≤ H, n ≥ 1,
c₁ > 0, ι = log(1/δ′) ≥ 0. Write L = ι/n, a = c₁√L, b = c₁²HL and θ = c₁H√L, so that aθ = b, and the
√ branch is active iff √Var ≥ θ.

*Lemma A* (verified). For 0 ≤ v ≤ w ≤ H with d = w − v and u = w + v:

  Var(w) − Var(v) = E[d u] − E[d] E[u] = E[d (u − E u)].

Since u, E u ∈ [0, 2H], we get |Var(w) − Var(v)| ≤ 2H ⟨p, w − v⟩.

*The plan's elementary route is wrong as written.* It requires only max{√Var(v), √Var(w)} ≥ θ. With
only √Var(v) ≥ θ, the bound √a − √b = (a − b)/(√a + √b) with √a + √b ≥ θ gives

  a(√Var(w) − √Var(v)) ≥ −2⟨p, d⟩,

which is off by a factor of 2 and does not close the argument. It works when **both** √Var(v) ≥ θ and
√Var(w) ≥ θ. Then √a + √b ≥ 2θ, and

  f(w) − f(v) ≥ ⟨p, d⟩ − a · 2H⟨p, d⟩/(2θ) = ⟨p, d⟩(1 − a²H/b) = 0.

*Correct elementary route* (no derivatives):
1. If Var(v) ≤ θ², then f(v) = ⟨p, v⟩ + b ≤ ⟨p, w⟩ + b ≤ f(w).
2. If Var(v) ≥ θ² and Var(w) ≥ θ², apply Lemma B (the both-endpoints bound above).
3. If Var(v) > θ² > Var(w), then t ↦ Var(v + t(w − v)) is continuous on [0, 1]. The IVT gives x* on the
   segment with Var(x*) = θ². The segment stays in the box and v ≤ x* ≤ w. Then f(v) ≤ f(x*) by Lemma B,
   and f(x*) = ⟨p, x*⟩ + b ≤ ⟨p, w⟩ + b ≤ f(w).
4. Edge cases: θ = 0 means ι = 0 (then f = ⟨p, ·⟩) or H = 0 (then v = w = 0).

This proves the vector form directly, with no coordinate chaining. Truth risk: low. Size: 250–450 lines.

---

## 3. Category corrections (C1–C7)

- **C1** U6: P → N (definition; cite `variance_eq_expectation_centered_sq`).
- **C2** #15, Remark 4.5 sentence 3: N → "implied only via O4". The node stays partial until O4 lands.
  Recommend O4 in P2.
- **C3** U11: P → P `_restricted` (entry `Thm3_2_burnInNecessary_restricted`), with a scope disclosure.
- **C4** D11 (OFF:1779–1785): the plan calls it a "cited claim", but the Bernstein-LCB-Q sentence has
  **no citation** (citations appear only at OFF:1799, for variance reduction). It is an uncited,
  underspecified book claim, so it is a source-fidelity finding (SOURCE-ISSUES at the next free C-id). It
  is **not eligible** for `cited-out-of-scope`, and it stays open unless the user explicitly scopes it out
  with accurate wording ("uncited, algorithm unspecified"). *Resolved as an open source-fidelity finding, [C50](SOURCE-ISSUES.md#C50) (user decision 2026-11-09).*
- **C5** R5.3/D6 rationale: "stationary MDPs are outside the book's model" is wrong, since stationary
  finite-horizon MDPs are a subclass of the book's nonstationary ones. Correct reason: "needs the
  azar2017 stationary analysis (shared transitions across steps), which the book does not develop".
- **C6** #26 `Eq_Vk_Itrue_corrected`: required P → optional (see §2.1).
- **C7** #28 Remark 6.3: not a blanket I/K. Sentences 1–3 are proved (`Remark6_3`), and sentence 4 (:184)
  is cited-only O.

---

## 4. Critic targets of plan §8: rulings

- **R-U11.** "Strictly better than a random guess" is undefined in the book. The plan's reading
  (constant-factor accuracy c′/(1−γ) w.p. ≥ 3/4) is reasonable, but it is a *reading*, not the printed
  statement, and it does not cover accuracies between c′/(1−γ) and 1/(1−γ). Required:
  1. name it `Thm3_2_burnInNecessary_restricted`;
  2. use the book's success metric `V⋆ − V^{π̂}` (Q-failure > ε implies V-failure > ε/γ, since
     `Q^{π̂} − Q⋆ = γP(V^{π̂} − V⋆)`; derive it in the wrapper);
  3. disclose deterministic estimators only (inherited from `Thm3_7_corrected`), and S ≥ 2, A ≥ 2,
     SA ≥ 16, γ ≥ 2/3;
  4. state ε = 1/(64(1−γ)) < 1/(32(1−γ)), as `Thm3_7_corrected` requires;
  5. point to a SOURCE-ISSUES scope-disclosure entry.
- **U9 χ².** Must be the lintegral `∫⁻ ofReal((dP/dQ − 1)²) dQ`. The Bochner `∫` in the plan's code
  block returns 0 when not integrable, which makes the Prop false. Keep `P ≪ Q` as a hypothesis (the book
  defines KL and χ² only then). Correct the plan's note (c): if χ² < ∞, then ∫ f² dQ < ∞, so `f log f`
  (bounded by f(f−1) above and −1/e below) is Q-integrable. So `klDiv` is finite and ≤ χ². If χ² = ∞, the
  right inequality is trivial.
- **ice-cream β₁.** Matches: the export proves the bound for every `C₀ ≥ 8`, with
  `policyEvaluationDepth = ⌈log(e/(1−γ))⌉₊` = the printed m and β₁ = C₀ log(Sm/δ). The printed
  "for some large enough C₀" is `∃ C̄, ∀ C₀ ≥ C̄`. No `_restricted` is needed. The premise is wrong
  (F-P2-2).
- **U6:** definition (C1).
- **U13:** export exists for randomized π (see §2.2).
- **U17:** see F-P3b-1.
- **U18:** see F-P3b-2.
- **Remark 5.9:** true; the route is corrected (§2.3).
- **Remark 5.13:** identification confirmed.
- **T:** see §5.T.

---

## 5. Required fixes (exact text where it matters)

### P1
- **F-P1-1 (U9).** Replace the right-hand side in the sketch with
  `InformationTheory.klDiv P Q ≤ ∫⁻ x, ENNReal.ofReal (((P.rnDeriv Q x).toReal - 1) ^ 2) ∂Q`.
  Change the locator to `chapters/intro.tex:216–247` (TV `:219–223`, KL/χ² `:227–235`, display
  `:241–247`). The plan's ":226–235" stops before the display.
- **F-P1-2 (U6).** Delete `Eq_matrix_VarP_V_expression` from P1. Add an N row (C1).
- **F-P1-3 (finite horizon).** In `Eq_dh_pi_defn`, the third conjunct must read "for every deterministic
  Markov policy f_h: d_h(s,a) = d_h(s)·1{a = f_h(s)}" (P:769, "holds given that π⋆ is deterministic"),
  not "greedy stages". In `Eq_Bellman_finite_opt`, quantify over every deterministic policy that dominates
  all Markov policies in V and Q at all (s,a,h), and assert existence of one (U8, P:739–741). Do not use
  `optimalValueAt`/`greedyActionAt` in the Prop. This also removes the G2 edges to `MDP.FiniteOptimal`,
  `MDP.OccupancyBridge` and `MDP.OptimalTrajectoryValue`.
- **F-P1-4 (G2 minimization).** The expected Ch2 G2 growth after F-P1-3 is `MDP.InfiniteReturn`,
  `MDP.ForcedActionReturn`, `MDP.DiscountedOccupancy`, `MDP.FiniteOccupancy`, `MDP.FiniteQTrajectory`.
  These are mixed definition/proof modules. AGENTS says "imports definition modules only". The gate only
  forbids `*Proofs`, and Ch6/Ch3Definitions already import such modules. The lead must list each edge in
  the PR with "defining module of `<def>`; no `*Definitions` split exists". Use
  `--write-allowlists --allow-grow` once, after the critic. Ch1.lean must import specific Mathlib modules
  only (no bare `import Mathlib`). Then Ch1 needs **no** G2 growth.
- **F-P1-5 (ownership).** The brief lists `Statements/Ch1.lean` and `Ch1Proofs.lean` as builder-owned,
  while the rules say statement drafts are builder drafts and the lead integrates. Use one
  rule: the builder drafts Ch1/Ch1Proofs content as builder drafts, and the lead creates the files at
  integration.
- **F-P1-6.** Every docstring must contain a literal `chapters/<file>.tex:a–b` range (the G3 regex). The
  sketch docstrings for `Eq_defn_Qpi_inf_horizon` and `Eq_bellman_consistency_V` give bare `:117–121`.
- **F-P1-7 (#1).** Either add the "V^π equals the T_π fixed point" conjunct to `Eq_defn_Vpi_inf` or
  remove it from the table row. Prefer omitting it, since it is already in `Eq_bellman_consistency_V`.

### P2
- **F-P2-1 (Remark 5.9).** Replace the plan's proof note with §2.3 (Lemma A, Lemma B with *both*
  endpoints above θ, IVT reduction). The docstring cites `chapters/onlineRL.tex:1330–1332` **first**, then
  `:3299–3311` and the proof `:3392–3433` (so the generator files it under the remark; see F-T-2).
- **F-P2-2 (ice-cream).** The display's own premise is **`N ≥ β₁/(1−γ)`** (MB:632), not
  `64β₁/(1−γ)`, which is Step 5/6's working premise at :589/:621. Sketch:
  `∃ C̄ > 0, ∀ C₀ ≥ C̄, ∀ … N (hN : 0 < N) δ, 0<δ → δ<1 → let m := ⌈log(e/(1−γ))⌉₊; let β₁ := C₀ * log(|S|·m/δ);
  β₁/(1−γ) ≤ N → 1 − δ < ℙ(‖V̂^π − V^π‖ ≤ 3√(8β₁/((1−γ)³N)))`.
  Write m inline, not `policyEvaluationDepth` (which lives in proof module
  `PolicyEvaluationHighSample`), so Ch3 needs no G2 growth (`valueEstimator`/`samplingLaw` are in
  `Ch3Definitions`). Check that the export's `valueEstimator` is the Ch3Definitions one.
- **F-P2-3 (U11).** As R-U11 (§4).
- **F-P2-4 (U10).** Add `0 < M.discount` with the docstring reason (printed /γ). Use a standard inverse
  in the Prop. Expect one possible G2 edge (`MDP.PolicyMatrixDefinitions` for Ch3). List it.
- **F-P2-5 (U12).** Add `0 ≤ Regret(T)` pathwise (BD:66–67) to `Eqn_regret_decomposition_ucb`.
- **F-P2-6 (#26).** Optional and last (C6). If built, list its G2 edges explicitly.
- **F-P2-7 (Remark 5.13).** The docstring cites C8 and the identification with `onlineActualT6*`
  (§2.1 #25). The √ conjunct needs `0 ≤ T6Policy`, `0 ≤ T6Difference` (proved, not assumed).
- **F-P2-8 (O4).** Recommended in P2: `QLearning_singleAction_eq_TD` (A = 1 synchronous Q-learning
  iterates equal TD iterates in law), so Remark 4.5 can close. If skipped, Remark 4.5 stays partial (C2).

### P3a
- **F-P3a-1.** Do not use `partitionFn` (it is defined in proof module `VPOGibbs712`). Write
  `Z(r,x) = ∑ y', π_ref x y' * Real.exp (r x y' / β)` inline (`eq:normalization`, RLHF:55–58). This
  needs no G2 edge.
- **F-P3a-2 (`eq:Jstar`).** Step (i) needs `IsCondPolicy π_cal` (∑_y π_cal(y|x) = 1), **not** ∑ρ = 1.
  ρ ≥ 0 suffices. Include all three printed equalities: the first line (`E_{ρ,π_r}[r − β(log π_r −
  log π_ref)] − E_{ρ,π_cal} r`), the log Z line, and lines (i) and (ii).
- **F-P3a-3 (U14).** State it with the trajectory object: for every robust-optimal deterministic f (in
  the sense of `Eq_mdp_value_Q`), `Q⋆ := robustPolicyQ ball M σ (detPolicy f)` satisfies
  (a) `Q⋆ = T^σ Q⋆` (with `V(s) = max_a Q(s,a)` written out),
  (b) every fixed point of `T^σ` equals Q⋆,
  (c) `T^σ` is a γ-contraction in sup norm (ROB:133), and
  (d) the DRVI iterates from Q̂₀ = 0 satisfy `|Q̂_t − Q̂⋆| ≤ γ^t/(1−γ)`, for any nominal kernel (this
  covers both the true and the empirical operator, ROB:132 and :261).
  Route: `robustPolicyQ_optPolicy` (RobustQ.lean:124) plus mutual domination for arbitrary optimal f.
  `RowAttains` must be proved for both balls, not assumed.
- **F-P3a-4 (U16).** Add the conjunct `optValue(r + c) = optValue(r) + ∑ x, ρ x * c x`, the
  uncalibrated J⋆ of RLHF:90. Write J(r,π) inline as in `Eq_online_RBMLE_restricted`. It needs
  `IsCondPolicy` for every competitor π.
- **F-P3a-5 (U13).** Cite `robustPolicyQ_eq_reward_add_rowInf` and `robustPolicyValue_eq_policyFix`.
  Write the infimum as `sInf`/`⨅` over the ball, or use `rowInf` only if it is defined in a definitions
  module already imported by Ch7.

### P3b
- **F-P3b-1 (U17).** Define inline `V⋆_{i,h}(s) := ⨆ π' : PlayerPolicy S (A i), valueJ G (deviate π i π') i h (H − h + 1) s`
  for every h ∈ [1,H] (π joint; `deviate` already uses the marginal of the others). Claim: (a) ∃ μ attaining
  it at all (h,s) simultaneously (maximum attained, marl:128–131); (b) the Bellman optimality display
  (marl:136–140) with terminal 0; (c) `BddAbove` is a proof obligation, not a hypothesis.
- **F-P3b-2 (U18).** Reading: (a) `∀ G (π : ProductPolicy), IsNE G π → IsCCE G (embed π)`; (b) `∃ G
  (m = 2, S = 1, H = 1) (π : JointPolicy), IsCCE G π ∧ ∀ π' : ProductPolicy, embed π' ≠ π`. The witness
  is a coordination game with π uniform on {(0,0),(1,1)}: V = 1 > 1/2 = best response, and π is not a
  product, since p(1−q) = 0 contradicts pq = (1−p)(1−q) = 1/2. Write `embed` inline (per-(h,s) product
  law). Note in the docstring: for product policies CCE ⇔ NE, so "not NE" = "not product".
- **F-P3b-3.** As planned, integrate only after inference builders C and D land (shared `Ch7.lean`).

### T
- **F-T-1 (never proved).** `explanatory`, `implied` and `cited-out-of-scope` are counted in three
  separate counters and never in "proved", "printed", "corrected" or "restricted". README, site and NEXT
  keep "INCOMPLETE". The whole-paper completion claim stays false while any `cited-out-of-scope` or
  partial node exists (AGENTS: "all … substantive mathematical claims").
- **F-T-2 (readiness).** For readiness of dependants, `explanatory` and `implied` nodes count as resolved.
  **`cited-out-of-scope` nodes do not**: a node that uses an unproved cited result stays blocked. Fix the
  Remark 6.3 mis-filing in the generator: the joint-entry rule must prefer the node whose range equals the
  docstring's first `.tex:a–b` range.
- **F-T-3 (qualifier inheritance).** `**Implied by `X`**` must resolve X to an entry with exactly one
  `X_holds` (G3), and the generated status must carry X's suffix (`implied (corrected)`,
  `implied (restricted)`). This applies to #20, #22, #23 and #38. A node with an N remainder (#22) gets
  `implied` only if the row lists the N sentences.
- **F-T-4 (user gate).** `**Out of scope: cited result**` is accepted by the generator only if the row
  also cites a user-decision anchor (e.g. `docs/DECISIONS.md#Dxx`, dated, quoting the user's words), and
  the generator fails otherwise. Batch T writes **no** such rows now. AGENTS forbids inferring approval.
  *Superseded 2026-11-09: the user decided to record cited results not stated precisely about the book's
  own objects as out of scope ([PROGRESS.md](PROGRESS.md#user-decisions-2026-11-09), completion triage); the
  generator enforces a dated `user decision YYYY-MM-DD` anchor.*
- **F-T-5 (D11).** *Resolved as an open source-fidelity finding, [C50](SOURCE-ISSUES.md#C50) (user decision
  2026-11-09).* Per category correction C4: a SOURCE-ISSUES entry ("uncited Bernstein LCB-Q claim; penalty, rate and ε
  threshold unspecified; `Thm6_8_corrected` does not imply (1−γ)⁻⁴"), status open. Check C49 first, as
  the plan says.
- **F-T-6 (explanatory review).** Each `explanatory` headline cites this check (or a later critic) as
  its review. #15 is not explanatory (C2). Add the four extra N items (§2.2).
- **F-T-7 (F1 rows).** `implied` is acceptable for the 17 Õ rows only if each row states the precise Õ
  reading (which theorem, which log factors are dropped) and says "Õ form not a separate Prop". Keep
  FED:120–129 open (C41).

### Plan-wide
- **P-0.** Re-pin the NEXT/COVERAGE hashes (see header).
- **P-1.** Recount §2 and §9 after C1, C3 and C6: new entries are 14 (NEXT) + 15 (§2) = **29**, not 31.
  P1 has 10 Ch2 entries plus Ch1's `Eq_KL_ub_chi2`.

---

## 6. Batch estimates, order, disjointness

- Estimates are plausible. Adjustments: P1 −40 lines (U6 dropped), +40 (arbitrary-π⋆ bridging).
  P2: Remark 5.9 drops to 250–450 with the IVT route; +O4 150–300 if adopted. P3a U14: 100–200 (bridging
  for arbitrary f plus `RowAttains` for both balls).
- Order T → P1 ∥ P2 → P3a/P3b after C/D is sound. T must land its generator change before any P-batch
  COVERAGE rows. T must not touch `site/**` while the site builder is active.
- Write sets are disjoint. P1 owns `MDP/PrelimDisplays.lean` and `Probability/KLChiSquared.lean`. P2
  owns `Online/SourceOptimism/MonotoneBonusFunction.lean`, `Generative/BurnInNecessity.lean`, and adds
  `Generative/VarPBoundDisplay.lean`, `Online/Bandit/RegretDecompositionDisplay.lean` and (if O4)
  `ModelFree/QLearningSingleActionTD.lean`. P3a owns `RobustRL/DRVI/RobustBellmanDisplays.lean` and
  `Ch7Rest/VPODisplays712.lean`. P3b owns `Ch7Rest/MarlBestResponse.lean` and
  `Ch7Rest/ConvexDistanceTV711.lean`. All `Statements/*`, `Formalization.lean`, docs and gate lists are
  lead-only and sequential. Record ownership rows in `docs/PROGRESS.md` before starting.
- Lean slots: with D and the C-r2 critic active, at most one of P1/P2 compiles at a time. Each builder
  checks `pgrep -x lean | wc -l` < 2 before compiling.

---
