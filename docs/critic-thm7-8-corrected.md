# CRITIC: corrected Theorem 7.8 (`thm:lower-marl`), post-build statement and proof review

Public copy of the independent critic report; local paths removed.

Post-review note (added to this public copy, 2026-11-07): the learner seed was later generalised from a finite seed to any discrete (countably supported) seed law; that generalisation was reviewed in docs/critic-thm7-8-integration.md. The review text below is unchanged.

Reviewer: independent critic subagent (not the builder). Date 2026-11-07. No author approval exists or is
implied; nothing here is a frozen-statement status. Edited nothing except this report and my own probe
`<reviewer probe folder>/CriticProbe.lean`.

Inputs (sha256):
* `source/upstream/tex/chapters/marl.tex` `8fadfab2c41ecad62349e27478adf2018047ad24a363c63a9918279238d12ffb`
  (matches docs/critic-thm7-8-plan-check.md).
* WIP files (all match BUILD-LOG "Final source hashes"):
  Defs `5f1f803b…5930`, Values `f0c681d4…d59b`, Hard `88fdda67…501f`, Testing `306de757…4e12`,
  HardTesting `74240961…53ca`, Bayes `2d288a8e…fc8f`, Statement `a24f8cc2…b38d`, Main `cf7bcf09…a69f`,
  Product `d0d30f2c…80bd`, AxiomProbe `50a038ae…1031`.
* Critic probe `CriticProbe.lean` `a60d12e70f42f5b1d9b62cbc6ed36b5f79bdb38bf096560efa31809abf15cdd2`.

## Verdicts

| Prop | Verdict |
|---|---|
| `Thm7_8_corrected` (zero-sum convention `zeroSumAdm`) | **ACCEPT WITH DISCLOSURES** |
| `Thm7_8_corrected_constSum` (`constSumAdm`) | **ACCEPT WITH DISCLOSURES** |
| `gapJ_toJoint` (bridge to existing `gap`) | ACCEPT |

Both Props are honest `_corrected` entries (they add size ranges and fix a convention the source leaves
undefined); neither may be called the printed theorem. Disclosures D1–D6 below must appear in the
docstring and/or SOURCE-ISSUES C40 when integrated.

## Compile evidence (actual commands, foreground, one at a time, no `-o`)

`bash scripts/lean-local.sh <builder working folder>/<F>.lean` for F = Defs, Values, Hard,
Testing, HardTesting, Bayes, Statement, Main, Product, AxiomProbe: every exit 0, no errors, no warnings
printed (14s, 4s, 2s, 7s, 3s, 10s, 2s, 5s, 1s, 5s). AxiomProbe output:
`thm7_8_corrected`, `thm7_8_corrected_constSum`, `gapJ_toJoint` each depend on `[propext, Classical.choice,
Quot.sound]`; the two `#check`s confirm the exports have exactly the types `Thm7_8_corrected`,
`Thm7_8_corrected_constSum`. Grep of all WIP `.lean`: no `sorry`, `admit`, `axiom` (other than
`#print axioms`), `native_decide`, `implemented_by`, `extern`, `unsafe`, `opaque`, `set_option`, macros.
Caveat: dependency oleans in `.lake/build/lib/lean/Thm78Wip/` are the builder's (12:47–12:48 local, after
the last source edit per BUILD-LOG); every source re-elaborated against them, so the chain is consistent.

`bash scripts/lean-local.sh <reviewer probe folder>/CriticProbe.lean`: exit 0, all four
probe results axiom-clean (`propext, Classical.choice, Quot.sound`):
* `prob_le_one`: the Prop's probability expression lies in `[0,1]` for every game/learner (genuine
  probability, no junk mass).
* `deviate_prob`: `(deviate π i π' h s).prob a = π'_{h}(a_i|s) · ∑_c π_h(update a i c | s)`, i.e. exactly
  `π'_i × π_{-i}` with `π_{-i}` the others' joint marginal (`marl.tex:84–85, 119–126`).
* `gapJ_zero_reward`: a zero-reward game has `gapJ = 0` for every joint policy (gap not junk-large).
* `nonvacuous`: from `thm7_8_corrected`, at `m = S = H = 2`, `A ≡ 2`, for whatever constants it provides,
  some `ε > 0` is admissible, `N = 1` is under the budget, and the conclusion is delivered for a concrete
  learner (point-mass seed on `Fin 1`, constant query rule, constant output). Hypotheses are satisfiable
  and the learner binders are inhabited.

## Independent reconstruction of the source (before reading Lean)

`marl.tex:487–503`: ∃ universal `c₁, c₂ > 0`; ∀ `m ≥ 2`, `S, H, A_i` (no ranges), `0 < ε ≤ c₁H`;
∃ family of "m-player zero-sum" games with `S` states, horizon `H`, `A_i` actions; if total sample size
`< c₂H⁴S max_i A_i/ε²` then `inf_{π̂} max_θ P_θ{gap(π̂) > ε} ≥ 1/4`, infimum over all (joint) policy
estimators. Gap `:332–340` = `max_s max_i (V^{⋆,π_{-i}}_{i,1}(s) − V^π_{i,1}(s))`, best response over Markov
`π'_i : S×[H] → Δ(A_i)` played independently of `π_{-i}` (`:119–126`). Policies are Markov throughout
(`:71–73`). Sampling `:307–315`: adaptive choice of `(s, a, h)`, independent `s' ~ P_h(·|s,a)`. Rewards
deterministic, `[0,1]` (`:41–43`); zero-sum defined only for `m = 2` (`r₂ = −r₁`, `r₁ ≥ 0`, `:50–53`, footnote
shift). Known reward: plug-in uses true `r` (`:374`). No proof or citation.

## Findings

### Binder-by-binder (both Props; they differ only in the admissibility predicate)

1. **Quantifier order** — `∃ c₁ c₂ > 0, ∀ m S H A, ranges → ∀ ε, 0<ε≤c₁H → ∃ Θ G, adm ∧ shared reward ∧
   ∀ N < budget, ∀ K seed rule out, ∃ θ, 1/4 ≤ P_θ`. Constants universal and first (as printed). Family is
   chosen before `N` (stronger than the source, which may let it depend on `N`); learner after family,
   `θ` after learner = `inf_π̂ max_θ`. `∃ θ, P_θ ≥ 1/4` is the printed max (stronger than sup). Correct.
2. **Budget** — `(N : ℝ) < c₂ * H^4 * S * (univ.sup A) / ε^2`, real-valued, `univ.sup A = max_i A_i`, strict
   as printed ("smaller than"). Exactly `N` queries; a learner with fewer samples is covered by padding.
   `c₁ = 1/2048`, `c₂ = 2⁻³²` in the proof (positive; "sufficiently small" reading). Correct.
3. **Learner class** — seed law `FiniteDistribution (Fin K)`, per-step randomized rule
   `rule ω t (history of (query, answer))`, output `out ω hist : JointPolicy` (Markov, possibly correlated).
   Query `(h, s, a) ∈ Fin H × Fin S × joint actions` maps to step `h+1` (`genEnv`), matching `:307–311`;
   `interactionLaw` (`AdaptiveKLDefinitions.lean:49–94`) is the genuine sequential product law
   `P_{T+1}(h) = P_T(init h) · π(a|init h) · e(o|init h, a)`, and `genEnv` ignores the past (independent
   samples). At least as general as the source's adaptive allocation. See D1 for the finite seed.
4. **Output class** — joint Markov policies only. The source defines policies and gap only for Markov
   policies (`:71–73`, `:332–346`), so this is faithful; `gapJ` is not defined by the source for
   history-dependent outputs (D4).
5. **Gap** — `gapJ = ⨆ s, ⨆ i, (⨆_{π' : PlayerPolicy} valueJ (deviate π i π') − valueJ π)`. Outer sups are
   over nonempty finite types (`S, m ≥ 2`): exact maxima. Inner sup over Markov deviations is the source's
   `eq:defn-optimal-V` (`:122–126`, `π'_i : S×[H] → Δ(A_i)`); `deviate` is the source deviation (probe
   `deviate_prob`). Restricting deviations to Markov makes the gap no larger, hence the lower bound no
   easier: the right direction. Well-definedness: the iSup is bounded above whenever `A i ≥ 1` (values use
   only finitely many reward entries); the proof itself establishes `BddAbove` (`Values.lean:68–87`,
   `le_ciSup` with bound `H` from `reward ≤ 1`), so the lower bound on the gap is genuine, not a junk 0.
   `valueJ G π i 1 H s` = `V^π_{i,1}(s)` with steps `1..H` (`:101–106`). Correct.
6. **Zero-sum convention (`zeroSumAdm`)** — `∑_i r_i = 0`, player index 0 rewards in `[0,1]`, all `|r_i| ≤ 1`,
   imposed at every `h : ℕ`, `s`, `a`. For `m = 2` this is exactly `r₂ = −r₁`, `r₁ ∈ [0,1]` (`:50–53`; the
   `[0,1]` upper bound on `r₁` is the `:41–43` normalisation). Since the predicate sits under `∃ family`,
   any extra strictness strengthens the theorem. For `m ≥ 3` the source has no definition; `Σ r_i = 0` is the
   standard reading. Disclosed in the Defs docstring. D3.
7. **Constant-sum variant** — `∑_i r_i = 1`, all `r_i ∈ [0,1]`: satisfies the `:41–43` normalisation for every
   player and is an instance of every "constant-sum / shifted zero-sum" reading (incl. the existing
   `sumConstant` predicate of `MarlPrinted78.lean`). The two Props together cover both natural readings
   (zero-sum with `r₁ ≥ 0` but `r₂ ∉ [0,1]`, or normalised constant-sum). The literal
   `sumZeroNormalized` reading (sum 0 and all in `[0,1]`) forces zero rewards and cannot hold; that is a
   source defect already recorded in C40.
8. **Known reward** — encoded by `(G θ).reward = (G θ').reward` plus learner quantified after the family.
   Matches `:374` and `generative_model_model_based.tex:31` per CHECK §3. Correct.
9. **Size hypotheses** — `m ≥ 2` (printed); `S ≥ 2`, `H ≥ 2`, `max A ≥ 2` added.
   * `max A ≥ 2`: necessary. With `A ≡ 1` every joint policy is the point mass, every deviation is trivial,
     `gapJ = 0`, probability 0 (also Lean-refuted for the printed Prop, `not_thm7_8_printed`).
   * `S ≥ 2`, `H ≥ 2`: necessary by docs/critic-thm7-8-plan-check.md §3 (C5): with `S = 1` all games in any admissible
     family coincide (unique transition, shared reward), with `H = 1` transitions are irrelevant; in both
     cases backward induction with stage-game CCEs (existence of CCE in finite normal-form games) gives an
     exact Markov CCE, gap 0, so every family fails. I re-checked the `S = 1` deviation argument: with one
     state the continuation value is independent of the current action, so per-step CCE inequalities sum.
     **Prose only, not Lean-proved** (D5).
   * `m ≥ 2` is also necessary for both Props (`m = 1`: zero-sum forces `r ≡ 0`, constant-sum forces `r ≡ 1`,
     gap 0). Prose.
   Hence the four ranges are a minimal set for the stated constants and rate. Nothing else is assumed: no
   `N ≥ 1`, no `ε` lower bound, no `A_i ≥ 1` for the non-maximal players.

### Proof soundness spot checks

10. **Hard family respects reward ranges** (`Main.lean:108–153`): `r_istar = 1[s≠z] − cst`, partner `p` gets
    the negation, others 0; `cst = 0` if `istar` is player index 0, else `cst = 1` and `p` is index 0, which
    then gets `1[s=z] ∈ [0,1]`. Sum 0, all in `[−1,1]`. This is the CHECK C3 fix. constSum: `r_istar =
    1[s≠z]`, `r_p = 1[s=z]`, sum 1. Reward independent of `θ` (`rfl`). Verified.
11. **Values formula** (`Hard.lean:126`): `V_istar = chainU(ℓ) − cst·k` off the sink; the constant shift is
    policy-independent and cancels in the gap. `hard_chain_gap` uses the deviation `piStar` (point mass on
    the hidden action) through `gapJ_ge` + `deviate_sum_coord`. Verified by reading and compile.
12. **Testing** — `finite_event_pinsker` derives from `PrelimFano.event_sq_gap_le_klDiv` (`2(p−q)² ≤ KL`);
    linearisation `p − q ≤ 2KL + 1/16` follows from `√(y) ≤ 4y + 1/16` with `y = KL/2` (AM–GM), correct.
    Prior `1/2` on the reference, `1/(2(n−1))` on each alternative (`sum_wt = 1`). `coord_bayes_le` gives
    `≤ 17/32 + ΣK_j/(n−1)`; the adaptive KL bound `KL(P_ref‖P_j) ≤ κ·E_ref[N_{c,j}]` comes from
    `hard_hist_kl_le` with absolute continuity `hard_env_ac`. Constants consistent with
    `budget_of_N` (`64κN ≤ (A−1)(S−1)⌊H/2⌋`, `λ = 1024ε`, `ε < λ/512`, `λ ≤ H/2` from `ε ≤ H/2048`).
13. **Bayes averaging to 1/4** (`Main.lean:58–99`): per-seed `hard_bayes` gives prior-average ≥ 1/4 for
    each deterministic `(rule ω, out ω)`; averaging over the seed and a strict-sum contradiction with a
    positive-mass `θ₀` yields `∃ θ`. Correct; uses only `sum_prior = 1`, `prior ≥ 0`.

### Bridge

14. `gapJ_toJoint : gapJ G (toJoint π) = gap G π` for every game (no hypotheses) — the joint-policy gap of
    a product policy equals the existing product `gap` of `MarlPrinted78.lean` (deviation of a product policy
    = `Function.update π i π'`, `deviate_toJoint_sum`). So product (NE-style) learners are covered with the
    same gap; no separate `Thm7_8_restricted_product` is needed for coverage. ACCEPT.

## Disclosures (must be stated in the docstring / C40 when integrated)

* **D1 (finite seed).** Shared learner randomness is a finitely supported seed `Fin K`. Not a real
  mathematical restriction: (a) for queries, with finite query/answer spaces and fixed `N` there are
  finitely many deterministic query strategies (Kuhn), and per-step randomization is a full
  `FiniteDistribution` over the finite query set; (b) for outputs, an arbitrary randomized output kernel is
  a mixture of deterministic outputs, the event probability is linear in the mixture, and the proof shows
  the prior-averaged failure ≥ 1/4 for every deterministic `(rule, out)`. But the Lean Prop does not
  literally quantify over measurable output kernels into the (continuous) policy space. Disclose as a
  modelling choice. Optional strengthening: seed over an arbitrary `Fintype`, or a general probability space
  with measurable `out` (a few lines on top of `hard_bayes`).
* **D2 (degenerate `A_j = 0`).** If some `A_j = 0` (allowed since only `max A ≥ 2` is assumed), the query type
  is empty, so no `rule` exists and the conclusion is vacuously true. The source implicitly has `A_i ≥ 1`;
  this does not weaken anything in the meaningful range. Mention in one line.
* **D3 (zero-sum for `m ≥ 3`; dummy players).** `zeroSumAdm` is a chosen convention for `m ≥ 3`; the hard
  family has only two non-dummy players (all others reward 0, transitions depend only on `a_istar`). This
  is allowed by the existential family but should be stated, together with the fact that the constSum Prop
  covers the normalised reading.
* **D4 (Markov outputs and Markov deviations).** Outputs are joint Markov policies and best responses range
  over Markov player policies, as in the source; restricting deviations can only lower the gap.
* **D5 (minimality partly prose).** Necessity of `S ≥ 2`, `H ≥ 2`, `m ≥ 2` relies on CCE existence and is
  not Lean-proved; necessity of `max A ≥ 2` is immediate (and Lean-proved for the printed Prop).
* **D6 (admissibility at all `h : ℕ`).** `zeroSumAdm`/`constSumAdm` constrain rewards at every `h : ℕ`, not only
  `h ∈ [1, H]`; harmless (stricter, under `∃`).

## Required edits (before landing; none block the mathematical verdict)

R1. Statement docstrings: add D1, D2, D4 sentences; mention that the history passed to `out` contains the
    queries and answers (current text says "the `N` answers").
R2. Registration per AGENTS.md: move the two Props to `Formalization/Statements/Ch7.lean` (definition imports
    only; `Statement.lean` already imports only `Defs`), proofs `Thm7_8_corrected_holds` /
    `Thm7_8_corrected_constSum_holds` in `Ch7Proofs.lean` applying the library theorems; docstrings must point
    to `docs/SOURCE-ISSUES.md#C40` and state the differences from the printed result (already present).
R3. SOURCE-ISSUES C40: record the corrected statement, the two conventions, D1–D5, the constants
    `c₁ = 1/2048`, `c₂ = 2⁻³²`, and that minimality of `S, H, m ≥ 2` is prose.
R4. Rename the `Thm78Wip.*` modules into the library namespace path and include them in `Formalization.lean`
    so `python3 scripts/check.py` and `Audit.lean` cover them; re-run the axiom audit after the move.
R5. Optional (D1): generalise the seed; optional: Lean-prove the `A ≡ 1` and `m = 1` necessity remarks
    for the corrected Props.

## Minimality notes

The Props assume exactly `m, S, H, max_i A_i ≥ 2`, `0 < ε ≤ c₁H`, `N < c₂H⁴S max A/ε²`; each range is
necessary (Finding 9), the rate matches the printed `H⁴ S max_i A_i / ε²` in every parameter, the family is
fixed before `N`, the conclusion is a genuine `max` (not sup), and the learner class contains every
adaptive, randomized (finite-seed) generative-model learner with joint Markov output. No hidden hypotheses,
weakened conclusions or fallback definitions found.
