# CRITIC: Theorem 7.6 (`thm:sample-complexity-plug-in-marl`): `not_thm7_6_printed`, `Thm7_6_restricted`

Public copy of the independent critic report; local paths removed.

Post-review note (added to this public copy, 2026-11-08): this review was of the builder's pre-integration snapshot. Builder module `X.lean` was integrated as `Formalization/Ch7Rest/Marl76X.lean` (for example `Defs.lean` became `Marl76Defs.lean`), and module names below are given under their integrated names. Required edits R1–R4 of this review were applied at integration, and the optional F4 corollaries were added (`not_thm7_6_printed_ne`, `not_thm7_6_printed_cce`); the optional F6 `m = 1` NE-oracle witness was not built. The index entry was drafted before integration and checked definitionally equal (rfl) to the reviewed `Thm7_6_restricted`. The review text below is otherwise unchanged.

I am an independent critic, not the builder. I reconstructed the source first, from `marl.tex`:
- model :15–54
- best response :119–129
- NE/CCE :213–238
- generative model :307–315
- gap :327–346
- plug-in algorithm and oracle :355–380
- Theorem 7.6 :384–399

I then read the builder's working files, the plan check (docs/critic-thm7-6-plan-check.md) and C45.

I edited nothing except this file and the probes in `<reviewer probe folder>/`.

## Verdicts

| Item | Verdict |
| --- | --- |
| `not_thm7_6_printed : ¬ Thm7_6_printed` | **ACCEPT.** This is a genuine refutation of the printed statement under the "any planning oracle" reading. `Thm7_6_printed` is not stronger than the printed text. |
| `thm7_6_restricted : Thm7_6_restricted` (C₁ = 400) | **ACCEPT as a `_restricted` variant.** The restriction to causal oracles is disclosed. All three clauses are genuine. Clause (a) is shown non-vacuous in Lean. Clauses (b) and (c) are non-vacuous mathematically but not in Lean (F6). |
| Compile / axioms | **PASS.** See §Evidence. |

Required edits are documentation and integration only (R1–R4). No theorem signature needs to change.

## Evidence (commands actually run, repo root, foreground, one at a time, no `-o`)

- **Snapshot.** `diff -r` of the builder's working folder against its reviewed snapshot shows them identical. All 14 sha256 prefixes match the builder's build-log final table, and every `.olean` is newer than its source.
- **Source pin.** `marl.tex` sha256 starts `8fadfab2c41e…`, which matches the plan pin.
- **Compile runs.** Each of these exited 0 with no errors and no `sorry`:
  - `bash scripts/lean-local.sh <builder working folder>/Marl76Restricted.lean`: exit 0 (3 s)
  - `… Marl76Refutation.lean`: exit 0 (3 s)
  - `… Marl76Nonvacuity.lean`: exit 0 (2 s)
  - `… <builder working folder>/AxiomProbe.lean`: exit 0
- **Axioms.** All five exports depend only on `[propext, Classical.choice, Quot.sound]`:
  - `thm7_6_restricted`
  - `not_thm7_6_printed`
  - `causalCCEOracle_exists`
  - `thm7_6_restricted_ccePlanner`
  - `stageCCE_exists`
- **Critic probe.** I ran `<reviewer probe folder>/CriticProbe.lean` (exit 0). It does the following:
  - `#print`s `Thm7_6_printed`, `CausalOracle`, `IsNE` and `IsCCE` as elaborated (no notation surprises), and `#check`s the key CE2 lemmas.
  - Repeats the axiom audit.
  - Checks `gapJ G (toJoint σ) = gap G σ`.

  Outputs are in `<reviewer probe folder>/*.out`.
- **Forbidden constructs.** `grep` for forbidden constructs (`sorry`, `admit`, `^axiom`, `native_decide`, `maxHeartbeats`, `implemented_by`, `extern`) in the reviewed snapshot of the `Marl76*.lean` modules found nothing.

## Findings

### F1. `Thm7_6_printed` faithfully transcribes the printed theorem under the any-oracle reading. It is not stronger than the printed text. (OK)

- **Constant first.** The statement opens with `∃ C₁ > 0`, and everything else is universally quantified after it. The oracles `One` and `Occe` are quantified after `G, N, δ, ε`. Universal quantifiers commute, so this equals "fix the oracle first". The oracles sit outside the probability.
- **Conclusion.**
  - The conclusion is the joint event `gap G (One Ĝ) ≤ ε ∧ gapJ G (Occe Ĝ) ≤ ε` with `1 − δ ≤ P(·)`.
  - The NE gap is the product-policy `gap` and the CCE gap is the joint-policy `gapJ`. Both are evaluated in the **true** game. Both are `max_s max_i (V^{⋆,π₋ᵢ}_{i,1}(s) − V^π_{i,1}(s))`, as in :332–342.
- **Threshold.** It is `C₁H³/ε² · log(S·H·N·∏A_i/δ) ≤ N`, with N inside the log, as at :393–395. The conditions `δ ∈ (0,1)` and `0 < ε ≤ √H` are as printed.
- **Rewards.** Rewards are required to lie in [0,1] only for `1 ≤ h ≤ H`. That is enough, because `value`/`valueJ … 1 H` read rewards and kernels only at steps 1..H. The kernel `P_H` is never used.
- **NE and CCE.**
  - Both are step-1 conditions (`value … 1 H`, for all `s, i`), as printed. NE uses the printed equality form.
  - The best response is the `iSup` over Markov deviations `S×[H]→Δ(A_i)`, matching :122–124. This iSup is bounded, because rewards are bounded, so there is no junk 0.
- **Empirical game.** It uses the true reward (:374). Step t uses the frequency of stage-(t−1) samples, which is consistent with `gameStages` (stage h samples `P_{h+1}`).
- **Sampling law.** It is the genuine product `Measure.pi` over all `(h,s,a,j)`, from the existing audited `FiniteHorizonGenerative.samplingLaw`.
- **Weakenings relative to the printed text** (each makes the Prop weaker, which is the safe direction for a refutation):
  - The added binders `0 < S`, `∀ i, 0 < A i` and `0 < N`.
  - Restricting oracles to deterministic maps from the empirical game.
  - The literal `∀ data` equilibrium hypothesis, which shrinks the class of admissible oracles.

### F2. The refutation is valid, with no junk-value exploitation. (OK)

- **The oracle returns an NE for every dataset.**
  - `oracle_isNE` holds for **every** game whose rewards are the CE2 rewards. Every empirical game has those rewards (`rfl`).
  - So the hypothesis holds for literally every dataset, including null-measure ones.
  - The CCE hypothesis is discharged by `IsNE.isCCE` with `Occe = toJoint ∘ oracle`.
- **The oracle reads only the empirical game.** Its output is a function of the empirical game alone: `B = supp P̂₁(·|s₀,(1,0))`, read from `G'.transition 1`.
- **The true gap.**
  - On `Good`, `stage1_risky` shows that the empirical continuation of (1,0) is 1 and that of a safe action is 1/2, so the argmax plays risky.
  - `gap_ge` then gives a true value of at most `|B|/(S−2)`, a deviation value of 1/2 for player 1 via safe, and `|B| ≤ N`.
  - So `gap ≥ 1/2 − N/(8N−2) ≥ 1/3 > 1/4`.
- **The bad event is null.** `good_ae` shows `P(¬Good) = 0` by a finite union of coordinate events of true probability 0, using the genuine marginal law.
- **The threshold holds for every C₁.**
  - With S = 8N, H = 2, ε = 1/4, δ = 1/2 and ∏A = 4, the argument of the log is `128N²` and the prefactor is `128C₁`.
  - For `N = n²` with `n = ⌈896C₁⌉₊+1`, `log(128n⁴) ≤ 7 + 4(n−1) ≤ 7n` and `896C₁ ≤ n`, so the threshold holds. This is valid for every `C₁ > 0`.
  - Also `ε = 1/4 ≤ √2`.
- **Conclusion.** The conclusion would need `1/2 ≤ P(…)`, but `P = 0`.
- **Additional observation (strengthens C45).**
  - The CE2 oracle output is in fact subgame-perfect in the empirical game: (0,0) and (1,1) are both stage NE at step 2 (`reward_two_update_le`), and step 1 is a team argmax.
  - So the counterexample does not depend on the step-1-only NE definition.
  - However, Lean proves only the step-1 `IsNE`. See F3.

### F3. C45 claims more than the Lean artifacts show. (Required doc edit R1)

- **What C45 asserts.** It currently asserts:
  - a *subgame-perfect* product NE
  - a zero-sum dummy-player example (CE1) with `gap ≥ 1 − 3N/K`
  - "No constraint on the type of equilibrium … rescues the statement"
  - "no Lean evidence yet"
- **What Lean proves.** Only CE2 with the printed step-1 NE/CCE.
- **Not in Lean.**
  - Subgame perfection is not stated as a Lean lemma, although it is easy to add from `reward_two_update_le` and `stage1_spec`.
  - CE1 is not formalized.
- **Fix.** On integration, C45 must state exactly what is Lean-checked and mark the rest as source-check evidence.

### F4. The refutation is of the joint conclusion. The NE-only and CCE-only readings are also refuted by the same witness, but this is not exported. (Optional)

`Occe = toJoint ∘ oracle` and `gapJ_toJoint` mean each conjunct fails on its own. Consider adding one-line corollaries, for example `not_thm7_6_printed_ne` and `not_thm7_6_printed_cce`, with single-clause printed Props. This would make the split NE/CCE structure from the plan check (docs/critic-thm7-6-plan-check.md) visible on the refutation side as well. It is not required, because the printed statement is joint.

### F5. `CausalOracle` and `CausalProductOracle` are faithful to the C45 restriction. They are not too strong for standard algorithms. (OK, disclosed)

- **The definition.** "Step-h output depends only on the kernels and rewards at steps ≥ h" is formalized as follows: for every pair of games that agree, for all `t ≥ h`, on `transition t` and `reward · t`, the outputs agree at step `h`.
  - This matches C45 ("policy at step h depends only on the empirical kernels from step h on").
  - Reading `P̂_h` itself at step h is correct and allowed.
- **Strength.**
  - Quantifying over all game pairs, rather than only empirical games of a fixed G, is a mild strengthening relative to `DataCausal`. `DataCausal` is what the proof actually uses, via `CausalOracle.dataCausal`.
  - The agreement premise also covers `t > H`, where empirical games copy G. That makes the premise harder to meet, so the condition is slightly easier to satisfy, which is harmless.
- **Which algorithms satisfy it.**
  - Backward-induction methods satisfy it: Nash VI with a fixed stage-equilibrium selector, and per-stage LP or no-regret with fixed initialization. `ccePlanner` proves this concretely.
  - Some algorithms may not satisfy it, for example a global LP over the whole game or trajectory-based no-regret.
  - The restriction is therefore a genuine restriction. It is correctly labelled "not claimed to be the weakest".
- **Policy-level only.** The empirical game always carries the true reward, so the reward agreement in the premise is automatic.

### F6. Clauses (b) and (c) are not shown non-vacuous in Lean. (Disclosure, non-blocking)

- **The gap.** No causal NE oracle is constructed, because Nash existence is not in Mathlib.
- **Why the clauses are still non-vacuous.** Mathematically they are non-vacuous: backward induction with a Nash stage selector is causal and Markov-perfect, so its output is a step-1 NE.
- **Clause (a).** It is instantiated in `thm7_6_restricted_ccePlanner`.
- **Fix.** COVERAGE and the statement docstring should say that the non-vacuity of (b) and (c) is not machine-checked.
- **Optional witness.** A cheap one is `m = 1`, where the greedy argmax backward induction is a causal NE oracle. It is not required.

### F7. Proof spot checks. (OK)

- **Gap decomposition.** `core` handles two data-causal maps that each return an empirical step-1 CCE. `gap_decomposition` is
  `V*_true − V_true ≤ (V^{br}_true − V^{br}_emp) + (V_emp − V_true)`,
  where `br` is the **true** greedy best response. It drops `V^{br}_emp − V_emp ≤ 0` using only the step-1 CCE inequality. Causality of `brPolicy` is proved (`brPolicy_congr`).
- **Union bound.** The index set is `EventIndex = Fin 2 × {i // 2 ≤ A i} × Bool × Fin H × Fin S × 𝒜`. `card_eventIndex` gives `4·m′·H·S·∏A`.
  - Each row uses `futureValue_row_bernstein` with η = δ/k.
  - The continuation value is the empirical-game value from step j+2. `value_factors_future` shows it is a function of strictly-future stages only.
  - The continuation value lies in [0, H] (`valueJ_mem_Icc`).
  - `log(4/η) = log(4k/δ)`.
- **Self-bounding.** `selfBound` consumes exactly the event's Bernstein form with `L = log(4k/δ)`.
- **Constants.** I recomputed the arithmetic by hand with `λ = ε/(8H²)` and `H³L ≤ 3Nε²/400`:
  - `λH² = ε/8`
  - `2HL/(λN) ≤ 0.12ε`
  - `(4/3)H²L/N ≤ 0.01ε`, using `ε² ≤ H`
  - The total is `2·0.255ε = 0.51ε ≤ ε`.
  - `H√(2L/N) ≤ √(6/400) < 1/2`.
- **Log absorption.** `16M·H·S·P/δ ≤ (SHNP/δ)³` holds when `H ≥ 2`, `P ≥ 2`, `2M ≤ P` and `δ < 1`.
- **Degenerate cases.**
  - H = 0 contradicts `0 < ε ≤ √0`.
  - With H = 1, the one-step values coincide in the empirical and true games, so CCE ⇒ gap ≤ 0.
  - If every `A_i = 1`, then best response = value.
- **Clauses.** Clauses (a) and (b) instantiate `core` with a duplicated map. Clause (c) uses one common event, so it gives the joint 1 − δ, not 1 − 2δ.

### F8. Non-vacuity infrastructure. (OK)

- **`stageCCE_exists`.** This is a genuine Hahn–Banach strict separation (`geometric_hahn_banach_compact_closed`) of the compact convex gain image from `{z ≤ 0}`, followed by the product-of-marginals identity. It contains no axioms and no hidden hypotheses.
- **`ccePlanner`.**
  - It is backward induction with a fixed `Classical.choose` selector.
  - `ccePlanner_causal` holds over all game pairs.
  - `ccePlanner_isCCE` holds for every game.

### F9. Integration hygiene. (Required R2–R4)

- **Imports.** `Marl76Defs.lean` imports `Formalization.MultiAgent.LowerBound.Product`, which is a proof module containing theorems. The statement index's `Ch7.lean` must import definition modules only. The existing `Ch7.lean` imports `Marl78Defs`. `Marl76Defs.lean` uses `value`, `bestResponseValue`, `valueJ`, `bestResponseValueJ`, `MarkovGame` and the Ch3 sampling definitions, and none of `toJoint`. The `Marl76*Defs` module should therefore import `Marl78Defs`, `MarlPrinted78` (or whatever provides `value`/`gap`) and `Statements.Ch3Definitions`, not `Marl78Product`.
- **Docstring.** The `Thm7_6_printed` docstring mentions only `0 < N`. It should also list `0 < S` and `∀ i, 0 < A_i`, and state that the oracles are deterministic maps of the empirical game, which is the "any oracle" reading.

## Required edits

- **R1 (`docs/SOURCE-ISSUES.md` C45, at integration).** Replace "no Lean evidence yet" with the exact Lean evidence:
  - `not_thm7_6_printed`: CE2, step-1 NE/CCE oracle, the joint conclusion fails for every C₁, with `P(gap ≤ 1/4) = 0`.
  - `thm7_6_restricted`: C₁ = 400, causal oracles.
  - Then state explicitly that subgame perfection of the CE2 output and the CE1 zero-sum example are source-check evidence only, not Lean.

  Alternatively, add a Lean lemma for subgame perfection before claiming it.
- **R2 (integration).** The definitions module for the statement index must not import `Marl78Product` or any other proof module (F9).
- **R3 (statement index).** Add `Thm7_6_restricted` to `Formalization/Statements/Ch7.lean`, self-contained, with a docstring that:
  - cites `marl.tex:384–399`
  - states the differences from the printed result: causal oracles, the added domain binders `0 < S`, `0 < A_i` and `0 < N`, and the `∀ data` equilibrium hypothesis
  - links C45
  - notes that (b) and (c) are not shown non-vacuous in Lean (F6)

  The proof wrapper goes in `Ch7Proofs.lean` and applies `thm7_6_restricted`.
- **R4 (docstring).** Expand the `Thm7_6_printed` docstring as described in F9.
- **Optional.** F4 split refutation corollaries; F6 `m = 1` NE-oracle witness.

## Not checked / limits

- I did not rebuild the imported `.olean`s. I relied on the builder's final sequential rebuild, which I confirmed by timestamps and matching hashes, and I re-elaborated the four requested files against them.
- I spot-checked the internals of `Marl76Eval.lean`'s self-bounding and total-variance induction through their statements and how they are consumed, not line by line. The kernel accepted them with a clean axiom closure.
- No author approval is implied.
