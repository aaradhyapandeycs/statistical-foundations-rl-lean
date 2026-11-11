# Critic review (round 2): revised corrected Theorem 7.5 (`thm:chi2-lower-bound`), WIP `Thm75Wip`

Public copy of the independent critic report; local paths removed.

Critic: independent (not the builder). Date: 2026-11-07. This review follows up
`docs/critic-thm7-5-corrected.md`, which raised R1–R4. I edited nothing outside this report and
`<reviewer probe folder>/`.

## Verdicts

| entry | verdict |
|---|---|
| `Thm7_5_printed_at` / `Thm7_5_printed` | **ACCEPT.** Unchanged from round 1. `Thm75Wip.printed_at_fails` refutes it for every `c₃, c₄ > 0`. |
| `Thm7_5_corrected_at` / `Thm7_5_corrected` | **ACCEPT, after the docstring edit E1.** The body is the printed body plus exactly `2 ≤ Fintype.card Action`. R1 is resolved. |
| `Thm7_5_corrected_knownReward_at` / `Thm7_5_corrected_knownReward` | **ACCEPT, after E1.** The body is the printed body plus exactly `2 ≤ S → 2 ≤ A →` and the conjunct `M₀.reward = M₁.reward`. R2 is resolved. |
| `knownReward_needs_two_states`, `knownReward_needs_two_actions`, `printed_at_fails` | **ACCEPT.** Each refuted Prop is exactly the known-reward or printed body minus one hypothesis, and the witnesses are honest. |
| Proof (`core_explicit`, `kr_nonpos`, `one_state_explicit`, monotonicity, ∃ forms) | **ACCEPT.** It is sound and genuine. The ε = 0 handling is honest and disclosed (§2). |
| `PAPER-PROOF.md` | **ACCEPT.** R3 is resolved. §6–§7 match the Lean proofs. |
| Probes, `AxiomProbe.lean` | **ACCEPT.** R4 is resolved. My re-run output is byte-identical to `axiom-probe.out`. |

**Overall:** accepted for integration, subject to E1 (citation range) and the integration items
I1–I3. Nothing is blocking on the mathematics.

## Inputs (sha256)

All WIP hashes match the "Revision R1–R4" table in `BUILD-LOG.md`.

| file | sha256 |
|---|---|
| `source/upstream/tex/chapters/robust_RL.tex` | `95ce19a9bcdb275c9d4c04e4b20e836c8e5f0965426e955999817e82141196d9` |
| `Thm75Wip/Statement.lean` | `9c4b64c0e110d0249be18c40e9a635f978447e70d2abf7777ab60c720208d9fb` |
| `Thm75Wip/ChiValues.lean` | `1146554ed543b830cb85c1b798482c001a5c01baabf71bbcbd3b04a6ea5b4703` |
| `Thm75Wip/Params.lean` | `c138165bc77d206391f8adbb302f7e3a9a11a9d4ae161775fb18b00cd8c75bb0` |
| `Thm75Wip/Bounds.lean` | `dda19d28130686ab61aad254585171f6ea7154376c34dec48055689432d02264` |
| `Thm75Wip/LowerBound.lean` | `7d5713cd607a01838b27dfb4b320256af045eac8eaed861521d6ddb492237c11` |
| `Thm75Wip/Main.lean` | `7082d76b125952b1a495f234ad334ce68f76c7caf506812531ceca91a3d4f870` |
| `Thm75Wip/Necessity.lean` | `19c506ad0094d59d2a6ff2e4eff5f6c529d0def6c69a97491dab821fd0f7d042` |
| `AxiomProbe.lean` | `3a2cf9fccdceb541a6738e162ba0c08945f27358fb1c478d6b7e563ceb096641` |
| `axiom-probe.out` | `2097e2a019787324492c8dc4477cd6c9da53a2e7ec9e3de8fbc61c99cd563059` |
| `PAPER-PROOF.md` | `dc38d6ecaa8b65c15311c30481e03b9bb71239c31fcaf89b48ca17c1cc0cf4b2` |
| critic probe `<reviewer probe folder>/Critic75b.lean` | `b2d1f9e7bfe9062cb4c5bcf671fbdc71d011f6cfc64b8db57d5672c0f3b40d50` |
| critic probe output `<reviewer probe folder>/critic75b.out` | `828af068be35cae189e5e0141d769ea014bb60a157f2240c864f1e663e6cc9c5` |

The WIP imports `Thm73Wip.{Values,Testing,SingleState}`. I diffed these against the integrated
`Formalization/RobustRL/Ch7/LowerBound73{Values,Testing,SingleState}.lean`, ignoring import lines
and the namespace rename. The only differences are the "(WIP)" suffixes in the module headers.

## Commands run

Each command was run in the foreground, one at a time, with no `-o`, and without lake or lean-lsp.
The project oleans for `Thm75Wip/*` and `Thm73Wip/*` are newer than their sources.

1. `bash scripts/lean-local.sh <builder working folder>/Thm75Wip/Main.lean`: exit 0,
   19 s, empty output (no errors or warnings).
2. `bash scripts/lean-local.sh <builder working folder>/Thm75Wip/Necessity.lean`:
   exit 0, 2 s, empty output.
3. `bash scripts/lean-local.sh <builder working folder>/AxiomProbe.lean`: exit 0, 10 s.
   The output is byte-identical to the builder's `axiom-probe.out`. All 13 lines report
   `[propext, Classical.choice, Quot.sound]`.
4. `bash scripts/lean-local.sh <reviewer probe folder>/Critic75b.lean`: exit 0,
   9 s, first attempt. All `#print axioms` lines report `[propext, Classical.choice, Quot.sound]`:
   `Crit75b.rfl_printed`, `rfl_corr`, `rfl_kr`, `rfl_noS`, `rfl_noA`, `eps0_anyN`,
   `Thm75Wip.thm7_5_corrected`, `thm7_5_corrected_knownReward`, `knownReward_needs_two_states`,
   `knownReward_needs_two_actions` and `printed_at_fails`.

A grep of `Thm75Wip/` and `AxiomProbe.lean` for
`sorry|admit|axiom|native_decide|implemented_by|extern|unsafe|set_option` matched nothing.

Skipped: `lake build`, `scripts/check.py` and the integration build. The files are still WIP.

## 1. Statement diffs (mechanical)

I extracted each `def` body from `Statement.lean` and `Necessity.lean` with awk and compared them
with `diff`.

* `Thm7_5_printed_at` vs `Thm7_5_corrected_at`: one line inserted,
  `2 ≤ Fintype.card Action →`. Nothing else differs.
* `Thm7_5_printed_at` vs `Thm7_5_corrected_knownReward_at`: two differences.
  * Inserted: `2 ≤ Fintype.card State → 2 ≤ Fintype.card Action →`.
  * Changed: `M₀.discount = γ ∧ M₁.discount = γ ∧` became the same line followed by
    `M₀.reward = M₁.reward ∧`.
* `Thm7_5_corrected_knownReward_at` vs `Thm75Wip.Thm7_5_knownReward_noTwoStates_at`: only the
  `2 ≤ Fintype.card State →` hypothesis is removed.
* `Thm7_5_corrected_knownReward_at` vs `Thm75Wip.Thm7_5_knownReward_noTwoActions_at`: only the
  `2 ≤ Fintype.card Action →` hypothesis is removed.
* `KRConclusion` (`LowerBound.lean`) is textually the conclusion of the known-reward body.

`rfl` probes (`Critic75b.lean`). I wrote one parametrized transcription of the tex body at
`robust_RL.tex:461–480`, independently of the builder's probe. Specialized with the
hypotheses ∅, `{A}`, `{S, A} + reward` and the two one-hypothesis-removed variants, it is
`rfl`-equal to `Thm7_5_printed_at`, `Thm7_5_corrected_at`, `Thm7_5_corrected_knownReward_at`,
`Thm7_5_knownReward_noTwoStates_at` and `Thm7_5_knownReward_noTwoActions_at`. The wrappers
`Thm7_5_{printed,corrected,corrected_knownReward} = ∃ c₃ c₄, 0<c₃ ∧ 0<c₄ ∧ _at c₃ c₄` are `rfl`
(builder's `probe_wrappers`, re-run).

The new statements mirror the accepted `Thm7_3_corrected_at` / `Thm7_3_corrected_knownReward_at`
(`Ch7PrintedStatements.lean:150–216`) in binder order, insertion point and the shared-reward
conjunct.

## 2. New cases and restructuring

* **`core_explicit`** (`LowerBound.lean`) is the round-1 proof with a new conclusion type,
  `KRConclusion`. The hard pair is
  `hardMDP hs a₀ … , hardMDP hs a₁ …` with `μ = pointMass s₀`, and `rfl, rfl, rfl` discharges the
  discount and reward clauses. So the shared reward really is definitional: both models use the
  same `lg, lb, hs`, and only the good action differs. The constants and the
  `hard_test_sum`/`chi_gap_event` chain are unchanged from round 1 (`Params`, `Bounds` and
  `ChiValues` hashes are unchanged).
* **ε < 0** (`kr_nonpos`, first branch). `gap_nonneg` (`V^π ≤ V^⋆` via
  `robustPolicyValue_le_optimal` and `qChiBall_self`) makes the event `univ`, and
  `probReal_univ = 1 ≥ 1/8`. The models come from `core_explicit` at `ε' = (1/512)/(1-γ) > 0`
  and `N = 0`, which keeps the shared reward. They are then used at the actual `N`, which is
  legitimate because the event is `univ` under any probability measure. Genuine.
* **ε = 0** (second branch). `hN` simplifies to `(N:ℝ) ≤ 0` (Lean `x/0 = 0`), so `N = 0`. Then
  `core_explicit` at `ε'` and `N = 0` is weakened by `{ε' < gap} ⊆ {0 < gap}` and
  `measureReal_mono`. This uses the junk value only to the extent that the printed
  statement's own Lean transcription forces it: at ε = 0 the Lean budget is literally `N ≤ 0`,
  and the printed Prop and both corrected Props contain the same instance. **Honesty check**
  (`Crit75b.eps0_anyN`, compiled): under the extended-real reading `c₄/0 = ∞` (no budget), the
  known-reward conclusion at ε = 0 still holds for every `N`. The proof takes `core_explicit` at
  `ε'' = 1/(5308416(N+1))`, which is admissible for that `N`, and then applies the same inclusion.
  So the junk reduction never turns a false instance into a true one; it only makes the ε = 0
  instance weaker. The `Thm7_5_corrected_at` docstring and `PAPER-PROOF.md` §6 disclose it
  ("at ε = 0 the Lean value `c₄/0 = 0` of the budget forces `N = 0`, a case that is proved").
  This is adequate. Optional E3 below.
* **S = 1** (`one_state_explicit`) holds only in the reward-blind class.
  * Construction: `singleMDP a₀/a₁` (shared self-loop, rewards `1[a = a_j]`).
  * `chi_single_value` gives `V^π = π(g|s)/(1-γ)`. The proof is genuine: it is a
    `valueFixedPoint_characterization` argument over all admissible `K`, using `csInf_singleton`.
  * `chi_single_gap` gives a gap of at least `1/(2(1-γ)) > (1/512)/(1-γ) ≥ ε` whenever
    `π(g) ≤ 1/2`.
  * `single_test_sum` (integrated `LowerBound73SingleState`) supplies the testing step.
  * No budget hypothesis is used, which is correct because the data are uninformative.
* **Assembly.** `thm7_5_corrected_at_explicit` splits on `2 ≤ card State`. The S ≥ 2 branch
  reuses the known-reward theorem and drops the reward conjunct; the other branch is
  `one_state_explicit`. `corrected_at_mono` and `corrected_knownReward_at_mono` are correct
  (antitone in `c₃, c₄`, using `1-γ > 0` and `(1-γ)^3 ε^2 ≥ 0`). The ∃ forms are instantiated at
  `1/512` and `1/5308416` with `norm_num` positivity.

Non-vacuity is shown by the builder's `S = 1, A = 2, ε = −1` and `S = A = 2, ε = 0` examples,
and by my `S = A = 2, γ = 3/4, σ = 1, ε = 1/1000, N = 0` example on the `ε > 0` core branch.
All three compile.

## 3. Necessity theorems

* **`knownReward_needs_two_states c₃ c₄ (hc₃ hc₄)`**
  * Statement: `¬ Thm7_5_knownReward_noTwoStates_at c₃ c₄`, for all positive constants.
  * Witness: `Unit`, `Fin 2`, `γ = 3/4`, `σ = 1`, `ε = c₃/4 > 0`, `N = 0`.
  * Every hypothesis is discharged genuinely, including `ε ≤ c₃/(1/4)`.
  * Argument: `val_single` gives `V^π = E_π r/(1-γ)` for any one-state model, so
    `detPolicy (argmax r₀)` is robust-optimal in both models because they share the reward.
    Both events are empty, and `max 0 0 < 1/8`.
  * The refutation uses only the shared-reward conjunct and S = 1, as intended.
* **`knownReward_needs_two_actions`**
  * Witness: `Fin 2` states (`2 ≤ S` holds), `Unit` actions.
  * Argument: every policy equals every other (`prob_eq_one_of_subsingleton`), so the gap is 0.
* **`printed_at_fails`**
  * Same witness, on the printed body.
  * It implies `¬ Thm7_5_printed` (builder's `probe_not_printed`).

No witness uses ε ≤ 0 or a junk budget. Each uses ε > 0, so the events are empty for genuine
reasons.

## 4. Docstrings

These are accurate and mirror 7.3 nearly word for word. They cover the S = 1 reward-blind
disclosure, the known-reward S ≥ 2 explanation, the "no ε > 0 added" explanation, the C7
pointer, the `generative_model_model_based.tex:31` and `robust_RL.tex:25` citations, and the
χ²/sampling citations (`:19–157`, `:135–147`). The known-reward docstring is stronger than 7.3's,
because the S = 1 necessity here is machine-checked rather than a paper argument. That is
correct. The exceptions:

* **E1 (Required, Low).** `robust_RL.tex:206–212` appears at `Statement.lean:8`, `:64` and `:94`.
  The 7.3 review corrected the same citation to `:206–215`. Lines 213–215 contain the empirical
  RMDP display `\widehat{\cM}_{\mathsf{rob}} = \{\cS,\cA,\gamma,\cU^\ror(\widehat P^\no), r\}`,
  which is exactly the line showing that the reward `r` is reused, that is, known. Change all
  three occurrences to `robust_RL.tex:206–215`.
* **E2 (Optional).** In `Thm7_5_corrected_at`'s S = 1 bullet, "the printed claim is false at
  `S = 1`" could add the pointer `(knownReward_needs_two_states)`, as `PAPER-PROOF.md` does.
* **E3 (Optional).** After the ε = 0 sentence in `Thm7_5_corrected_at`, add one sentence: under
  the reading `c₄/0 = ∞` the ε = 0 instance also holds for every `N`, because the models may
  depend on `N`. That makes it explicit that the junk value only weakens the instance. If the
  claim is cited, port `Crit75b.eps0_anyN` or re-prove it.

## 5. Integration items (outside the WIP; not blocking this review)

* **I1.** Rename the imports `Thm73Wip.*` → `Formalization.RobustRL.LowerBounds.LowerBound73*` and the
  namespace `Thm73Wip` → `StatisticalRL.RobustRL.Ch7.LowerBound73`. Update the docstring
  reference "`Thm75Wip.Necessity`" (`Statement.lean:100`) to the integrated module name. Move the
  `def`s to `Ch7PrintedStatements.lean` beside 7.3.
* **I2.** `docs/SOURCE-ISSUES.md` C7 (lines 208–232) still proposes "`S ≥ 2`, `A ≥ 2`, and
  `ε > 0`" and says "no complete Lean proof … is claimed". It must be rewritten in the same
  change, as round-1 Finding 3 required. The new text should record:
  * `A ≥ 2` is necessary (`printed_at_fails`).
  * `S ≥ 2` is necessary only under known rewards (`knownReward_needs_two_states`).
  * `ε > 0` is not needed in either class.
  * Both corrected forms are proved.
* **I3.** C7 has no `<a id="C7"></a>` anchor, unlike C38 at line 1053. `Statement.lean:56`
  (`docs/SOURCE-ISSUES.md#C7`) and the existing `[C7](#C7)` link in C38 therefore do not
  resolve. Add the anchor.
* Statement index: add `Thm7_5_corrected` and `Thm7_5_corrected_knownReward` entries to
  `Formalization/Statements/Ch7.lean` and `Ch7Proofs.lean`, and update `docs/COVERAGE.md` in the
  same change, as AGENTS.md requires. The entries should be self-contained Props with the
  `robust_RL.tex:461–480` citation and a C7 pointer.

## Informational (carried from round 1, unchanged, not action items)

* The `∀ N ∃ M` quantifier order matches 7.3. The hard models do not depend on `N`. The S = 1
  models do not either.
* Estimators are deterministic maps `Samples → StationaryPolicy`. Randomized estimators are
  covered by averaging.
