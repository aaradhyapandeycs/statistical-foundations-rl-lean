# Critic review: corrected Theorem 7.5 (`thm:chi2-lower-bound`), WIP `Thm75Wip`

Public copy of the independent critic report; local paths removed.

Post-review note (added to this public copy, 2026-11-07): findings 1–3 of this round-1 review were addressed in the revision reviewed in round 2; see docs/critic-thm7-5-revision.md. The review text below is unchanged.

Critic: independent (not the builder). Date: 2026-11-07. Nothing outside this report and
`<reviewer probe folder>/` was edited.

## Verdict

**The proof is sound. The correction is not minimal, so it is not accepted as written.**

* `Thm75Wip.thm7_5_corrected : Thm7_5_corrected` compiles from the stated inputs. Its axioms are
  `propext`, `Classical.choice` and `Quot.sound` only. Hard instances, the χ² ball, the exact
  robust value, the sampling law and the constant chain all check out (§3).
* `Thm7_5_printed_at` matches the tex binder by binder (§1). `Thm7_5_corrected_at` is `rfl`-equal
  to the printed body plus the three added hypotheses. I re-proved this against my own
  transcription written from the tex.
* **Blocking (High), Finding 1:** two of the three added hypotheses are redundant for the Lean
  Prop. I proved in Lean that the printed body holds with **only `2 ≤ card Action`** at the
  builder's constants (`Crit75.minAt_explicit`). `0 < ε` is never needed. `2 ≤ card State` is
  not needed in the reward-blind Lean class. It *is* needed under the book's known-reward
  convention (`Crit75KR.kr_one_state_fails`). This is the same situation as the accepted
  Theorem 7.3 precedent, which the present statement does not follow.

## Inputs and hashes

| file | sha256 |
|---|---|
| `source/upstream/tex/chapters/robust_RL.tex` | `95ce19a9bcdb275c9d4c04e4b20e836c8e5f0965426e955999817e82141196d9` |
| `<builder working folder>/Thm75Wip/Statement.lean` | `ef4fddcc4c31c159b078c96c868db87ccd1b07c6f2a8ce90d8bbeb61fdd7d67c` |
| `<builder working folder>/Thm75Wip/ChiValues.lean` | `1146554ed543b830cb85c1b798482c001a5c01baabf71bbcbd3b04a6ea5b4703` |
| `<builder working folder>/Thm75Wip/Params.lean` | `c138165bc77d206391f8adbb302f7e3a9a11a9d4ae161775fb18b00cd8c75bb0` |
| `<builder working folder>/Thm75Wip/Bounds.lean` | `dda19d28130686ab61aad254585171f6ea7154376c34dec48055689432d02264` |
| `<builder working folder>/Thm75Wip/LowerBound.lean` | `4bdbfb8a9adb73ed8105d38f10b43188757f2f81c87fe343daae6475b3d87f1d` |
| `<builder working folder>/PAPER-PROOF.md` | `fb02571e79e43b66a9aa1f395675b52c33db7d1f34879e711ce6be087836ef05` |
| `<builder working folder>/AxiomProbe.lean` | `eea1ddcff27e62295067613e2c9c8dbc81617a84da605709bb07740873a0a89a` |
| critic probe `<reviewer probe folder>/Critic75.lean` | `ddddccc8106839d9ca57b3575127eb9eb8f54d22e71711e6b95073df4db4a872` |
| critic probe `<reviewer probe folder>/CriticKR.lean` | `5cad3176d9f85d1b0ead7da08f3779bd54986f3efe60068216543372067c71fa` |

The WIP hashes match `BUILD-LOG.md`.

## Commands run

Each command was run in the foreground, one at a time, with no `-o`, and without lake or lean-lsp.

1. `bash scripts/lean-local.sh <builder working folder>/Thm75Wip/LowerBound.lean`
   gave exit 0 in 8s with empty output (no errors and no warnings; log at
   `<reviewer probe folder>/relab-LowerBound.out`). A grep of `Thm75Wip/` for
   `sorry|admit|axiom|native_decide|implemented_by|extern|unsafe|set_option` found nothing.
2. `bash scripts/lean-local.sh <reviewer probe folder>/Critic75.lean` gave exit 0
   in 15s (after two failed iterations of the critic's own proof script). `#print axioms`
   reports only `[propext, Classical.choice, Quot.sound]` for `Crit75.printed_rfl`,
   `Crit75.minAt_explicit`, `Crit75.min_implies_corrected`, `Crit75.singleton_action_fails` and
   `Thm75Wip.thm7_5_corrected`.
3. `bash scripts/lean-local.sh <reviewer probe folder>/CriticKR.lean` gave exit 0
   in 11s (after one failed iteration). `Crit75KR.kr_one_state_fails` depends only on
   `[propext, Classical.choice, Quot.sound]`.

Skipped: full `lake build`, `scripts/check.py` and the integration build. The files are still
WIP and outside `Formalization/`.

## 1. Printed statement vs tex (`robust_RL.tex:461–480`)

Reconstructed independently from the tex before reading the Lean.

| tex | `Thm7_5_printed_at` | status |
|---|---|---|
| "for some small universal constant c₃>0" (:465), "for some universal constant c₄>0" (:478) | `Thm7_5_printed := ∃ c₃ c₄, 0<c₃ ∧ 0<c₄ ∧ body` | OK (see note below) |
| any `(S,A,γ,σ,ε)` | `∀ State Action [Fintype] [Nonempty] γ σ ε` | OK. `S = {1..S}` makes nonemptiness implicit |
| `γ ∈ [3/4,1)` | `3/4 ≤ γ → γ < 1` | OK |
| `σ ∈ (0,∞)` | `0 < σ` | OK |
| `ε ≤ c₃/(1−γ)`, no sign condition | `ε ≤ c₃/(1-γ)` | OK. **No `ε > 0` is printed**, unlike 7.3 (:386, `ε ∈ (0, …]`) |
| `N ≤ c₄/((1−γ)³ε²)·(1+σ/(1−γ))` | `(N:ℝ) ≤ c₄/((1-γ)^3*ε^2)*(1+σ/(1-γ))` | OK, exact shape |
| ∃ two RMDPs, `μ`, χ² divergence, discount `γ` | `∃ M₀ M₁ μ, M₀.discount = γ ∧ M₁.discount = γ`, balls `chiBall`, radius `σ` | OK |
| N i.i.d. samples per `(s,a)` from the nominal kernel | `ModelBasedPolicyLearning.samplingLaw M N` (product of nominal rows) | OK |
| `inf_π̂ max{P₀(gap>ε), P₁(gap>ε)} ≥ 1/8` | `∀ est : Samples → StationaryPolicy, 1/8 ≤ max(P₀.real{ε < gap₀}, P₁.real{ε < gap₁})` | OK. Strict `>` and `1/8` are preserved |

**Constants.** The ∃-in-front reading is the natural one. It is not weaker than the alternative
"for every sufficiently small c₃, c₄": the body is antitone in both constants, and the builder
proves exactly that (`corrected_at_mono`, plus `thm7_5_corrected_at` for every
`c₃ ≤ 1/512, c₄ ≤ 1/5308416`). The two readings are therefore equivalent here.

**Lean junk at ε = 0.** `ε² = 0` makes `c₄/0 = 0`, so the budget becomes `N ≤ 0`, that is,
`N = 0`. This produces neither vacuity nor falsity: the instance asks for a positive-gap lower
bound with no data, which is true when `A ≥ 2` (proved in `minAt_explicit`). When `ε < 0` the
budget is finite and the claim is trivially true, because `gap ≥ 0 > ε` and the samplingLaw is
a probability measure (`Crit75.gap_nonneg`).

## Findings

1. **High (minimality / process).** At `Statement.lean:55–59` (`Thm7_5_corrected_at`) and
   `LowerBound.lean:59–60`, the hypotheses `0 < ε` and `2 ≤ Fintype.card State` are redundant
   for the Lean Prop.
   * Evidence: `Crit75.minAt_explicit : MinAt (1/512) (1/5308416)`. Here `MinAt` is the printed
     body with only `2 ≤ Fintype.card Action` added, and
     `Crit75.min_implies_corrected : MinAt c₃ c₄ → Thm7_5_corrected_at c₃ c₄`. The proof has
     three cases:
     * `S ≥ 2, ε > 0` uses the builder's theorem.
     * `ε < 0`: the event is `univ` (`gap_nonneg` and `probReal_univ`), and the models come from
       the builder's theorem at `ε' = c₃/(1−γ)`, `N = 0`.
     * `ε = 0`: the junk budget forces `N = 0`. Apply the builder's theorem at
       `ε' = c₃/(1−γ) > 0` and `N = 0`, then use `{ε' < gap} ⊆ {0 < gap}` and `measureReal_mono`.
     * `S = 1` uses the two one-state models `Thm73Wip.singleMDP a₀/a₁`, which share the
       point-mass kernel and have rewards `1[a = a_j]`. A new χ² one-state value lemma
       `Crit75.chi_single_value` gives `V = π(g|s)/(1−γ)`, the two laws coincide
       (`single_test_sum`), and `max ≥ 1/4`.
   * The critic did not fully prove one point. `minAt_explicit` holds only at the explicit
     constants. Getting the ∃-version requires composing with `corrected_at_mono`-style
     monotonicity for `MinAt`. That step is routine but was not written.
2. **High (fidelity disclosure / consistency with the 7.3 precedent).** The `S = 1` case holds in
   Lean only because estimators are reward-blind and `M₀, M₁` may differ in reward. The
   known-reward convention is stated at `generative_model_model_based.tex:31` ("Unless otherwise
   noted, … reward function is fully known"), and the RMDP tuple at `robust_RL.tex:25` fixes
   `r`. Under that convention, `S ≥ 2` is necessary.
   * Evidence: `Crit75KR.kr_one_state_fails`. For every `c₃, c₄ > 0`, the printed body with
     `2 ≤ A` and the extra conclusion `M₀.reward = M₁.reward` is false at `State = Unit`,
     `Action = Fin 2`, `γ = 3/4`, `σ = 1`, `ε = c₃/4`, `N = 0`. Take the estimator
     `detPolicy(argmax r)`. Then `robustOptimalValue ≤ robustPolicyValue`, because the one-state
     χ² value is `E_π r/(1−γ)` (`Crit75KR.val_single`), so both error events are empty.
   * The builder's hard pair does share the reward: `(hardMDP h a₀ …).reward = (hardMDP h a₁ …).reward`
     holds by `rfl` (checked in `Critic75.lean`). The known-reward variant is therefore one `rfl`
     away from the existing proof.
   * The accepted 7.3 statements (`Formalization/Statements/Ch7.lean:131–203`) handle this
     already: `Thm7_3_corrected` adds only `A ≥ 2` and discloses the reward-blind `S = 1` case,
     and `Thm7_3_corrected_knownReward` adds `S ≥ 2, A ≥ 2` together with
     `M₀.reward = M₁.reward`. Theorem 7.5 should mirror this.
3. **Medium (SOURCE-ISSUES C7 accuracy).** `docs/SOURCE-ISSUES.md` lines 206–228 propose
   `ε > 0` as part of the correction, citing the division by `ε²`. In the Lean transcription the
   printed claim is true for every `ε ≤ 0` (Finding 1), so `ε > 0` is not a correction needed
   for truth. At most it is a well-definedness remark about the printed expression. C7 should
   also record three Lean-checked facts:
   * `A ≥ 2` is necessary for every pair of positive constants (`Crit75.singleton_action_fails`,
     at `Fin 2` states, `Unit` actions, `γ = 3/4`, `σ = 1`, `ε = c₃/4`, `N = 0`). This
     independently confirms C7's `A = 1` claim for χ², with `S = 2`.
   * `S ≥ 2` is necessary under known rewards (`kr_one_state_fails`) but not in the reward-blind
     class.
   * `ε > 0` is not needed in either class.
     * Reward-blind class: covered by Finding 1.
     * Known-reward class: the same `ε ≤ 0` reductions apply, because they reuse the builder's
       shared-reward models. This was argued, not separately compiled.
4. **Low (quantifier order, informational).** `∀ N, … → ∃ M₀ M₁ μ` lets the models depend on
   `N`. The tex (:467–470) can also be read as fixing the models for given `(S,A,γ,σ,ε)` and
   requiring every admissible `N` to work. The `∀N∃M` form is the standard fixed-`N` minimax
   reading, it matches the accepted 7.3 transcription, and the builder's models do not depend on
   `N`, so the stronger `∃M ∀N` form is also available. Optionally disclose this.
5. **Low (estimator class).** Estimators are deterministic maps `Samples → StationaryPolicy`.
   Randomized estimators are covered by averaging, since the per-realization bound
   `P₀(E₀)+P₁(E₁) ≥ 1/4` survives mixing. The policy class is stationary randomized, as in the
   library definitions (already reviewed). There is no action item beyond an optional docstring
   sentence.
6. **Info (definitions).** No defects found.
   * `chiBall = QLearning.qChiBall`: `q ≪ p` (`∀x, p x = 0 → q x = 0`), and
     `χ²(q‖p) = Σ_{p x>0} (q x − p x)²/p x`. This is `∫(dQ/dP − 1)² dP` with the nominal `P⁰`
     as reference, the correct orientation for `ρ(P_{s,a}, P⁰_{s,a})` (`intro.tex:229–234`,
     `robust_RL.tex:41–46`).
   * `robustPolicyValue` is the `sInf` of actual trajectory values over rectangular admissible
     kernels. `chi_hard_robustPolicyValue` proves equality by `le_antisymm` with explicit
     `BddBelow`, a lower bound over every admissible `K` (sub-solution comparison), and an
     admissible attaining `Kstar`. The infimum is therefore well-defined and attained.
   * The gap uses only `V^π ≤ V^⋆` (`robustPolicyValue_le_optimal`, with `BddAbove` by
     `1/(1−γ)`).
   * Hard models: the reward `if s = s₀ then 0 else 1 ∈ [0,1]`, and rows are `twoRow` values.
     Their `clamp01` is applied only to arguments in `[0,1]`: `ℓ ∈ (0,1)` and `T ∈ [0,ℓ]` by
     `ChiPair`.
   * `chi_lower` computes `χ² = (q₁−ℓ)²/(ℓ(1−ℓ))` and from it `q₁ ≥ T`. `chi_attain` gives
     `χ² = σ` exactly.

## 3. Constant chain (PAPER-PROOF §3–5), re-derived by hand

* `T(u) = u(u−s)/(1+u²) = h/(1+u²)`, because `u² = su + h`. Also
  `ℓ − T = sv/(1+v²) ≥ 0` and `(ℓ−T)² = σℓ(1−ℓ)`. Correct.
* `h + γa ≤ h + (3/2)h` and `h + γL ≤ 5h/2`. With `a − L ≥ D/2 ≥ 16h²ε`:
  `gap = γ(a−L)/((h+γa)(h+γL)) ≥ (3/4)(16h²ε)/((25/4)h²) = (48/25)ε > ε`. Correct.
* `162·K²·c₄ = 162·16384/5308416 = 2654208/5308416 = 1/2 < log 2`. Correct, and `test_budget`
  compiles.
* `Khε ≤ 1/4` follows from `hε ≤ 1/512` with `K = 128`. Correct.

## Minimality recommendation

* Reward-blind Lean class (the current Prop shape): the weakest correct hypothesis set is
  **{`2 ≤ card Action`}**. It is Lean-proved sufficient here and necessary
  (`singleton_action_fails`).
* Known-reward reading (add `M₀.reward = M₁.reward` to the conclusion): the weakest set is
  **{`2 ≤ card State`, `2 ≤ card Action`}**. Both are necessary (`kr_one_state_fails`,
  `singleton_action_fails`, whose instance already has two states). Sufficiency follows from the
  builder's proof plus `rfl` and the `ε ≤ 0` reductions.
* Do not add `0 < ε` in either variant.

## Required edits (builder)

* R1. Change `Thm7_5_corrected_at` so it adds only `2 ≤ Fintype.card Action`, and prove it. The
  critic's `Crit75.minAt_explicit` (in `<reviewer probe folder>/Critic75.lean`) is a complete compiled
  proof at the explicit constants that the builder may adopt. Then restate monotonicity and the
  ∃-wrapper. Keep the docstring disclosure: the `S = 1` case holds only because estimators do
  not see the reward, and under known rewards the printed claim is false at `S = 1`.
* R2. Add `Thm7_5_corrected_knownReward` with `2 ≤ S`, `2 ≤ A` and `M₀.reward = M₁.reward` in
  the conclusion, worded as in `Thm7_3_corrected_knownReward`. Prove it with the existing
  construction (`rfl` for the reward) and the `ε ≤ 0` reductions.
* R3. Update `PAPER-PROOF.md` and SOURCE-ISSUES C7. Drop `ε > 0` from the proposed correction
  (or mark it as a non-needed well-definedness note). Record that `S ≥ 2` is needed only under
  known rewards, and cite the critic probes as Lean evidence for the `A = 1` and known-reward
  `S = 1` failures.
* R4. Re-run the `rfl` probe against the new statement(s). Then submit for a delta review.
  Status must say "corrected, not author-approved". `Thm7_5_printed` stays unproved and is
  false at `A = 1`.
