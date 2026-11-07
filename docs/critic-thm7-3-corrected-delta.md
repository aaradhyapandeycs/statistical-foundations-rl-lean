# CRITIC (delta): corrected Theorem 7.3, dropping `S ≥ 2` (`robust_RL.tex:377–391`, C38)

Public copy of the independent critic report; local paths removed.

Critic: independent (did not build). Date 2026-11-07. Scope: the revision answering finding 1 /
R1–R2 of `docs/critic-thm7-3-corrected.md` (Statement, new SingleState, LowerBound, AxiomProbe,
PAPER-PROOF §5, BUILD-LOG "Revision").

## Verdict: ACCEPT WITH DISCLOSURES

`Thm73Wip.thm7_3_corrected : Thm7_3_corrected` is an axiom-clean proof of the printed
`Thm7_3_printed_at` body with exactly one inserted hypothesis `2 ≤ Fintype.card Action`. The
`S = 1` branch (`lb_one_state`) is genuine: no junk value, vacuity, or weakened conclusion.
Its truth depends on the Lean estimator class, which has no reward access. Under the book's
known-reward convention, `S = 1` is a counterexample to the printed theorem, not an instance of
it. This must be disclosed (Finding 3). The recommendation (below) is to keep the `A ≥ 2`-only
entry and add the known-reward disclosure.

## Inputs (sha256; all match BUILD-LOG "Revision")

| file | sha256 |
|---|---|
| Thm73Wip/Statement.lean | f043e1c524d46eaca80508372b527ec512241e7e26bd321a402c93e2fec75eee |
| Thm73Wip/SingleState.lean | 9675a761119b30a12d146c492fd00886dff5cc4bec117d7a8e35e06ed86b8627 |
| Thm73Wip/LowerBound.lean | 0cdbeff868e51360d4a4747681d38ed9ec88a917c33705ddf7c9333522b58555 |
| Thm73Wip/Values.lean (unchanged) | 1192c5300b8d554b3ef3dc206833cafe8709d9c81ce4efd9edc2dadbb0529ee5 |
| Thm73Wip/Testing.lean (unchanged) | 18b33d9c279c539403ff47bbc4edc9fbdc1bce50982e074b0c626ac08b6cf106 |

## Checks performed (repo root, foreground, one at a time, no `-o`; no lake, no lean-lsp)

1. `bash scripts/lean-local.sh <builder working folder>/Thm73Wip/{Statement,SingleState,LowerBound}.lean`:
   each exited 0 (3s / 4s / 27s) with empty output (no warnings, no errors). Olean mtimes
   (09:08:21 / 09:09:16 / 09:09:53) are later than the source mtimes (09:07:46 / 09:09:13 / 09:09:13).
2. `bash scripts/lean-local.sh <builder working folder>/AxiomProbe.lean`: exit 0. Its
   output is byte-identical to `axiom-probe.out`.
3. Critic probe (scratchpad `CriticDeltaProbe.lean`, sha256 `689806d7…3af54`, exit 0, 10s). Every
   `#print axioms` returns `[propext, Classical.choice, Quot.sound]` (8 declarations). It contains:
   * `critic_printed_unfold : Thm7_3_printed_at c₀ = (B) := rfl` and
     `critic_corrected_unfold : Thm7_3_corrected_at c₀ = (B') := rfl`. Here `B` is lines 126–139 of
     `Ch7PrintedStatements.lean`, extracted by `sed`. `B'` is `B` with one line,
     `2 ≤ Fintype.card Action →`, inserted after line 2 by `awk`. `diff B B'` = that one line only.
     Both `rfl`s close the gap between the extracted text and the actual printed definition, so
     the delta is exactly the one hypothesis. The builder's `probe_corrected_unfold` right-hand
     side also differs from the extracted printed body only by that line. R2 is resolved.
   * `critic_lbconcl : LBConclusion State Action γ σ ε N = <printed conclusion text> := rfl`.
     `LBConclusion` is definitionally the printed conclusion, not a weaker one. In any case,
     `thm7_3_corrected` has type `Thm7_3_corrected`, so the shape of `LBConclusion` cannot weaken
     what is proved.
   * The `S = 1` instance `lb_one_state` at `Fin 1, Fin 3, γ = 9/10, σ = 1/2, ε = 1/1000,
     N = 10⁶` is far above the printed N-bound. As expected, the `S = 1` case does not use the
     N-bound or `ε > 0`.
   * A concrete `single_robustPolicyValue` instance, and
     `(hardMDP h a₀ …).reward = (hardMDP h a₁ …).reward := rfl`. This confirms that the `S ≥ 2`
     models share the reward.
4. `grep sorry|admit|axiom |native_decide|implemented_by|extern|unsafe|set_option` in `Thm73Wip/`
   returns no hits.

## Review of the `S = 1` proof (`SingleState.lean`, `LowerBound.lean:213–267`)

* **Models are legitimate.** `singleMDP g γ` uses kernel `pointMass s` (a valid
  `FiniteDistribution`), reward `ell g 1 0 a = 1[a = g] ∈ {0,1}` (nonnegativity and `≤ 1` are proved
  in the structure), and discount `γ` (`rfl` gives `M_j.discount = γ`). The two models differ only
  in reward (`a₀` vs `a₁`, with `a₀ ≠ a₁` from `card A ≥ 2`). `μ = pointMass s`.
* **Robust value is the real `sInf`.** `single_robustPolicyValue` proves that the value set
  `{v | ∃ K, RobustAdmissible tvBall M σ K ∧ v = V^{π}_{M with K}(s)}` equals the singleton
  `{π(g|s)/(1-γ)}`, then applies `csInf_singleton`. Both inclusions are proved. Every kernel `K`
  on a subsingleton state space yields the constant `W` as the Bellman fixed point (via
  `valueFixedPoint_characterization` and `trajectoryExpectedValue_eq_valueFixedPoint`). The
  nominal kernel is admissible because `tvBall p σ ∋ p` for `σ ≥ 0`. The proof does not even need
  the ball to be a singleton: the value does not depend on the kernel.
* **The optimal-value lower bound is genuine.** It uses
  `HorizonTrap.robustPolicyValue_le_optimal` (the reviewed lemma: real `sSup`, bounded above and
  nonempty) with the deterministic policy `detPolicy (fun _ ↦ g)`, whose `prob g = 1`. That gives
  `V^{⋆,σ} ≥ 1/(1-γ)`.
* **The gap is strict.** `single_gap` gives `gap ≥ 1/(2(1-γ))` when `π(g|s) ≤ 1/2`, and
  `hεlt : ε < 1/(2(1-γ))` follows from `ε ≤ c₀/(256(1-γ)) ≤ 1/(2048(1-γ))`. The set membership
  `ε < gap` is therefore strict, matching the printed `>`.
* **Testing.** The kernels coincide, so `rowAff_self` gives 1 for every row. Then
  `samplingLaw_test_sum` (reviewed, unchanged Testing.lean) gives `P₀(E₀) + P₁(E₁) ≥ 1/2`, hence
  `max ≥ 1/4 ≥ 1/8`. The test is `1/2 < π̂(a₀|s)`. Its false branch gives `π̂(a₀) ≤ 1/2`, so
  `E₀` holds. Its true branch gives `π̂(a₁) < 1/2` via `π̂(a₀) + π̂(a₁) ≤ 1` (`Finset.add_le_sum`), so
  `E₁` holds.
* **Case split.** `thm7_3_corrected` splits on `card State < 2` (with `Nonempty` this gives
  `card = 1`, hence `Subsingleton`) or `card State ≥ 2`. The `S ≥ 2` branch is the previously
  reviewed `lb_two_states`, with an identical hypothesis list.

## Findings

1. **Medium (disclosure / fidelity): `S = 1` holds only because of the Lean estimator class, and
   the book's reading contradicts it.**
   `generative_model_model_based.tex:31` assumes "throughout" that the reward is known. Ch. 7
   inherits this: the empirical RMDP `{S, A, γ, U^σ(P̂⁰), r}` (`robust_RL.tex:~212`) uses the
   true `r`, and the RMDP tuple at `:25` fixes `r`. Under that reading, at `S = 1` (any `A`) an
   estimator that knows `r` plays `argmax r`. Every TV row on one state is the point mass, so its
   gap is 0 in both models, and the printed claim fails (probability `0 < 1/8`). So for the book,
   `S = 1` is a counterexample (C38), not a case of the theorem. `lb_one_state` instead proves a
   lower bound against reward-blind estimators, using two models that differ only in reward. This
   is true of the accepted transcription `Thm7_3_printed_at` (estimator `Samples → Policy`, models
   chosen independently). The current docstrings (`Statement.lean`) and PAPER-PROOF §5 say this
   correctly ("holds only because the estimator does not see the reward"; under known reward
   "degenerate"). They should also say plainly that the book's `S = 1` statement is *false*, not
   merely "degenerate".
2. **Low (unchecked claim in docstring).** `Statement.lean` says the `S ≥ 2` case "also holds
   under the book's known-reward convention". This is true by inspection: `hardMDP`'s reward
   `if s = s₀ then 0 else 1` does not depend on `g`, which the critic confirmed with `rfl`. But no
   Lean Prop states it, because `LBConclusion` does not expose `M₀.reward = M₁.reward`. Either
   mark it "(by inspection; not a separate Lean statement)" or add the variant in the
   Recommendation.
3. **Low (wording).** `Statement.lean` says the `S ≥ 2` models "differ in one transition row
   pair", while `LowerBound.lean` (`lb_two_states` docstring) says "differing in two transition
   rows". They differ at `(s₀,a₀)` and `(s₀,a₁)`. Use "two transition rows `(s₀,a₀),(s₀,a₁)`"
   consistently.
4. **Info.** C38 (`docs/SOURCE-ISSUES.md:1047–1058`) still proposes "A ≥ 2 and S ≥ 2" and says
   the correction "does not prove the cited bound". At integration, update it to say the
   following. Under the Lean (reward-blind) transcription, `A ≥ 2` alone suffices and is proved.
   Under the known-reward convention, `S ≥ 2` is also necessary, and the `S ≥ 2, A ≥ 2` proof
   uses shared rewards. Keep "Not author-approved". R3 of the first review still applies.
5. **Info.** The builder's `probe_printed_implies_corrected` is kept but is now redundant given the
   `rfl` probe. That is harmless.

## Recommendation (question 3)

**Keep the entry as `A ≥ 2` only (current `Thm7_3_corrected`).**

* AGENTS.md requires the corrected entry to state exactly what is proved, relative to the
  accepted transcription of the printed result. With respect to `Thm7_3_printed_at`, `A ≥ 2` is
  the minimal and complete correction. `A = 1` is refuted (`SingletonAction73.lean`) and every
  `A ≥ 2` case is proved.
* Re-adding `S ≥ 2` would not encode the known-reward convention. The Prop would still quantify
  over reward-blind estimators and independently chosen rewards. It would only state a strictly
  weaker theorem with a hypothesis the Lean statement does not need. That adds no faithfulness
  and hides a proved case.
* The book's convention is a property of the estimator class or model pair. It cannot be captured
  by restricting `S`. If faithfulness to it is wanted, the right form is a separate entry, e.g.
  `Thm7_3_corrected_knownReward`, with `2 ≤ S`, `2 ≤ A`, and `M₀.reward = M₁.reward` added to the
  conclusion (or `est` taking the reward as input). It is directly derivable from the
  `lb_two_states` construction (shared reward by `rfl`, as shown above), with a small
  strengthening of the existential. This is advised but not blocking.
* Required at integration: in the `Thm7_3_corrected` docstring and C38, state the following.
  (a) The `S = 1` case is a property of the reward-blind estimator class and does not correspond
  to the book's setting, where the printed claim is false at `S = 1`. (b) The `S ≥ 2` case holds
  with a shared reward. Also fix Findings 2–3.
