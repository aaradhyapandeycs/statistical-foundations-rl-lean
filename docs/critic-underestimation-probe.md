# PROBE: Q-learning under-estimation bound (batch plan item (c))

Public copy of the feasibility probe report; local paths removed. The batch plan it answers is the builder's private plan; it is not published.

Post-review note (added to this public copy, 2026-11-09): the probe files named below were private scratch files outside the library; their content was integrated into the library on 2026-11-09 with the Theorem 4.6 re-witness in the same change. `TDLogCubeTransport.lean` (`probe_td_logCube_accuracy`) → `Formalization/ModelFree/TDLogCubeUnitConstants.lean` (`td_logCube_unitConstants_accuracy`); `QLearningUnitConstants.lean` (`probe_qLearning_unit_constants`) → the proof body of `qLearning_exists_universal_constants_source_accuracy` in `Formalization/ModelFree/QLearningSourceTheoremClosure.lean` (former 1/4 body retained as `qLearning_exists_universal_constants_source_accuracy_quarter`); the under-estimation pipeline → `Formalization/ModelFree/QLearningUnderestimation{,Coupling,Lift,Law,Value}.lean`. The integrated entry cites `generative_model_model_free.tex:1869–1881` (plan-check fix F1), not the `:1869–1886` proposed below. The text below is otherwise unchanged.

Source: `source/upstream/tex/chapters/generative_model_model_free.tex:1869–1886` (paragraph
"Discussion: over-estimation vs. under-estimation"). Schedule `eq:thm:infinite-horizaon-eta` at
`:881–886` (log³T, "for some universal constants c₁ ≥ c₂ > 0"). Theorem 4.6 at `:891–912`
("small enough universal constants"). TD schedule `eq:thm:eta-TD` at `:177–181` (log²T).
Probe date 2026-11-08. No file under `Formalization/` was modified.

## 1. Verdict on the transport obstruction

**The obstruction is real only for Q-learning constants c₂ < 1. It is refuted as a general
blocker. For c₂ ≥ 1, in particular c₁ = c₂ = 1, the existing TD layers transport to the log³ schedule
unchanged. This is compiled; see §5.**

Exact reasons:

- All TD layers that consume the schedule take `c₁ c₂ c₃ : ℝ` as ordinary real arguments with
  explicit side conditions. Only the top wrapper fixes them
  (`tdSource_policyEvaluation_accuracy_exists_universal_constants`,
  `TDSourceFullAccuracyUniversal.lean:19–126`, witnesses 1/4, 1/4).
  The real arguments may depend on T. The consumed layers are:
  - `tdSource_firstFreedman_allStates_of_budget` (`TDSourceFirstFreedmanAssembly.lean:112`)
  - `tdSource_varianceProxy_both_of_budget` (`TDSourceVarianceProxyLemma.lean:16`)
  - `tdInitialError_contraction_of_source_budget` (`TDInitialErrorContraction.lean:15`)
  - `tdSource_final_accuracy_of_events` (`TDSourceFinalAccuracyComposition.lean:50`)
- The log³ schedule with Q-constants (c₁, c₂) is literally the log² schedule
  `tdSourceRateSchedule` / `TDStepSizeSchedule` (`TDSourceRateFiniteExtension.lean:17`,
  `TDStepSizeEarly.lean:9`) with c₁' = c₁/log T and c₂' = c₂/log T.
- The eligibility premise is `htime : T/(c₂' log T) ≤ t`, also written `tdSourceEligibleTerminal`
  (`TDSourceRateProxyTransport.lean:14`). It appears in:
  - `TDStepSizeEarly.lean:63`
  - `TDStepSizeLate.lean:13,52`
  - `TDSourceFreedmanScheduleCaps.lean:51`
  - `TDEarlyVarianceBudget.lean:133`
  - `TDInitialErrorContraction.lean:28`
  - `TDSourceFirstFreedmanComparisons.lean:67`
  - `TDSourceFirstFreedmanAssembly.lean:128`
  - `TDSharpSecondFreedmanEligibleUnion.lean:26`
  - `TDSourceFixedTerminalProxyBudget.lean:39`
- At the only terminal the closure uses, t = T, `htime` becomes c₂' log T = c₂ ≥ 1. The universal
  wrapper derives it through `tdSource_final_terminal_eligible_of_budget`
  (`TDSourceFinalAccuracyComposition.lean:27`), which uses `td_normalizedBudget_implies_final_late`
  and `td_final_terminal_is_late` (`TDTerminalWeightEnvelope.lean:35–65`). That derivation needs
  `exp(1/c₂') ≤ c₃ log⁴2`, which fails for c₂' = c₂/log T. A transport bypasses it and supplies
  `htime` directly.
- **Conclusion.** For c₂ < 1 (e.g. 1/4, Theorem 4.6's witness), no admissible c₂' exists:
  - The cap comparison forces c₂' ≤ c₂/log T.
  - Eligibility forces c₂' log T ≥ 1.

  So the plan's statement is correct for the 1/4 witness. For c₂ = 1 it is false: `htime` is
  `T/1 ≤ T`.
- The remaining side conditions hold with c₁' = c₂' = 1/L (L = log T) and c₃' = 8192·L:
  - c₁'c₃' = 8192 ≥ 4.
  - c₁'c₃' log²2 ≥ 1.
  - c₃' ≥ 3168 because L ≥ log 2 ≥ 1/2.
  - c₁'c₂' = 1/L² ≤ 1/8. This is derived from the budget: 8192 L⁵ ≤ T, so T ≥ 256 and L ≥ 4.
  - The budget c₃'L³·log(ST/δ)/((1−γ)³ε²) ≤ T is exactly 8192 L⁴·log(ST/δ)/((1−γ)³ε²) ≤ T. So the
    plan's log⁴ appears naturally.
- **c₁ = c₂ = 1 is also a valid witness for Theorem 4.6 itself.** The layer
  `qLearning_conditional_source_accuracy` (`QLearningConditionalFinalAssembly.lean:44`) only needs
  0 < c₁ ≤ 1 and 0 < c₂, plus budget constants from `qFinal_exists_universal_budget_constant c₂`.
  The closure `qSource_robust_comparator_closeness_from_stopped_law` is generic in c₂. This is
  compiled; see §5. So one witness pair can serve both Thm 4.6 and the under-estimation claim, and
  the "same Q-learning run" reading is available.

## 2. Recommended route

Route **(i′): transport by T-dependent instantiation at Q-constants c₁ = c₂ = 1.** It needs no new
or generalized TD envelope lemmas and no edits to existing TD files.

- Route (i) proper (generalizing the envelope over the log exponent, or over a 1/c₂ factor, so that
  c₂ < 1 is covered) is not needed. It would be expensive:
  - `tdSourceBarEta = 2 log³T/((1−γ)T)` (`TDSourceFreedmanBudgetSmallness.lean:11`) and the
    constants 3, 16, 33, 3168 are hard-coded through about 15 files.
  - It needs parallel parametrized copies of roughly 2000–3000 lines.
- Route (ii) (a direct argument) re-derives the sharp TD analysis. Not recommended.
- Route (iii) (restricted) is not needed if the critic accepts the witness (1, 1); see Risks.

Pipeline:

1. Definitions `qPolicyEvaluationIterate` / `qPolicySampledIterate`, as in the plan, in the
   allowlisted `QLearningSamplingDefinitions.lean`.
2. Pathwise coupling Q̃_t ≤ Q_t for η ∈ [0,1], γ ≥ 0.
3. Lifted MDP on `State × Action` with `Action' = Unit`.
   - Transition (s,a) ↦ law of (s′, f s′) with s′ ∼ P(·|s,a). Reward r(s,a). Same γ.
   - Pathwise: `qPolicyEvaluationIterate M f η samples Q₀ t (s,a) = tdIterate lift unit η
     (liftSamples samples) Q₀' t (s,a)`. Here policyReward of the lift is r(s,a).
4. Law identity. The Q index type `((S×A) × Fin T)` coincides with the TD source index
   `(State' × Fin T)`. The lifted `tdSourceSamplingLaw` is the map of `qSamplingLaw` under the
   coordinatewise lift (`Measure.pi_map_pi` plus `PMF.toMeasure_map` on `rowMeasure`). Reuse the
   `TDSourceAccuracyExactSamples` projection pattern for padded vs exact samples.
5. Value identity. Lifted `trajectoryExpectedValue unit (s,a) = M.trajectoryExpectedQ
   M.optimalGreedyPolicy s a` when f is optimal in the sense of the Prop. Use fixed-point uniqueness
   (`trajectoryExpectedQ_eq_policyFixedPoint`, `MDP/ForcedPrefixBridge.lean:271`;
   `MDP/OptimalTrajectoryValue.lean:111–133`).
6. Promote the probe `probe_td_logCube_accuracy` (123 lines, compiled) to a library lemma.
7. Assembly with ε := √(8192 L⁴ log(SAT/δ)/((1−γ)³T)), where card(S×A) = S·A:
   - If ε ≤ 1/(1−γ), the budget holds with equality: apply step 6.
   - Otherwise Q̃_T ≥ 0 ≥ Q⋆ − 1/(1−γ) > Q⋆ − ε holds pathwise. This needs Q̃ ≥ 0, from Q₀ ≥ 0,
     η ∈ [0,1], r ≥ 0.
8. Statement entry plus `_holds` wrapper. Optionally re-witness `Thm4_6_holds` at (1, 1) (40 lines,
   compiled probe) so that both entries can share constants. This is not required for the
   existential Props.

## 3. Revised line estimate

| Step | Lines |
|---|---|
| 1 defs | 20–30 |
| 2 coupling | 80–150 |
| 3 lift + pathwise identity | 120–200 |
| 4 law pushforward + projection | 150–350 |
| 5 value identity | 200–400 |
| 6 log³ transport (done in probe) | 125–140 |
| 7 assembly / case split | 200–350 |
| 8 entry + wrapper | 60–100 |
| **Total** | **≈ 950–1700** (was 1700–3700) |

Class M (was L). The heaviest risk moves from TD re-derivation to the measure/instance plumbing
(step 4) and the value identity (step 5).

## 4. Prop draft

```lean
/-- Under-estimation discussion after Theorem 4.6, `thm:infinite-horizon-simple`,
`source/upstream/tex/chapters/generative_model_model_free.tex:1869–1886` (Q-learning
`:851–871`, schedule `eq:thm:infinite-horizaon-eta` `:881–886`, Theorem 4.6 `:891–912`).
`Q̃` (`qPolicySampledIterate`) uses the same samples and initialization as Q-learning but takes the
next action from a deterministic optimal policy `f`. Clause 1 (`Q̃_T ≤ Q_T`) is pathwise for every
data set. Clause 2 makes the printed `−Õ(√(1/((1−γ)³T)))` explicit: the hidden polylog is
`log⁴T · log(SAT/δ)`, the four powers of log T coming from the log³ step-size schedule plus one
extra factor, and the claim holds with probability `≥ 1−δ`, simultaneously for all `(s,a)`. The
schedule constants are existential, as in `Thm4_6`. The proof uses `c₁ = c₂ = 1`, which also
witnesses `Thm4_6`. `A ≥ 2` is not assumed. A prose claim, not a numbered result. -/
def Thm4_6_underestimation : Prop :=
  ∃ c₁ c₂ C : ℝ, 0 < c₂ ∧ c₂ ≤ c₁ ∧ 0 < C ∧
  ∀ (State : Type u) (Action : Type v) [Fintype State] [Fintype Action]
    (M : DiscountedMDP State Action) (η : ℕ → ℝ) (δ : ℝ) (T : ℕ),
    1 / 2 ≤ M.discount → 2 ≤ T → 0 < δ → δ < 1 →
    (∀ k, k ≤ T →
      1 / (1 + c₁ * (1 - M.discount) * T / Real.log (T : ℝ) ^ 3) ≤ η k ∧
      η k ≤ 1 / (1 + c₂ * (1 - M.discount) * k / Real.log (T : ℝ) ^ 3)) →
    ∀ (Q₀ : State → Action → ℝ), (∀ s a, 0 ≤ Q₀ s a ∧ Q₀ s a ≤ M.effectiveHorizon) →
    ∀ (f : State → Action),
      (∀ s, M.trajectoryExpectedValue (fun t ↦ EnvironmentStage.pointMass (f t)) s =
        M.trajectoryExpectedValue M.optimalGreedyPolicy s) →
    (∀ (data : QSamples State Action T) s a,
        qPolicySampledIterate M f η T Q₀ data s a ≤ qSampledIterate M η T Q₀ data s a) ∧
    1 - δ ≤ (qSamplingLaw M T).real {data | ∀ s a,
      -(C * Real.sqrt (Real.log (T : ℝ) ^ 4 *
          Real.log ((Fintype.card State : ℝ) * (Fintype.card Action : ℝ) * T / δ) /
          ((1 - M.discount) ^ 3 * T))) ≤
        qPolicySampledIterate M f η T Q₀ data s a -
          M.trajectoryExpectedQ M.optimalGreedyPolicy s a}
```

The witnesses are c₁ = c₂ = 1 and C = 91 (91² = 8281 ≥ 8192). The existing `Thm4_6` `(∀ k, k ≤ T → …)`
schedule form is kept. Only indices 1 ≤ k ≤ T are used.

Note: the plan pointed to `MF:1869–1885`. The display closes at `:1882` and the sentence ends at
`:1886`. Cite `:1869–1886`.

## 5. Probe evidence (build log)

All compiles: `bash scripts/lean-local.sh <file>` from the project root, foreground, one at a time.

| File | Exit | Wall | Result |
|---|---|---|---|
| `TDLogCubeTransport.lean` (private probe) | 0 | 55 s | no errors/warnings |
| `TDLogCubeTransportAxioms.lean` (private probe; same + `#print axioms`) | 0 | ~55 s | `probe_td_logCube_accuracy`: [propext, Classical.choice, Quot.sound] |
| `QLearningUnitConstants.lean` (private probe) | 0 | ~60 s | `probe_qLearning_unit_constants`: [propext, Classical.choice, Quot.sound] |

What each probe establishes:

- `probe_td_logCube_accuracy`: for any M, π, γ ≥ 1/2, T ≥ 2, δ ∈ (0,1), 0 < ε ≤ 1/(1−γ), and η with
  `1/(1+(1−γ)T/log³T) ≤ η i ≤ 1/(1+(1−γ)i/log³T)` for 1 ≤ i ≤ T, the hypothesis
  `8192·log⁴T·log(ST/δ)/((1−γ)³ε²) ≤ T` gives
  `1−δ ≤ P_tdSamplingLaw(∀ s, |V_T(s) − V^π(s)| ≤ ε)`.
- `probe_qLearning_unit_constants`: the `Thm4_6` accuracy statement holds with c₁ = c₂ = 1, for some
  c₃ > 0.

sha256:

- `c02c99d524c082337f4f1cc5d36bd5f9f150279b4f61b4d97d62b87b6264f000  QLearningUnitConstants.lean`
- `bfc809ea5227fe7c9927abbfb53b9fdef6192c93f06947a7d3ce51fe86f99025  TDLogCubeTransport.lean`
- `0853b990e9d0a676841a88276b231337c011b2e0db182380568c95b7372ab22c  TDLogCubeTransportAxioms.lean`

## 6. Risks

1. **Witness reading (critic decision).** The source says "small enough universal constants". Using
   (1, 1) relies on the project's existential encoding, as already used by `Thm4_1` and `Thm4_6`. If
   the critic requires the claim for Thm 4.6's existing witness (1/4) or for all small c₂, it is
   **not** covered: c₂ < 1 is exactly the real obstruction. Then use
   `Thm4_6_underestimation_restricted` with a SOURCE-ISSUES scope paragraph, or pay for route (i).
   Mitigation: re-witness `Thm4_6_holds` at (1, 1). The compiled probe shows this is a 40-line
   change, and it lets both entries describe the same schedule class.
2. **Measurable-space instances on `State × Action`** (step 4). The TD layers use a local
   `MeasurableSpace := ⊤`. The lifted state type may pick up `Prod.instMeasurableSpace` instead. This
   is a propositional, not definitional, equality on finite types. Budget about 100 extra lines, or
   state everything with an explicit `⊤` instance.
3. **Value identity** (step 5). This depends on how `optimalGreedyPolicy` and `pointMass` policies are
   related in the existing API. f-optimality is given only as V^f = V⋆, and Q^f = Q⋆ must be derived
   via the Bellman equation for Q. Existing lemmas at `MDP/OptimalTrajectoryValue.lean:111–133` look
   sufficient, but this is unverified.
4. **Log power.** `log⁴T·log(SAT/δ)` is the honest explicit polylog for this route. Whether a sharper
   `log³T` is achievable is irrelevant to the Õ claim. The docstring discloses the exponents. Per
   the small-batch-2 plan check (c) ([public copy](critic-small-batch-2-plan-check.md)), that disclosure is acceptable, so the entry does not need
   `_restricted`.
5. Not verified here: steps 2–5 and 7 were not compiled. Only the TD transport (step 6) and the
   Thm 4.6 re-witness were compiled.
