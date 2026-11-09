# CHECK: Q-learning under-estimation route (probe report, batch plan item (c))

Public copy of the independent plan check; local paths removed. The probe report checked here is published as [critic-underestimation-probe.md](critic-underestimation-probe.md); the batch plan is the builder's private plan and is not published.

Post-review note (added to this public copy, 2026-11-09): the plan was integrated into the library on 2026-11-09 with the Theorem 4.6 re-witness in the same change (F2 done: the (1,1) body is the export's body and the 1/4 body is retained as `qLearning_exists_universal_constants_source_accuracy_quarter`). Probe files named below map to `Formalization/ModelFree/TDLogCubeUnitConstants.lean` (`TDLogCubeTransport.lean`) and `Formalization/ModelFree/QLearningSourceTheoremClosure.lean` (`QLearningUnitConstants.lean`); the pipeline is `Formalization/ModelFree/QLearningUnderestimation{,Coupling,Lift,Law,Value}.lean`. The text below is otherwise unchanged.

Independent plan check, critic stance. Date 2026-11-08. Read only. No Lean or lake was run, and
nothing under `Formalization/` was touched.

Inputs read:

- `AGENTS.md`
- the source `source/upstream/tex/chapters/generative_model_model_free.tex`
  (sha256 `7f4eb058e00480bc0694cac93ac41e22f4cfe48aa58a00c4ccf909f805e60b22`), lines 170–185,
  845–912 and 1855–1887
- `Formalization/Statements/Ch4.lean`: `Thm4_1` docstring :20–25, `Thm4_6` :140–159,
  `Remark4_2` :471–502
- `Formalization/Statements/Ch4Proofs.lean`: `Thm4_6_holds` :86–89, `Remark4_2_holds` :127
- `QLearningSamplingDefinitions.lean`, `QLearningIterateBounds.lean:18–25`,
  `TDSamplingDefinitions.lean`, `TDIterateBounds.lean`, `TDActualErrorDecomposition.lean`,
  `MDP/CoreDefinitions.lean`, `MDP/OptimalTrajectoryValue.lean:105–135`,
  `QLearningLateRateSchedule.lean:8`
- the three probe files (private)

## Verdict: GO WITH FIXES

The mathematics of the route is sound and the transport argument is correct. The naming is
acceptable unsuffixed **only** together with fix F2, which moves the Theorem 4.6 witnesses to (1,1).
Two plan facts are wrong and must be corrected:

- the citation range (F1)
- the claim that the index types coincide in step 4 (F5)

## Source facts (independently read)

- `:881–886` `eq:thm:infinite-horizaon-eta`. The schedule is log³T and covers `0 ≤ t ≤ T`. The text
  says "for some universal constants c₁ ≥ c₂ > 0". It names no threshold.
- `:887` says the schedule class "encompass[es] both constant and rescaled linear learning rates
  (when appropriately chosen)".
- `:891–912` Theorem 4.6 says "for some small enough universal constants c₁ ≥ c₂ > 0". Its hypotheses
  are A ≥ 2, the budget, and 0 ≤ Q₀ ≤ 1/(1−γ).
- `:1869–1881` is the under-estimation paragraph:
  - `:1869` is the `\paragraph` header.
  - `:1871` is the prose: the auxiliary iteration with the "same initialization and transition
    samples" and a "deterministic optimal policy π⋆". It says "one can anticipate that Q̃_t ≤ Q_t"
    and "The TD-learning analysis gives".
  - `:1873–1879` is the display `Q_T−Q⋆ ≥ Q̃_T−Q⋆ ≥ −Õ(√(1/((1−γ)³T)))1_{SA}`.
  - `:1881` is the closing sentence.
  - `:1882–1886` are blank lines. `:1887` starts `\section{Extension: asynchronous Q-learning}`.
- The paragraph states no constants, no δ and no T threshold. The only sensible context is Q-learning
  with the learning rates of Theorem 4.6 (`eq:thm:infinite-horizaon-eta`), with Thm 4.6's
  initialization.

## (1) Witness reading and naming

- **How the project encodes the constants.** `Thm4_6` encodes "small enough universal constants" as
  `∃ c₁ c₂ c₃, 0 < c₂ ≤ c₁ ∧ 0 < c₃ ∧ ∀ …`. It does not encode "∃ threshold, ∀ c₁ ≥ c₂ below it".
  This weaker existential encoding is already accepted in the index for `Thm4_1`, `Thm4_6` and the
  remarks. Within that encoding, "small enough" puts no constraint on the witness value: c = 1 is as
  admissible as c = 1/4. Both the Prop's existential and the proof back this.
- **What the under-estimation claim inherits.** It is a remark about the Q-learning run that
  Theorem 4.6 analyses. So it inherits Theorem 4.6's schedule class, meaning the **same** existential
  witnesses. It does not inherit "every admissible c₂". A separate, independently witnessed
  existential would certify the remark for a schedule class (1,1) for which the index certifies no
  Theorem 4.6, while `Thm4_6` stays certified only at (1/4,1/4). No single run would then be covered
  by both entries. The two classes are incomparable:
  - c₁ = 1 has a smaller lower bound than c₁ = 1/4.
  - c₂ = 1 has a smaller cap than c₂ = 1/4.
- **The obstruction for c₂ < 1 is real, but it belongs to the proof infrastructure.** The closure
  needs c₂' log T ≥ 1, as the probe found. It is not a falsity of the source claim. The claim is
  presumably still true for small c₂, via a log³ re-derivation of the TD envelope (route (i)).
  Therefore:
  - If the "every sufficiently small c₂" reading were required, the honest name would be
    `Thm4_6_underestimation_restricted`, with a scope paragraph rather than a refutation.
  - Under the project's existential encoding it is not required.
- **Decision.**
  - Use the name `Thm4_6_underestimation` (unsuffixed), provided F2 is done in the same change, so
    that `Thm4_6`, `Remark4_2` and the new entry share the witnesses c₁ = c₂ = 1. The re-witness probe
    `probe_qLearning_unit_constants` shows Theorem 4.6 holds at (1,1). The library export
    `qLearning_exists_universal_constants_source_accuracy` has signature
    `∃ c₁ c₂ c₃, 0 < c₂ ∧ c₂ ≤ c₁ ∧ c₁ ≤ 1 ∧ 0 < c₃ ∧ …`, and c₁ = 1 satisfies `c₁ ≤ 1`. So the
    re-witness changes no signature.
  - If F2 is declined, use `Thm4_6_underestimation_restricted`. Its docstring and SOURCE-ISSUES
    scope paragraph must say that its witnesses (1,1) differ from `Thm4_6`'s (1/4,1/4), so the
    "same run" reading is not certified, and that c₂ < 1 is not covered.
- **Side effect to disclose.** After F2, the statement index certifies Theorem 4.6 for the (1,1)
  class and no longer for (1/4,1/4). The library may keep the (1/4) proof. Both are legitimate
  existential witnesses. The (1,1) class contains both examples that `:887` names:
  - the constant rate `η ≡ 1/(1+(1−γ)T/log³T)`
  - the rescaled linear rate `1/(1+(1−γ)t/log³T)`

## (2) Transport argument: verified

- **Rate identity.** `(1/L)(1−γ)i/L² = 1·(1−γ)i/L³`, with L = log T ≠ 0. This is
  `probe_logCube_rate_eq`. So the log³ schedule with c = 1 is literally the log² schedule
  `tdSourceRateSchedule γ c' c' T η` with c' = 1/L. More generally, c ↦ c/L.
- **htime.** `T/(c₂' L) ≤ t` with c₂' = c₂/L becomes `T/c₂ ≤ t`. At the only terminal used, t = T,
  this is c₂ ≥ 1. With c₂ = 1, c₂'L = 1 and `htime` is `T ≤ T`. The probe supplies it directly as
  `htime`, which bypasses the `exp(1/c₂') ≤ c₃ log⁴2` route that fails.
- **Side conditions** with c₁' = c₂' = 1/L and c₃' = 8192L. L ≥ log 2 ≥ 1/2 is proved via
  `one_sub_inv_le_log_of_pos`.
  - c₁'c₃' = 8192 ≥ 4.
  - 8192·log²2 ≥ 8192/4 ≥ 1.
  - c₃' ≥ 4096 ≥ 3168 ≥ 384.
  - c₁'c₂' = 1/L² ≤ 1/8 needs L ≥ √8 ≈ 2.83. The probe gets L ≥ 4 as follows:
    - `td_mainBudget_implies_normalized` gives c₃'L⁴ ≤ T, i.e. 8192L⁵ ≤ T.
    - With L ≥ 1/2, this gives T ≥ 256, hence L ≥ 8 log 2 ≥ 4.
    - The normalization uses S ≥ 1 (`M.state_nonempty`, available because `DiscountedMDP` carries
      nonemptiness), δ < 1 and ε ≤ 1/(1−γ). So log(ST/δ) ≥ log T.
- **Budget.** `c₃'L³·log(S'T/δ)/((1−γ)³ε²) = 8192L⁴·log(S'T/δ)/((1−γ)³ε²) ≤ T`. This is
  `hbudget'`. For the lifted chain, S' = card(State×Action) = S·A (`Fintype.card_prod` plus a cast),
  which matches the Prop's `S*A*T/δ`.
- **Probe statement meaning.** `probe_td_logCube_accuracy` concludes
  `1−δ ≤ (tdSamplingLaw M π T).real {∀ s, |tdErrorValue … T s| ≤ ε}`. Here
  `tdErrorValue = tdIterate − M.trajectoryExpectedValue π` (`TDActualErrorDecomposition.lean:11–14`),
  i.e. |V_T − V^π| ≤ ε, two-sided. Its hypotheses:
  - schedule only on 1 ≤ i ≤ T, with the explicit factor `1 *`
  - γ ≥ 1/2, T ≥ 2, δ ∈ (0,1), 0 < ε ≤ 1/(1−γ), V₀ ∈ [0, 1/(1−γ)]

  All of these are implied by the Prop's premises after `one_mul`, restriction to 1 ≤ k, and the
  instantiation ε := ε_T. `probe_qLearning_unit_constants` is `Thm4_6`'s body with
  `qSourceRateSchedule γ 1 1` (`QLearningLateRateSchedule.lean:8`, the same `∀ k ≤ T` form) and
  c₃ from `qFinal_exists_universal_budget_constant 1`.
- **Not re-run here.** The probe compile results and axiom lists are taken from PROBE §5. The file
  hashes match:
  - `c02c99d5…f000` `QLearningUnitConstants.lean`
  - `bfc809ea…9025` `TDLogCubeTransport.lean`
  - `0853b990…2c` `TDLogCubeTransportAxioms.lean`

  `TDLogCubeTransportAxioms.lean` differs from `TDLogCubeTransport.lean` only by the added
  `#print axioms` line.

## (3) Steps 1–8

1. **Defs.** Correct. They match the `qLearningIterate` indexing: `η (t+1)` and `samples (t+1)`,
   with the max replaced by evaluation at `f s'`.
2. **Coupling.** Sound. The difference at step t is
   `(1−η)(Q−Q̃)_{t−1} + ηγ(max_{a'}Q_{t−1}(s',a') − Q̃_{t−1}(s',f s')) ≥ 0`. It needs η_k ∈ [0,1] for
   1 ≤ k ≤ T and γ ≥ 0:
   - The lower bound gives η_k > 0, using (1−γ) > 0 and L > 0.
   - The cap gives η_k ≤ 1.
   - Clause 1 is stated for every `data`. Only k ≤ T is used, so the schedule hypothesis suffices.
3. **Lift.** Sound.
   - State' = State×Action, Action' = Unit, r'((s,a),()) = r(s,a) ∈ [0,1], same γ.
   - P'((s,a),()) = law of (s', f s') with s' ∼ P(·|s,a). A `FiniteDistribution` map/pushforward is
     needed; its API has not been checked.
   - `policyReward M' (pointMass ()) = r(s,a)` needs a small lemma (expectation under a point mass on
     Unit).
4. **Law. Plan correction F5 applies.** Sound in substance, but the probe's claim that the Q index
   `((S×A)×Fin T)` "coincides" with the TD index is wrong:
   - `tdSamplingLaw M π T = samplingLaw M π (T+1)` lives on `State × Fin (T+1)`. `tdSamplesExtend`
     reads `data (s, t)` at index t (index 0 unused).
   - `qSamplesExtend` reads `data ((s,a), t−1)`.

   The step must therefore be a coordinate pushforward (s' ↦ (s', f s')) composed with the
   Fin (T+1) → Fin T marginal via `Fin.succ`, plus a pathwise identity at T that uses only indices
   1..T. In addition, the TD row is a policy mixture `Σ_a' π(a'|x) P'(·|x,a')`; with π = pointMass ()
   it must be shown to equal P'(·|x,()). `TDSourceAccuracyExactSamples.lean`
   (`tdSource_policyEvaluation_exactSamples_accuracy_exists_universal_constants`) is the right
   pattern. Keep the 150–350 line budget, leaning to its upper end.
5. **Value identity.** Sound.
   - Lifted V'(s,a) and Q^f(s,a) both satisfy X(s,a) = r(s,a) + γ Σ P(s'|s,a) X(s', f s'), so they
     are equal by uniqueness of the γ-contraction fixed point. Available API:
     `trajectoryExpectedValue_eq_policyAverageQ` and `trajectoryExpectedQ_eq_policyFixedPoint` on the
     lift, then `policyFixedPoint_eq_reward_add_value` on M.
   - Then Q^f = r + γPV^f = r + γPV⋆ = Q⋆. The last step uses the hypothesis V^f = V⋆ for all s and
     `optimalGreedy_trajectoryQ` together with `policyFixedPoint_eq_reward_add_value` for the greedy
     policy.
   - The hypothesis "V^f(s) = V⋆(s) for all s" is the right notion of a deterministic optimal policy
     (cf. P:738–739). It is more general than f = greedy.
6. **Transport lemma.** Verified in (2). When it is promoted to the library, keep the explicit
   `(1 : ℝ) *` form or restate it with c = 1 folded.
7. **Assembly.** Sound. Let ℓ = log(SAT/δ) > 0 (because SAT/δ > T ≥ 2) and
   ε_T = √(8192L⁴ℓ/((1−γ)³T)) > 0.
   - **Case ε_T ≤ 1/(1−γ).** The budget holds with equality: 8192L⁴ℓ/((1−γ)³ε_T²) = T. The TD event
     maps to the Q event by preimage. With `⊤` σ-algebras on finite types, any set is measurable.
     Note `.real` of the pushforward on a non-measurable set; use the `⊤` or `Finite`-based
     measurability.
   - **Case ε_T > 1/(1−γ).** Pathwise Q̃_T ≥ 0 (Q₀ ≥ 0, η ∈ [0,1], r ≥ 0, γ ≥ 0) and
     Q⋆ ≤ 1/(1−γ) (reward ≤ 1). So Q̃−Q⋆ ≥ −1/(1−γ) > −ε_T. The event is all of the space, with
     measure 1 ≥ 1−δ (probability measure).
   - **C = 91.** 91² = 8281 ≥ 8192, so ε_T ≤ 91·√(L⁴ℓ/((1−γ)³T)).
   - There is no lower-order term and no budget premise, so the Prop holds for every T ≥ 2, which is
     stronger than needed.
8. **Entry and wrapper.** Fine, subject to F1–F4.

The probe's estimate of 950–1700 lines, class M, is credible. The main risks are steps 3–5
(`FiniteDistribution` map, the mixture-row lemma, and instance plumbing for `MeasurableSpace` on
`State×Action`).

## (4) Prop draft `Thm4_6_underestimation`

Faithful and self-contained:

- **Quantifiers.** ∃ c₁ c₂ C, then the universes u, v as in `Thm4_6`. Every hypothesis is written
  out.
- **Schedule.** Uses the `∀ k ≤ T` range, i.e. 0 ≤ k ≤ T, exactly as in `:885` and in `Thm4_6`.
- **Initialization.** Q₀ ∈ [0, 1/(1−γ)], as in `:902–903`. γ ≥ 1/2 and T ≥ 2 as in Thm 4.6.
- **Hypotheses not assumed.** A ≥ 2 is dropped and Thm 4.6's budget is not assumed. Both make the
  Prop stronger, which is not a discrepancy under AGENTS.md. δ ∈ (0,1) and "w.p. ≥ 1−δ, simultaneously
  for all (s,a)" are the standard explicit reading of Õ plus `1_{SA}`.
- **Optimal policy.** The deterministic optimal f is a hypothesis in the existing `pointMass (f t)`
  convention (`Ch3Definitions.lean:116`). Q⋆ is `trajectoryExpectedQ optimalGreedyPolicy`, as in
  `Thm4_6`.
- **The two display inequalities.**
  - Clause 1 (pathwise Q̃_T ≤ Q_T) is equivalent to the first inequality.
  - Clause 2 is the second inequality with Õ made explicit as
    `C·√(log⁴T·log(SAT/δ)/((1−γ)³T))`. That is a polylog factor in T, S, A and 1/δ, with no
    1/(1−γ) factor hidden. It is a legitimate instance of Õ, and the exponents are disclosed.
- **Non-vacuity.** c₁ = c₂ = 1 admits η_k = 1/(1+(1−γ)k/L³).
- **Statements/Ch4.lean import rule.** Only the definition module `QLearningSamplingDefinitions.lean`
  is needed, which complies with the rule.

## Required fixes

- **F1. Citation.** Cite `generative_model_model_free.tex:1869–1881`, not `:1869–1886` (probe) or
  `:1869–1885` (plan). The display is `:1873–1879`. The paragraph's last sentence ends at `:1881`.
  `:1882–1886` are blank. The probe's note "display closes at :1882, sentence ends at :1886" is
  factually wrong.
- **F2. Shared witnesses, as the condition for the unsuffixed name.** In the same change, make the
  Theorem 4.6 witnesses c₁ = c₂ = 1. Preferred: change only the proof body of
  `qLearning_exists_universal_constants_source_accuracy`
  (`QLearningSourceTheoremClosure.lean:58`) to the (1,1) witness, keeping its signature. Then
  `Thm4_6_holds` and `Remark4_2_holds` (via `qLearning_meanError_exists_universal_constants`) follow
  unchanged, and the `Remark4_2` docstring's "reuses its witnesses" stays true. Update every text
  that cites 1/4 for Theorem 4.6:
  - the `Thm4_6` docstring at `Ch4.lean:140–142`
  - `docs/named-result-status.json` and COVERAGE notes, if they cite 1/4 for Theorem 4.6

  `Thm4_1`'s 1/4 stays: that is TD, a different schedule. If only the wrapper `Thm4_6_holds` is
  re-witnessed, the `Remark4_2` docstring (Ch4.lean:473–475) must be corrected as well. If F2 is
  declined, use `_restricted` as described in (1).
- **F3. Docstring disclosure.**
  - In both `Thm4_6` and `Thm4_6_underestimation`: "small enough universal constants" is encoded
    existentially. The witness is c₁ = c₂ = 1. Schedules with c₂ < 1 are not covered. The
    "every sufficiently small c₁ ≥ c₂" reading is not established. For the under-estimation entry
    this is a proof-infrastructure limit: the TD closure needs c₂ ≥ 1 after log³→log² transport.
    It is not a source error.
  - Remove the wording "A prose claim, not a numbered result" only if the index convention requires
    it; otherwise keep it.
- **F4. Docstring precision.**
  - State that the hidden polylog is exactly `log⁴T·log(SAT/δ)` with constant C (= 91 in the proof).
  - State that there is no T budget and no A ≥ 2 premise (both are stronger than printed).
  - State that clause 1 holds for every data array.
- **F5. Plan correction for step 4.** It is a pushforward composed with the `Fin (T+1) → Fin T`
  (`Fin.succ`) marginal, plus a policy-mixture row lemma for the Unit action, following
  `TDSourceAccuracyExactSamples.lean`. It is not an identity of index types.

Optional, not required: a stronger statement for all c₁ ≥ c₂ ≥ 1 is reachable by the same transport,
with c' = c/L and a c-dependent C via the L² ≥ 8c₁c₂ requirement. It is not needed for the printed
claim.

## Hashes

- `7f4eb058e00480bc0694cac93ac41e22f4cfe48aa58a00c4ccf909f805e60b22`
  `source/upstream/tex/chapters/generative_model_model_free.tex`
- `c02c99d524c082337f4f1cc5d36bd5f9f150279b4f61b4d97d62b87b6264f000`
  `QLearningUnitConstants.lean` (private probe)
- `bfc809ea5227fe7c9927abbfb53b9fdef6192c93f06947a7d3ce51fe86f99025`
  `TDLogCubeTransport.lean` (private probe)
- `0853b990e9d0a676841a88276b231337c011b2e0db182380568c95b7372ab22c`
  `TDLogCubeTransportAxioms.lean` (private probe)
