import Formalization.Generative.FiniteHorizonWorstTiePlanner
import Formalization.Generative.FiniteHorizonSelectorPipeline

/-! `Thm:sample-compl-finite` for every empirically optimal deterministic policy.

The statistical pipeline is run for the causal worst-tie planner (an analysis device that
reads the true model, not the algorithm). Every deterministic policy that is optimal for
the empirical MDP at every stage and state dominates that planner in the true model at
every stage and state, so the same event bounds its V and Q losses. -/
open MeasureTheory ProbabilityTheory
namespace StatisticalRL.FiniteHorizonGenerative
variable {State Action : Type*} [Fintype State] [Fintype Action]
local instance anyTieStateMeasurable : MeasurableSpace State := ⊤

/-- The worst-tie planner on the true stages and the empirical stages of `data`. -/
noncomputable def worstTieSelector {H : ℕ} (E : Fin H → EnvironmentStage State Action)
    (N : ℕ) (hN : 0 < N) (default : Action) (data : Samples State Action H N) :
    ℕ → State → Action :=
  worstActions default (List.ofFn E) (empiricalStages E N hN data)

/-- (W4) The worst-tie planner after stage `h` reads only strictly-future samples. -/
theorem worstTieSelector_factorsFuture {H : ℕ} (E : Fin H → EnvironmentStage State Action)
    (N : ℕ) (hN : 0 < N) (default : Action) :
    SelectorFactorsFuture (worstTieSelector E N hN default) := by
  intro h x data k s
  unfold worstTieSelector
  rw [worstActions_drop, worstActions_drop]
  have he := empiricalStages_drop_eq_of_future_eq E N hN h data
    (completeFutureData h N x (futureData h N data)) (by
      intro j hj t a i
      simp [completeFutureData, futureData, hj])
  rw [he]

/-- (W2) The worst-tie planner is empirically optimal at every suffix. -/
theorem worstTieSelector_empiricallyOptimal {H : ℕ}
    (E : Fin H → EnvironmentStage State Action) (N : ℕ) (hN : 0 < N) (default : Action) :
    SelectorEmpiricallyOptimal E N hN (worstTieSelector E N hN default) := by
  intro data h s
  exact worstActions_suffixOptimal default (List.ofFn E) (empiricalStages E N hN data)
    (by rw [empiricalStages_length, List.length_ofFn]) h s

theorem controlled_length_eq (es : List (EnvironmentStage State Action))
    (π : ℕ → StationaryPolicy State Action) :
    (EnvironmentStage.controlled es π).length = es.length := by
  induction es generalizing π with
  | nil => rfl
  | cons e es ih => simp [EnvironmentStage.controlled, ih]

/-- Optimality at the stages `h < H` of a length-`H` episode is optimality at every suffix:
beyond the episode both sides are the zero terminal value. -/
theorem suffixOptimal_of_forall_fin {H : ℕ} (fs : List (EnvironmentStage State Action))
    (hl : fs.length = H) (f : ℕ → State → Action)
    (hf : ∀ h : Fin H, ∀ s, policyTrajectorySuffix fs f h.val s =
      EnvironmentStage.optimalValue (fs.drop h.val) s) :
    SuffixOptimal fs (deterministicPolicy f) := by
  intro n s
  by_cases hn : n < H
  · exact hf ⟨n, hn⟩ s
  · have h1 : (EnvironmentStage.controlled fs (deterministicPolicy f)).drop n = [] :=
      List.drop_eq_nil_of_le (by rw [controlled_length_eq]; omega)
    have h2 : fs.drop n = [] := List.drop_eq_nil_of_le (by omega)
    rw [h1, h2, DecisionStage.trajectoryValue_nil]
    rfl

/-- Domination transfers the worst-tie planner's loss bound to every empirically
suffix-optimal deterministic policy. -/
theorem policyPerformanceBound_of_worstTie {H : ℕ}
    (E : Fin H → EnvironmentStage State Action) (N : ℕ) (hN : 0 < N) (default : Action)
    (data : Samples State Action H N) (R : ℝ) (hR : 0 ≤ R)
    (hw : PolicyPerformanceBound E (worstTieSelector E N hN default data) R)
    (f : ℕ → State → Action)
    (hf : SuffixOptimal (empiricalStages E N hN data) (deterministicPolicy f)) :
    PolicyPerformanceBound E f R := by
  have hl : (List.ofFn E).length = (empiricalStages E N hN data).length := by
    rw [empiricalStages_length, List.length_ofFn]
  have hv (h : ℕ) (s : State) :
      0 ≤ EnvironmentStage.optimalValue ((List.ofFn E).drop h) s -
          policyTrajectorySuffix (List.ofFn E) f h s ∧
      EnvironmentStage.optimalValue ((List.ofFn E).drop h) s -
          policyTrajectorySuffix (List.ofFn E) f h s ≤ R := by
    have hdom := worstActions_dominated_suffix default (List.ofFn E)
      (empiricalStages E N hN data) hl f hf h s
    have hwh := ((hw h).1 s).2
    unfold worstTieSelector at hwh
    refine ⟨sub_nonneg.mpr (policyTrajectorySuffix_le_optimal _ f h s), ?_⟩
    linarith
  intro h
  exact ⟨hv h, fun s a ↦ policyTrajectoryQSuffix_loss_le_of_values (List.ofFn E) f R hR
    (fun k t ↦ (hv k t).2) h s a⟩

/-- `Thm:sample-compl-finite` for every deterministic policy that is optimal for the
empirical MDP at every stage and state, with the explicit constant 8640. -/
theorem mainSample_anyEmpiricalOptimalPolicy {H : ℕ}
    (E : Fin H → EnvironmentStage State Action) (N : ℕ) (hN : 0 < N) (δ ε : ℝ)
    (hδ : 0 < δ) (hε : 0 < ε) (hεH : ε ≤ H)
    (hsize : 8640 * (H : ℝ) ^ 3 *
      Real.log ((H : ℝ) * Fintype.card State * Fintype.card Action / δ) / ε ^ 2 ≤ N) :
    1 - δ ≤ (samplingLaw E N).real
      {data | ∀ f : ℕ → State → Action,
        (∀ h : Fin H, ∀ s, policyTrajectorySuffix (empiricalStages E N hN data) f h.val s =
          EnvironmentStage.optimalValue ((empiricalStages E N hN data).drop h.val) s) →
        ∀ h : Fin H,
          (∀ s, EnvironmentStage.optimalValue ((List.ofFn E).drop h.val) s -
              policyTrajectorySuffix (List.ofFn E) f h.val s ≤ ε) ∧
          (∀ s a, EnvironmentStage.optimalQ ((List.ofFn E).drop h.val) s a -
              policyTrajectoryQSuffix (List.ofFn E) f h.val s a ≤ ε)} := by
  have hH : 0 < H := by
    have : (0 : ℝ) < H := hε.trans_le hεH
    exact_mod_cast this
  let default : Action := Classical.choice (E ⟨0, hH⟩).action_nonempty
  have hp := mainSample_selectorPolicy E N hN hH (worstTieSelector E N hN default)
    (worstTieSelector_factorsFuture E N hN default)
    (worstTieSelector_empiricallyOptimal E N hN default) δ ε hδ hε hεH hsize
  apply hp.trans
  apply measureReal_mono _ (measure_ne_top (samplingLaw E N) _)
  intro data hd f hf h
  have hso := suffixOptimal_of_forall_fin (empiricalStages E N hN data)
    (empiricalStages_length E N hN data) f hf
  have hb := policyPerformanceBound_of_worstTie E N hN default data ε hε.le hd f hso h.val
  exact ⟨fun s ↦ (hb.1 s).2, fun s a ↦ (hb.2 s a).2⟩

/-- A single numerical constant precedes all finite carriers, models, horizons,
confidence/accuracy parameters and sample sizes; the policy is any empirically optimal
deterministic policy, quantified inside the event. -/
theorem exists_universal_anyEmpiricalOptimalPolicy_sample_constant :
    ∃ c₀ : ℝ, 0 < c₀ ∧
      ∀ (State Action : Type*) [Fintype State] [Fintype Action]
        (H : ℕ) (E : Fin H → EnvironmentStage State Action)
        (N : ℕ) (hN : 0 < N) (δ ε : ℝ),
        0 < δ → 0 < ε → ε ≤ H →
        c₀ * (H : ℝ) ^ 3 *
          Real.log ((H : ℝ) * Fintype.card State * Fintype.card Action / δ) / ε ^ 2 ≤ N →
        1 - δ ≤
          (samplingLaw E N).real
            {data | ∀ f : ℕ → State → Action,
              (∀ h : Fin H, ∀ s,
                policyTrajectorySuffix (empiricalStages E N hN data) f h.val s =
                  EnvironmentStage.optimalValue ((empiricalStages E N hN data).drop h.val) s) →
              ∀ h : Fin H,
                (∀ s, EnvironmentStage.optimalValue ((List.ofFn E).drop h.val) s -
                    policyTrajectorySuffix (List.ofFn E) f h.val s ≤ ε) ∧
                (∀ s a, EnvironmentStage.optimalQ ((List.ofFn E).drop h.val) s a -
                    policyTrajectoryQSuffix (List.ofFn E) f h.val s a ≤ ε)} := by
  refine ⟨8640, by norm_num, ?_⟩
  intro State Action _ _ H E N hN δ ε hδ hε hεH hsize
  exact mainSample_anyEmpiricalOptimalPolicy E N hN δ ε hδ hε hεH hsize

end StatisticalRL.FiniteHorizonGenerative
