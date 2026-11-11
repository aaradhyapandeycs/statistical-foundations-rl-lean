import Formalization.Online.Regret.T3.OnlineRegretT3PrefixSetSum
import Formalization.Probability.EmpiricalRow
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

/-!
# Conditional centering on the actual source prefix filtration

measure-theoretic bridge. The actual joint reset/path law is used,
and each prefix sigma-field is the comap of the actual reset-vector plus
reconstructed-history observation. The finite arbitrary-set sum lemma supplies
the set-integral identity; no conditional-mean assumption is added.
-/

namespace StatisticalRL.OnlineRL
open MeasureTheory ProbabilityTheory
open scoped BigOperators

universe uState uAction
variable {State : Type uState} {Action : Type uAction}
  [Fintype State] [Fintype Action]
noncomputable local instance onlineT3CESetStateMeasurable : MeasurableSpace State := ⊤
noncomputable local instance onlineT3CESetStateDecidableEq : DecidableEq State :=
  Classical.decEq State
noncomputable local instance onlineT3CESetActionDecidableEq : DecidableEq Action :=
  Classical.decEq Action

/-- Source T₃ residual at the fixed episode/stage index, on the actual
finite reset/path sample space. The tail uses only the first `k*H` records,
while the selected row uses the entire revealed prefix. -/
noncomputable def onlineT3SourceResidualAtPrefix
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (fallback : State) (planner : OnlineEpisodePlanner State Action H)
    (k : Fin K) (h : Fin H) (L c₁ c₂ : ℝ) (m : ℕ)
    (sample : (Fin K → State) × OnlineOutcomePath.{uState, 0} State
      ((m + 1) + (k.val * H + h.val))) : ℝ := by
  let n := k.val * H + h.val
  let history := onlineT3PrefixHistory H K hH fallback planner sample.1 n (m + 1) sample.2
  let choose := onlineEpisodicChoose H K hH sample.1 fallback planner
  let rowLaw := onlineMDPSuccessorRowLaw E
  let tail := onlineT3CompletedPrefixTail E history k.val h L c₁ c₂
  exact (rowLaw (choose history)).expectation tail -
    tail (onlineSequentialPathSuffix n (m + 1) sample.2).2.1

/-- Actual prefix observation: the reset vector is retained in the information
field because it determines the causal planner at each episode boundary. -/
noncomputable def onlineT3PrefixObservation
    (H K : ℕ) (hH : 0 < H) (fallback : State)
    (planner : OnlineEpisodePlanner State Action H)
    (m n : ℕ)
    (sample : (Fin K → State) × OnlineOutcomePath.{uState, 0} State (m + n)) :=
  (sample.1, onlineT3PrefixHistory H K hH fallback planner sample.1 n m sample.2)

/-- The actual prefix sigma-field, with the full reset vector revealed and the
first `n` causal records observed. -/
noncomputable def onlineT3PrefixSigma
    (H K : ℕ) (hH : 0 < H) (fallback : State)
    (planner : OnlineEpisodePlanner State Action H) (m n : ℕ) :
    MeasurableSpace ((Fin K → State) × OnlineOutcomePath.{uState, 0} State (m + n)) :=
  (⊤ : MeasurableSpace ((Fin K → State) × List (OnlineMDPRow State Action H × State))).comap
    (onlineT3PrefixObservation H K hH fallback planner m n)

/-- Conditional expectation of the actual T₃ residual is zero given the actual
reset-vector/prefix-history sigma-field. The sample horizon is expressed as
`(m+n)`; callers use the exact finite-horizon arithmetic to instantiate the
source's `K*H` draws. -/
theorem onlineSequentialEpisodeLaw_sourceT3_condExp_zero
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (ρ : FiniteDistribution State) (fallback : State)
    (planner : OnlineEpisodePlanner State Action H)
    (k : Fin K) (h : Fin H) (L c₁ c₂ : ℝ) (m : ℕ) :
    let n := k.val * H + h.val
    let μ := (onlineSequentialEpisodeLaw H K hH E ρ fallback planner ((m + 1) + n)).rowMeasure
    let f := onlineT3SourceResidualAtPrefix H K hH E fallback planner k h L c₁ c₂ m
    μ[f | onlineT3PrefixSigma H K hH fallback planner (m + 1) n] =ᵐ[μ] 0 := by
  classical
  dsimp
  let n := k.val * H + h.val
  let law := onlineSequentialEpisodeLaw H K hH E ρ fallback planner ((m + 1) + n)
  let μ : @Measure ((Fin K → State) × OnlineOutcomePath.{uState, 0} State ((m + 1) + n)) ⊤ :=
    law.rowMeasure
  let obs := onlineT3PrefixObservation H K hH fallback planner (m + 1) n
  let f := onlineT3SourceResidualAtPrefix H K hH E fallback planner k h L c₁ c₂ m
  have hle : MeasurableSpace.comap obs
      (⊤ : MeasurableSpace ((Fin K → State) × List (OnlineMDPRow State Action H × State))) ≤
      ⊤ := le_top
  haveI : IsProbabilityMeasure μ := by
    dsimp [μ, law]
    infer_instance
  have hf : Integrable f μ := Integrable.of_finite
  have hset (s : Set ((Fin K → State) × OnlineOutcomePath.{uState, 0} State ((m + 1) + n)))
      (hs : MeasurableSet[MeasurableSpace.comap obs
        (⊤ : MeasurableSpace ((Fin K → State) × List (OnlineMDPRow State Action H × State)))] s)
      (hμs : μ s < ⊤) :
      ∫ x in s, f x ∂μ = ∫ x in s, (0 : ℝ) ∂μ := by
    obtain ⟨target, htarget, rfl⟩ := (MeasurableSpace.measurableSet_comap).1 hs
    have hmeas : @MeasurableSet ((Fin K → State) × OnlineOutcomePath.{uState, 0} State
        ((m + 1) + n)) ⊤ (obs ⁻¹' target) := by
      exact MeasurableSpace.measurableSet_top
    have hsum := onlineSequentialEpisodeLaw_sourceT3_prefixSet_sum_zero
      H K hH E ρ fallback planner k h L c₁ c₂ m target
    have hpoint (sample : (Fin K → State) × OnlineOutcomePath.{uState, 0} State
        ((m + 1) + n)) :
        law.prob sample * (obs ⁻¹' target).indicator f sample =
          onlineT3PrefixSetResidualWeight H K hH E ρ fallback planner k h L c₁ c₂ m
            target sample := by
      classical
      change law.prob sample * (if obs sample ∈ target then f sample else 0) = _
      by_cases hx : obs sample ∈ target
      · simp [onlineT3PrefixSetResidualWeight, onlineT3SourceResidualAtPrefix,
          onlineT3PrefixObservation, onlineT3PrefixHistory, obs, f, hx, n, law]
      · simp [onlineT3PrefixSetResidualWeight, onlineT3SourceResidualAtPrefix,
          onlineT3PrefixObservation, onlineT3PrefixHistory, obs, f, hx, n, law]
    calc
      _ = ∫ sample, (obs ⁻¹' target).indicator f sample ∂μ :=
        (MeasureTheory.integral_indicator (μ := μ) (f := f)
          (s := obs ⁻¹' target) hmeas).symm
      _ = ∑ sample, law.prob sample * (obs ⁻¹' target).indicator f sample := by
        rw [FiniteDistribution.rowMeasure_integral]
        rfl
      _ = ∑ sample, onlineT3PrefixSetResidualWeight H K hH E ρ fallback planner
            k h L c₁ c₂ m target sample := by
          apply Finset.sum_congr rfl
          intro sample hs
          exact hpoint sample
      _ = 0 := hsum
      _ = ∫ x in obs ⁻¹' target, (0 : ℝ) ∂μ := by simp
  have hg : Integrable (fun _ : (Fin K → State) × OnlineOutcomePath.{uState, 0} State
      ((m + 1) + n) => (0 : ℝ)) μ := integrable_zero _ _ _
  have hgm : AEStronglyMeasurable[MeasurableSpace.comap obs
      (⊤ : MeasurableSpace ((Fin K → State) × List (OnlineMDPRow State Action H × State)))]
      (fun _ : (Fin K → State) × OnlineOutcomePath.{uState, 0} State
        ((m + 1) + n) => (0 : ℝ)) μ := by
    exact measurable_const.aestronglyMeasurable
  have hcond := MeasureTheory.ae_eq_condExp_of_forall_setIntegral_eq
    (μ := μ) (m := MeasurableSpace.comap obs
      (⊤ : MeasurableSpace ((Fin K → State) × List (OnlineMDPRow State Action H × State))))
    (m₀ := (⊤ : MeasurableSpace
      ((Fin K → State) × OnlineOutcomePath.{uState, 0} State ((m + 1) + n))))
    hle hf (fun s hs hμs => integrableOn_zero)
      (fun s hs hμs => (hset s hs hμs).symm) hgm
  exact hcond.symm

end StatisticalRL.OnlineRL
