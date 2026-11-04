import Formalization.Online.Regret.T8.OnlineT8RowVariance

/-! Actual-law variance and gap proof component: OnlinePredictableTestVariance.
This module supplies an intermediate proof, not the complete T56 theorem. -/
namespace StatisticalRL.OnlineRL
open MeasureTheory ProbabilityTheory
universe uState uAction
variable {State : Type uState} {Action : Type uAction} [Fintype State] [Fintype Action]
noncomputable local instance predVarState : MeasurableSpace State := ⊤

theorem onlinePredictableTest_conditionalVariance
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (ρ : FiniteDistribution State) (fallback : State) (planner : OnlineEpisodePlanner State Action H)
    (n m : ℕ) (φ : (Fin K → State) → List (OnlineMDPRow State Action H × State) → State → ℝ) :
    let μ := (onlineSequentialEpisodeLaw H K hH E ρ fallback planner ((m + 1) + n)).rowMeasure
    let obs := onlineT3PrefixObservation H K hH fallback planner (m + 1) n
    μ[(fun sample => (onlinePredictableTestResidualAtPrefix H K hH E fallback planner n m φ sample)^2) |
      onlineT3PrefixSigma H K hH fallback planner (m + 1) n] =ᵐ[μ]
      (fun sample => (onlineMDPSuccessorRowLaw E
        (onlineEpisodicChoose H K hH sample.1 fallback planner (obs sample).2)).variance
        (φ sample.1 (obs sample).2)) := by
  classical
  dsimp
  let law := onlineSequentialEpisodeLaw H K hH E ρ fallback planner ((m + 1) + n)
  let μ := law.rowMeasure
  let obs := onlineT3PrefixObservation H K hH fallback planner (m + 1) n
  let σ := onlineT3PrefixSigma H K hH fallback planner (m + 1) n
  let θ := fun initial history x =>
    (φ initial history x - (onlineMDPSuccessorRowLaw E
      (onlineEpisodicChoose H K hH initial fallback planner history)).expectation (φ initial history))^2
  let source := onlinePredictableTestResidualAtPrefix H K hH E fallback planner n m φ
  let f : (Fin K → State) × OnlineOutcomePath.{uState, 0} State ((m + 1) + n) → ℝ := fun sample => θ sample.1
    (onlineT3PrefixHistory H K hH fallback planner sample.1 n (m + 1) sample.2)
    (onlineSequentialPathSuffix n (m + 1) sample.2).2.1
  let rowVariance : (Fin K → State) × OnlineOutcomePath.{uState, 0} State ((m + 1) + n) → ℝ := fun sample =>
    (onlineMDPSuccessorRowLaw E (onlineEpisodicChoose H K hH sample.1 fallback planner (obs sample).2)).variance
      (φ sample.1 (obs sample).2)
  have hcent := onlineSequentialEpisodeLaw_predictableTest_condExp_zero H K hH E ρ fallback planner n m θ
  have hf : Integrable f μ := Integrable.of_finite
  have hg : Integrable rowVariance μ := Integrable.of_finite
  have hobs : @Measurable ((Fin K → State) × OnlineOutcomePath.{uState, 0} State ((m + 1) + n))
      ((Fin K → State) × List (OnlineMDPRow State Action H × State)) σ ⊤ obs := by
    intro s hs
    exact (MeasurableSpace.measurableSet_comap).2 ⟨s, hs, rfl⟩
  have hrowFunction : StronglyMeasurable[⊤]
      (fun z : (Fin K → State) × List (OnlineMDPRow State Action H × State) =>
        (onlineMDPSuccessorRowLaw E (onlineEpisodicChoose H K hH z.1 fallback planner z.2)).variance (φ z.1 z.2)) :=
    StronglyMeasurable.of_discrete
  have hgmeas : StronglyMeasurable[σ] rowVariance := by
    simpa [rowVariance, obs] using hrowFunction.comp_measurable hobs
  have hcondg : μ[rowVariance | σ] = rowVariance :=
    MeasureTheory.condExp_of_stronglyMeasurable (show σ ≤ ⊤ from le_top) hgmeas hg
  have hcenterFunction :
      (fun sample => onlinePredictableTestResidualAtPrefix H K hH E fallback planner n m θ sample) =
        fun sample => rowVariance sample - f sample := by
    funext sample
    dsimp [onlinePredictableTestResidualAtPrefix, θ, f, rowVariance, obs, onlineT3PrefixObservation]
    rw [← (onlineMDPSuccessorRowLaw E (onlineEpisodicChoose H K hH sample.1 fallback planner
      (onlineT3PrefixHistory H K hH fallback planner sample.1 n (m + 1) sample.2))).variance_eq_expectation_centered_sq]
  have hcent' := hcent
  dsimp [μ, law, σ] at hcent'
  have hcent'' : μ[rowVariance - f | σ] =ᵐ[μ] 0 := by
    simpa [hcenterFunction] using hcent'
  have hsub := MeasureTheory.condExp_sub hg hf σ
  have htheta : μ[f | σ] =ᵐ[μ] rowVariance := by
    filter_upwards [hcent'', Filter.Eventually.of_forall (fun sample => congrFun hcondg sample), hsub] with sample hz hgval hsubval
    have hdifffun : (μ[rowVariance | σ] - μ[f | σ]) sample = 0 := hsubval.symm.trans hz
    have hdiff : μ[rowVariance | σ] sample - μ[f | σ] sample = 0 := by simpa using hdifffun
    rw [hgval] at hdiff
    linarith
  have hsourceEq : (fun sample => source sample ^ 2) = f := by
    funext sample
    simp [source, onlinePredictableTestResidualAtPrefix, θ, f]
    ring
  simpa [source, obs, σ, μ, law, hsourceEq, rowVariance] using htheta
end StatisticalRL.OnlineRL
