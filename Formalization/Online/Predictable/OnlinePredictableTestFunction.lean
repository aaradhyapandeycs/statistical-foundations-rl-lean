import Formalization.Online.Regret.T3.OnlineRegretT3CommonFiltration

/-! generic predictable-test centering under the actual sequential
reset/path law. The function of the fresh outcome may depend arbitrarily on
its reset vector and revealed prefix. No independence or conditional-mean
hypothesis is assumed. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators
open MeasureTheory ProbabilityTheory
universe uState uAction
variable {State : Type uState} {Action : Type uAction}
  [Fintype State] [Fintype Action]
noncomputable local instance predictableStateMeasurable : MeasurableSpace State := ⊤
noncomputable local instance predictableStateDecidable : DecidableEq State := Classical.decEq State
noncomputable local instance predictableActionDecidable : DecidableEq Action := Classical.decEq Action

theorem onlineSequentialEpisodeLaw_predictableTest_fiber_sum_zero
    {State Action : Type*} [Fintype State] [Fintype Action]
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (ρ : FiniteDistribution State) (initial : Fin K → State) (fallback : State)
    (planner : OnlineEpisodePlanner State Action H)
    (n m : ℕ) (tail : State → ℝ)
    (prePath : OnlineOutcomePath State n) :
    let choose := onlineEpisodicChoose H K hH initial fallback planner
    let rowLaw := onlineMDPSuccessorRowLaw E
    let history := onlineSequentialPathHistory choose n [] prePath
    (∑ suffix : OnlineOutcomePath State (m + 1),
      (onlineSequentialEpisodeLaw H K hH E ρ fallback planner ((m + 1) + n)).prob
        (initial, onlineSequentialPathAppend n (m + 1) prePath suffix) *
        ((rowLaw (choose history)).expectation tail - tail suffix.2.1)) = 0 := by
  classical
  dsimp
  let choose := onlineEpisodicChoose H K hH initial fallback planner
  let rowLaw := onlineMDPSuccessorRowLaw E
  let history := onlineSequentialPathHistory choose n [] prePath
  let f : State → ℝ := fun x => (rowLaw (choose history)).expectation tail - tail x
  have hrow : (rowLaw (choose history)).expectation f = 0 := by
    dsimp [f]
    rw [FiniteDistribution.expectation_sub,
      FiniteDistribution.expectation_const]
    ring
  have hsum := onlineSequentialOutcomeLaw_continuation_first_sum
    rowLaw choose n m [] prePath f
  change (∑ suffix : OnlineOutcomePath State (m + 1),
      ((onlineInitialVectorLaw ρ K).prob initial *
        (onlineSequentialOutcomeLaw rowLaw choose ((m + 1) + n) []).prob
          (onlineSequentialPathAppend n (m + 1) prePath suffix)) *
        f suffix.2.1) = 0
  calc
    _ = (onlineInitialVectorLaw ρ K).prob initial *
        ∑ suffix : OnlineOutcomePath State (m + 1),
          (onlineSequentialOutcomeLaw rowLaw choose ((m + 1) + n) []).prob
            (onlineSequentialPathAppend n (m + 1) prePath suffix) * f suffix.2.1 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro suffix hsuffix
      ring
    _ = (onlineInitialVectorLaw ρ K).prob initial *
        ((onlineSequentialOutcomeLaw rowLaw choose n []).prob prePath *
          (rowLaw (choose history)).expectation f) := by
      rw [hsum]
    _ = 0 := by rw [hrow]; ring

noncomputable def onlinePredictableTestPrefixWeight
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (ρ : FiniteDistribution State) (fallback : State)
    (planner : OnlineEpisodePlanner State Action H)
    (n m : ℕ)
    (θ : (Fin K → State) → List (OnlineMDPRow State Action H × State) → State → ℝ)
    (target : Set ((Fin K → State) × List (OnlineMDPRow State Action H × State)))
    (sample : (Fin K → State) × OnlineOutcomePath.{uState, 0} State
      ((m + 1) + n)) : ℝ := by
  classical
  let history := onlineT3PrefixHistory H K hH fallback planner sample.1 n (m + 1) sample.2
  let choose := onlineEpisodicChoose H K hH sample.1 fallback planner
  let rowLaw := onlineMDPSuccessorRowLaw E
  let tail := θ sample.1 history
  exact if (sample.1, history) ∈ target then
    (onlineSequentialEpisodeLaw H K hH E ρ fallback planner ((m + 1) + n)).prob sample *
      ((rowLaw (choose history)).expectation tail -
        tail (onlineSequentialPathSuffix n (m + 1) sample.2).2.1)
    else 0

/-- The actual joint reset/path weighted residual has zero finite sum over the
preimage of any set of `(reset vector, observed n-record history)` values.
The history map is the actual causal source selector. -/
theorem onlineSequentialEpisodeLaw_predictableTest_prefixSet_sum_zero
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (ρ : FiniteDistribution State) (fallback : State)
    (planner : OnlineEpisodePlanner State Action H)
    (n m : ℕ)
    (θ : (Fin K → State) → List (OnlineMDPRow State Action H × State) → State → ℝ)
    (target : Set ((Fin K → State) × List (OnlineMDPRow State Action H × State))) :
      (∑ sample : (Fin K → State) × OnlineOutcomePath.{uState, 0} State ((m + 1) + n),
      onlinePredictableTestPrefixWeight H K hH E ρ fallback planner n m θ
        target sample) = 0 := by
  classical
  let e : ((Fin K → State) × OnlineOutcomePath.{uState, 0} State ((m + 1) + n)) ≃
      (Fin K → State) ×
        (OnlineOutcomePath.{uState, 0} State n × OnlineOutcomePath.{uState, 0} State (m + 1)) :=
    Equiv.prodCongr (Equiv.refl _) (onlineSequentialPathSplitEquiv n (m + 1))
  let f := onlinePredictableTestPrefixWeight H K hH E ρ fallback planner n m θ target
  let g := fun split : (Fin K → State) ×
      (OnlineOutcomePath.{uState, 0} State n × OnlineOutcomePath.{uState, 0} State (m + 1)) =>
    let history := onlineSequentialPathHistory
      (onlineEpisodicChoose H K hH split.1 fallback planner) n [] split.2.1
    let choose := onlineEpisodicChoose H K hH split.1 fallback planner
    let rowLaw := onlineMDPSuccessorRowLaw E
    let tail := θ split.1 history
    if (split.1, history) ∈ target then
      (onlineSequentialEpisodeLaw H K hH E ρ fallback planner ((m + 1) + n)).prob
          (split.1, onlineSequentialPathAppend n (m + 1) split.2.1 split.2.2) *
        ((rowLaw (choose history)).expectation tail - tail split.2.2.2.1)
    else 0
  have hsum : (∑ sample, f sample) = ∑ split, g split := by
    apply Fintype.sum_equiv e f g
    intro sample
    rcases sample with ⟨initial, path⟩
    simp [e, Equiv.prodCongr_apply, Equiv.refl_apply,
      onlineSequentialPathSplitEquiv, onlineT3PrefixHistory,
      onlinePredictableTestPrefixWeight, f, g,
      onlineSequentialPathAppend_prefix_suffix]
  rw [hsum]
  simp only [Fintype.sum_prod_type]
  apply Finset.sum_eq_zero
  intro initial hi
  apply Finset.sum_eq_zero
  intro prePath hpre
  by_cases htarget :
      (initial, onlineSequentialPathHistory
        (onlineEpisodicChoose H K hH initial fallback planner) n [] prePath) ∈ target
  · simp only [g, htarget, ↓reduceIte]
    exact onlineSequentialEpisodeLaw_predictableTest_fiber_sum_zero
      H K hH E ρ initial fallback planner n m
        (θ initial (onlineSequentialPathHistory
          (onlineEpisodicChoose H K hH initial fallback planner) n [] prePath)) prePath
  · simp [g, htarget]

noncomputable def onlinePredictableTestResidualAtPrefix
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (fallback : State) (planner : OnlineEpisodePlanner State Action H)
    (n m : ℕ)
    (θ : (Fin K → State) → List (OnlineMDPRow State Action H × State) → State → ℝ)
    (sample : (Fin K → State) × OnlineOutcomePath.{uState, 0} State
      ((m + 1) + n)) : ℝ := by
  let history := onlineT3PrefixHistory H K hH fallback planner sample.1 n (m + 1) sample.2
  let choose := onlineEpisodicChoose H K hH sample.1 fallback planner
  let rowLaw := onlineMDPSuccessorRowLaw E
  let tail := θ sample.1 history
  exact (rowLaw (choose history)).expectation tail -
    tail (onlineSequentialPathSuffix n (m + 1) sample.2).2.1

theorem onlineSequentialEpisodeLaw_predictableTest_condExp_zero
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (ρ : FiniteDistribution State) (fallback : State)
    (planner : OnlineEpisodePlanner State Action H)
    (n m : ℕ)
    (θ : (Fin K → State) → List (OnlineMDPRow State Action H × State) → State → ℝ) :
    let μ := (onlineSequentialEpisodeLaw H K hH E ρ fallback planner ((m + 1) + n)).rowMeasure
    let f := onlinePredictableTestResidualAtPrefix H K hH E fallback planner n m θ
    μ[f | onlineT3PrefixSigma H K hH fallback planner (m + 1) n] =ᵐ[μ] 0 := by
  classical
  dsimp
  let law := onlineSequentialEpisodeLaw H K hH E ρ fallback planner ((m + 1) + n)
  let μ : @Measure ((Fin K → State) × OnlineOutcomePath.{uState, 0} State ((m + 1) + n)) ⊤ :=
    law.rowMeasure
  let obs := onlineT3PrefixObservation H K hH fallback planner (m + 1) n
  let f := onlinePredictableTestResidualAtPrefix H K hH E fallback planner n m θ
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
    have hsum := onlineSequentialEpisodeLaw_predictableTest_prefixSet_sum_zero
      H K hH E ρ fallback planner n m θ target
    have hpoint (sample : (Fin K → State) × OnlineOutcomePath.{uState, 0} State
        ((m + 1) + n)) :
        law.prob sample * (obs ⁻¹' target).indicator f sample =
          onlinePredictableTestPrefixWeight H K hH E ρ fallback planner n m θ
            target sample := by
      classical
      change law.prob sample * (if obs sample ∈ target then f sample else 0) = _
      by_cases hx : obs sample ∈ target
      · simp [onlinePredictableTestPrefixWeight, onlinePredictableTestResidualAtPrefix,
          onlineT3PrefixObservation, onlineT3PrefixHistory, obs, f, law]
      · simp [onlinePredictableTestPrefixWeight, onlinePredictableTestResidualAtPrefix,
          onlineT3PrefixObservation, onlineT3PrefixHistory, obs, f, law]
    calc
      _ = ∫ sample, (obs ⁻¹' target).indicator f sample ∂μ :=
        (MeasureTheory.integral_indicator (μ := μ) (f := f)
          (s := obs ⁻¹' target) hmeas).symm
      _ = ∑ sample, law.prob sample * (obs ⁻¹' target).indicator f sample := by
        rw [FiniteDistribution.rowMeasure_integral]
        rfl
      _ = ∑ sample, onlinePredictableTestPrefixWeight H K hH E ρ fallback planner
            n m θ target sample := by
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
