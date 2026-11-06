import Formalization.Online.QLearning.HalfBudgetConfidence
import Formalization.Online.QLearning.ActualStageErrorBridge
import Formalization.Online.QLearning.ActualWeightedRegretTail

/-! Exact same-bonus confidence allocation for the actual regret proof.
The cb=2 bonus keeps log(SAT/δ); only the martingale's failure budget is δ/2. -/
namespace StatisticalRL.OnlineRL
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
universe u v
variable {State : Type u} {Action : Type v} [Fintype State] [Fintype Action]
local instance jointRegretStateMeasurable : MeasurableSpace State := ⊤
local instance jointRegretSampleMeasurable (H K : ℕ) :
    MeasurableSpace ((Fin K → State) × OnlineOutcomePath.{u,0} State (K*H)) := ⊤

/-- The source regret is bounded by the actual state-selector stage-zero
error on the single simultaneous optimism event. -/
theorem qLearning_actualRegret_le_episodePolicyError {H K : ℕ} (hH : 0 < H)
    (E : Fin H → EnvironmentStage State Action) (initial : Fin K → State) (fallback : State)
    (δ cb : ℝ) (path : OnlineOutcomePath.{u,0} State (K*H))
    (hgood : qLearningSourceOptimismGood hH E fallback δ cb (initial,path)) :
    let L := Real.log ((Fintype.card (OnlineMDPRow State Action H):ℝ)*(K:ℝ)/δ)
    let bonus := fun i : ℕ => cb*Real.sqrt ((H:ℝ)^3*L/(i:ℝ))
    qLearningActualRegret hH E bonus initial fallback path ≤
      qLearningActualEpisodePolicyError hH E bonus initial fallback path 0 := by
  dsimp only
  rw [qLearning_actualEpisodePolicyError_zero]
  exact qLearning_actual_regret_le_optimistic hH E initial fallback δ cb path hgood

/-- One event contains both the actual algorithm's source optimism/error
bounds and the signed weighted trajectory fluctuation, with strict probability
above 1−δ. The fixed bonus coefficient is chosen before all parameters. -/
theorem qLearning_actual_jointRegretEvent_confidence
    (H K : ℕ) (hH : 0 < H) (hK : 0 < K)
    (E : Fin H → EnvironmentStage State Action) (ρ : FiniteDistribution State)
    (fallback : State) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1)
    (w : Fin H → ℝ) (M : ℝ≥0) (hM : 0 < M) (hweight : ∀ h, |w h| ≤ (M:ℝ)) :
    let L := Real.log ((Fintype.card (OnlineMDPRow State Action H):ℝ)*(K:ℝ)/δ)
    let bonus := fun i : ℕ => 2*Real.sqrt ((H:ℝ)^3*L/(i:ℝ))
    let μ := (onlineSequentialEpisodeLaw H K hH E ρ fallback
      (qLearningActualEpisodePlanner hH E bonus) (K*H)).rowMeasure
    1-δ < μ.real {sample : (Fin K → State) × OnlineOutcomePath.{u,0} State (K*H) |
      qLearningSourceOptimismGood hH E fallback δ 2 sample ∧
      |∑ n ∈ Finset.range (K*H), qLearningRegretChronologicalY hH E bonus fallback w n sample| ≤
        Real.sqrt (2*((K:ℝ)*(H:ℝ)*((M:ℝ)*(H:ℝ))^2)*Real.log (4/δ))} := by
  classical
  let L := Real.log ((Fintype.card (OnlineMDPRow State Action H):ℝ)*(K:ℝ)/δ)
  let bonus := fun i : ℕ => 2*Real.sqrt ((H:ℝ)^3*L/(i:ℝ))
  let μ := (onlineSequentialEpisodeLaw H K hH E ρ fallback
      (qLearningActualEpisodePlanner hH E bonus) (K*H)).rowMeasure
  haveI : IsProbabilityMeasure μ := by dsimp [μ]; infer_instance
  let A : Set ((Fin K → State) × OnlineOutcomePath.{u,0} State (K*H)) :=
    {sample | qLearningSourceOptimismGood hH E fallback δ 2 sample}
  let B : Set ((Fin K → State) × OnlineOutcomePath.{u,0} State (K*H)) :=
    {sample | |∑ n ∈ Finset.range (K*H), qLearningRegretChronologicalY hH E bonus fallback w n sample| ≤
      Real.sqrt (2*((K:ℝ)*(H:ℝ)*((M:ℝ)*(H:ℝ))^2)*Real.log (4/δ))}
  have hA : 1-δ/2 ≤ μ.real A :=
    qLearning_sourceOptimism_confidence_halfBudget H K hH hK E ρ fallback δ 2 hδ hδ1 (by norm_num)
  have hε : 0<δ/2 := by positivity
  have hε1 : δ/2<1 := by linarith
  have hB0 := qLearning_actual_weightedRegretResidual_confidence H K hH hK E ρ bonus fallback
    w M hM hweight (δ/2) hε hε1
  have he : (2:ℝ)/(δ/2)=4/δ := by rw [div_div_eq_mul_div]; ring
  have hB : 1-δ/2 < μ.real B := by simpa only [he] using hB0
  have hAm : MeasurableSet A := (Set.to_countable A).measurableSet
  have hBm : MeasurableSet B := (Set.to_countable B).measurableSet
  have hAc := measureReal_compl (μ:=μ) hAm
  have hBc := measureReal_compl (μ:=μ) hBm
  rw [probReal_univ] at hAc hBc
  have hbad : μ.real (A∩B)ᶜ < δ := by
    rw [Set.compl_inter]
    exact (measureReal_union_le _ _).trans_lt (by linarith)
  have hAB := measureReal_compl (μ:=μ) (hAm.inter hBm)
  rw [probReal_univ] at hAB
  change 1-δ < μ.real (A∩B)
  linarith

end StatisticalRL.OnlineRL
