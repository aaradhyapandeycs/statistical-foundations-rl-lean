import Formalization.Online.Regret.T4.OnlineT4SuffixAzuma
import Formalization.Probability.FiniteStrictTwoSidedTail

/-! Same-experiment suffix proof component: OnlineT4SuffixConfidence.
Scope and source confidence are established only by the final applying theorem. -/
namespace StatisticalRL.OnlineRL
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
universe uState uAction
variable {State : Type uState} {Action : Type uAction}
  [Fintype State] [Fintype Action]
noncomputable local instance suffixConfidenceStateMeasurable : MeasurableSpace State :=
  StatisticalRL.FiniteDistribution.empiricalRowStateMeasurable
noncomputable local instance suffixConfidenceSampleMeasurable (H K : ℕ) :
    MeasurableSpace ((Fin K → State) × OnlineOutcomePath.{uState, 0} State (K * H)) :=
  StatisticalRL.FiniteDistribution.empiricalRowStateMeasurable

theorem onlineT4SuffixActualSum_hasSubgaussianMGF
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (ρ : FiniteDistribution State) (fallback : State)
    (planner : OnlineEpisodePlanner State Action H) (j : Fin H) :
    let μ := (onlineSequentialEpisodeLaw H K hH E ρ fallback planner (K * H)).rowMeasure
    HasSubgaussianMGF
      (fun sample : (Fin K → State) × OnlineOutcomePath.{uState, 0} State (K * H) =>
        ∑ k : Fin K, onlineT4SuffixEpisodeIncrement H K hH E fallback planner j.val k sample)
      ((K : ℝ≥0) * (H : ℝ≥0)^2) μ := by
  dsimp
  have hs := onlineT4SuffixEpisodeSum_hasSubgaussianMGF H K hH E ρ fallback planner j
  apply hs.congr
  apply Filter.Eventually.of_forall
  intro sample
  dsimp only
  rw [Finset.sum_range]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [onlineT4SuffixPaddedEpisodeY, dif_pos k.isLt]

theorem onlineT4SuffixActualSum_confidence_strict
    (H K : ℕ) (hH : 0 < H) (hK : 0 < K)
    (E : Fin H → EnvironmentStage State Action) (ρ : FiniteDistribution State)
    (fallback : State) (planner : OnlineEpisodePlanner State Action H)
    (j : Fin H) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    let μ := (onlineSequentialEpisodeLaw H K hH E ρ fallback planner (K * H)).rowMeasure
    1 - 2 * δ < μ.real {sample : (Fin K → State) × OnlineOutcomePath.{uState, 0} State (K * H) |
      |∑ k : Fin K, onlineT4SuffixEpisodeIncrement H K hH E fallback planner j.val k sample| ≤
        Real.sqrt (2 * (K : ℝ) * (H : ℝ)^2 * Real.log (1 / δ))} := by
  dsimp
  let μ := (onlineSequentialEpisodeLaw H K hH E ρ fallback planner (K * H)).rowMeasure
  haveI : IsProbabilityMeasure μ := by dsimp [μ]; infer_instance
  let X := fun sample : (Fin K → State) × OnlineOutcomePath.{uState, 0} State (K * H) =>
    ∑ k : Fin K, onlineT4SuffixEpisodeIncrement H K hH E fallback planner j.val k sample
  have hc : 0 < (K : ℝ≥0) * (H : ℝ≥0)^2 := by
    have hK' : 0 < (K : ℝ≥0) := by exact_mod_cast hK
    have hH' : 0 < (H : ℝ≥0) := by exact_mod_cast hH
    exact mul_pos hK' (pow_pos hH' _)
  have ht := StatisticalRL.HasSubgaussianMGF.measure_abs_le_sqrt_gt_of_finite
    μ X ((K : ℝ≥0) * (H : ℝ≥0)^2) hc
    (onlineT4SuffixActualSum_hasSubgaussianMGF H K hH E ρ fallback planner j) δ hδ hδ1
  simpa only [X, NNReal.coe_mul, NNReal.coe_pow, NNReal.coe_natCast, mul_assoc] using ht

theorem onlineT4SuffixActualSum_allStages_confidence
    (H K : ℕ) (hH : 0 < H) (hK : 0 < K)
    (E : Fin H → EnvironmentStage State Action) (ρ : FiniteDistribution State)
    (fallback : State) (planner : OnlineEpisodePlanner State Action H)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    let μ := (onlineSequentialEpisodeLaw H K hH E ρ fallback planner (K * H)).rowMeasure
    1 - 2 * (H : ℝ) * δ ≤ μ.real
      {sample : (Fin K → State) × OnlineOutcomePath.{uState, 0} State (K * H) |
        ∀ j : Fin H,
          |∑ k : Fin K, onlineT4SuffixEpisodeIncrement H K hH E fallback planner j.val k sample| ≤
            Real.sqrt (2 * (K : ℝ) * (H : ℝ)^2 * Real.log (1 / δ))} := by
  dsimp
  let μ := (onlineSequentialEpisodeLaw H K hH E ρ fallback planner (K * H)).rowMeasure
  haveI : IsProbabilityMeasure μ := by dsimp [μ]; infer_instance
  let good : Fin H → Set ((Fin K → State) × OnlineOutcomePath.{uState, 0} State (K * H)) :=
    fun j => {sample |
      |∑ k : Fin K, onlineT4SuffixEpisodeIncrement H K hH E fallback planner j.val k sample| ≤
        Real.sqrt (2 * (K : ℝ) * (H : ℝ)^2 * Real.log (1 / δ))}
  have hb (j : Fin H) : μ.real (good j)ᶜ ≤ 2 * δ := by
    have hp := onlineT4SuffixActualSum_confidence_strict H K hH hK E ρ fallback planner j δ hδ hδ1
    have hc := measureReal_compl (μ := μ) ((Set.to_countable (good j)).measurableSet)
    rw [probReal_univ] at hc
    change 1 - 2 * δ < μ.real (good j) at hp
    linarith only [hp, hc]
  let allGood := {sample | ∀ j : Fin H, sample ∈ good j}
  have heq : allGoodᶜ = ⋃ j : Fin H, (good j)ᶜ := by
    ext sample
    simp only [allGood, Set.mem_compl_iff, Set.mem_setOf_eq, Set.mem_iUnion]
    exact not_forall
  have hbad : μ.real allGoodᶜ ≤ 2 * (H : ℝ) * δ := by
    calc
      _ = μ.real (⋃ j : Fin H, (good j)ᶜ) := congrArg μ.real heq
      _ ≤ ∑ j : Fin H, μ.real (good j)ᶜ := measureReal_iUnion_fintype_le _
      _ ≤ ∑ _j : Fin H, 2 * δ := Finset.sum_le_sum (fun j hj => hb j)
      _ = 2 * (H : ℝ) * δ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  have hc := measureReal_compl (μ := μ) ((Set.to_countable allGood).measurableSet)
  rw [probReal_univ] at hc
  change 1 - 2 * (H : ℝ) * δ ≤ μ.real allGood
  linarith only [hbad, hc]

end StatisticalRL.OnlineRL
