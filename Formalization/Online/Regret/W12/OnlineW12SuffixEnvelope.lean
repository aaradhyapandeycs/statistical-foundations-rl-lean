import Formalization.Online.Regret.W12.OnlineW12ActualPoint
import Formalization.Online.Regret.W12.OnlineW12MaskedAggregation

/-! Same-experiment suffix proof component: OnlineW12SuffixEnvelope.
Scope and source confidence are established only by the final applying theorem. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators
variable {State Action : Type*} [Fintype State] [Fintype Action]
noncomputable local instance w12SuffixState : DecidableEq State := Classical.decEq State
noncomputable local instance w12SuffixAction : DecidableEq Action := Classical.decEq Action

noncomputable def onlineW12SuffixIndices (H K : ℕ) (h0 : Fin H) : Finset (Fin H × Fin K) :=
  Finset.univ.filter (fun i => h0.val ≤ i.1.val)

noncomputable def onlineActualW2RadiusTerm
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (initial : Fin K → State) (fallback : State) (path : OnlineOutcomePath State (K * H))
    (δ c₁ c₂ : ℝ) (h : Fin H) (k : Fin K) : ℝ :=
  let planner := onlineCappedGreedyPlanner E (Real.log (1 / δ)) c₁ c₂
  let sa := onlineActualStageRowSequence H K hH initial fallback planner path h k.val
  let n := onlineActualW1Count H K hH E initial fallback path δ c₁ c₂ h k
  let U := onlineActualOptimisticContinuation H K hH E initial fallback path δ c₁ c₂ h k
  let P := onlineActualPolicyContinuation H K hH E initial fallback path δ c₁ c₂ h k
  let d := ((E h).transition sa.1 sa.2).expectation (fun s => (U s - P s)^2)
  if 3 ≤ n then Real.sqrt (2 * (Fintype.card State : ℝ) * Real.log (1 / δ) * d / n) +
    (Fintype.card State : ℝ) * H * Real.log (1 / δ) / n else H

/-- Every deterministic suffix, simultaneously, is bounded by the same full
path radius sums. Both input certificates are the single actual-history
events used globally; no additional union over suffixes is needed. -/
theorem onlineActualW12_all_suffix_le_full_radii
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (initial : Fin K → State) (fallback : State) (path : OnlineOutcomePath State (K * H))
    (δ c₁ c₂ : ℝ) (hδ : 0 < δ) (hδsmall : δ ≤ 2 / 5) (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂)
    (hW1 : onlineObservedTrueW1Certificates H K E δ
      (onlineSequentialPathHistory (onlineEpisodicChoose H K hH initial fallback
        (onlineCappedGreedyPlanner E (Real.log (1 / δ)) c₁ c₂)) (K * H) [] path))
    (hW2 : onlineObservedW2CoordinateCertificates H K E δ
      (onlineSequentialPathHistory (onlineEpisodicChoose H K hH initial fallback
        (onlineCappedGreedyPlanner E (Real.log (1 / δ)) c₁ c₂)) (K * H) [] path))
    (hoptimism : onlineHistoryAllStageTrajectoryOptimism H K E δ c₁ c₂
      (onlineSequentialPathHistory (onlineEpisodicChoose H K hH initial fallback
        (onlineCappedGreedyPlanner E (Real.log (1 / δ)) c₁ c₂)) (K * H) [] path)) :
    ∀ h0 : Fin H,
      |∑ i ∈ onlineW12SuffixIndices H K h0, onlineActualW1Point H K hH E initial fallback path δ c₁ c₂ i.1 i.2| ≤
        ∑ i : Fin H × Fin K, onlineActualW1RadiusTerm H K hH E initial fallback path δ c₁ c₂ i.1 i.2 ∧
      |∑ i ∈ onlineW12SuffixIndices H K h0, onlineActualW2Point H K hH E initial fallback path δ c₁ c₂ i.1 i.2| ≤
        ∑ i : Fin H × Fin K, onlineActualW2RadiusTerm H K hH E initial fallback path δ c₁ c₂ i.1 i.2 := by
  classical
  intro h0
  constructor
  · exact onlineW12_abs_masked_sum_le_full_radius Finset.univ (onlineW12SuffixIndices H K h0)
      (Finset.subset_univ _) _ _ (fun i _ =>
        onlineActualW1Point_abs_le_radius H K hH E initial fallback path δ c₁ c₂ hW1 i.1 i.2)
  · exact onlineW12_abs_masked_sum_le_full_radius Finset.univ (onlineW12SuffixIndices H K h0)
      (Finset.subset_univ _) _ _ (fun i _ =>
        onlineActualW2Point_abs_le_radius H K hH E initial fallback path δ c₁ c₂ hδ hδsmall hc₁ hc₂ hW2 hoptimism i.1 i.2)
end StatisticalRL.OnlineRL
