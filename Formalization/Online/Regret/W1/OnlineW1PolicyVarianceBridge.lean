import Formalization.Online.Regret.W1.W1Definitions
import Formalization.Online.Regret.W1.OnlineW1ActualCumulative
import Formalization.Online.SourceOptimism.SourceOptimismAllocation
import Formalization.Online.SourceOptimism.VarianceGapTransfer

/-! OnlineW1PolicyVarianceBridge: an intermediate component for the corrected-zero-count, fixed-tie W₁ analysis. Source-facing K≥2 scope and remaining W₂/regret obligations are stated at the final export. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators
variable {State Action : Type*} [Fintype State] [Fintype Action]
noncomputable local instance OnlineW1PolicyVarianceBridgeLocalInstance1 : DecidableEq State := Classical.decEq State
noncomputable local instance OnlineW1PolicyVarianceBridgeLocalInstance2 : DecidableEq Action := Classical.decEq Action

/-- Pointwise ordered values give the two-term variance comparison. -/
theorem onlineVariance_ordered_three
    (d : FiniteDistribution State) (V P U : State → ℝ)
    (hPV : ∀ s, P s ≤ V s) (hVU : ∀ s, V s ≤ U s) :
    d.variance V ≤ 2 * d.variance P + 2 * d.expectation (fun s => (U s - P s)^2) := by
  let D := fun s => V s - P s
  have hadd := d.sqrt_variance_add_le P D
  have heq : (fun s => P s + D s) = V := by funext s; dsimp [D]; ring
  rw [heq] at hadd
  have hv := d.variance_nonneg V
  have hp := d.variance_nonneg P
  have hd := d.variance_nonneg D
  have hsqv := Real.sq_sqrt hv
  have hsqp := Real.sq_sqrt hp
  have hsqd := Real.sq_sqrt hd
  have hdiff : d.variance D ≤ d.expectation (fun s => (U s - P s)^2) := by
    apply (d.variance_le_expectation_sq D).trans
    apply d.expectation_mono
    intro s
    dsimp [D]
    have ha : 0 ≤ V s - P s := sub_nonneg.mpr (hPV s)
    have hb : V s - P s ≤ U s - P s := sub_le_sub_right (hVU s) _
    nlinarith [sq_nonneg (U s - V s)]
  have hs := sq_nonneg (Real.sqrt (d.variance P) - Real.sqrt (d.variance D))
  nlinarith [Real.sqrt_nonneg (d.variance V), Real.sqrt_nonneg (d.variance P),
    Real.sqrt_nonneg (d.variance D)]





/-- The same actual all-stage optimism event supplies every ordering needed
for T₆-optimal ≤ 2 T₆-policy + 2 T₆-difference, including the terminal
continuation. -/
theorem onlineActualT6Optimal_le_policy_difference
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (initial : Fin K → State) (fallback : State) (path : OnlineOutcomePath State (K * H))
    (δ c₁ c₂ : ℝ)
    (hoptimism : onlineHistoryAllStageTrajectoryOptimism H K E δ c₁ c₂
      (onlineSequentialPathHistory
        (onlineEpisodicChoose H K hH initial fallback
          (onlineCappedGreedyPlanner E (Real.log (1 / δ)) c₁ c₂))
        (K * H) [] path)) :
    onlineActualW1T6Optimal H K hH E initial fallback path δ c₁ c₂ ≤
      2 * onlineActualT6Policy H K hH E initial fallback path δ c₁ c₂ +
      2 * onlineActualT6Difference H K hH E initial fallback path δ c₁ c₂ := by
  classical
  let planner := onlineCappedGreedyPlanner E (Real.log (1 / δ)) c₁ c₂
  let history := onlineSequentialPathHistory
    (onlineEpisodicChoose H K hH initial fallback planner) (K * H) [] path
  have hpoint : ∀ h : Fin H, ∀ k : Fin K,
      onlineActualW1Variance H K hH E initial fallback path δ c₁ c₂ h k ≤
      2 * (let sa := onlineActualStageRowSequence H K hH initial fallback planner path h k.val
        ((E h).transition sa.1 sa.2).variance
          (onlineActualPolicyContinuation H K hH E initial fallback path δ c₁ c₂ h k)) +
      2 * (let sa := onlineActualStageRowSequence H K hH initial fallback planner path h k.val
        ((E h).transition sa.1 sa.2).expectation (fun s =>
          (onlineActualOptimisticContinuation H K hH E initial fallback path δ c₁ c₂ h k s -
            onlineActualPolicyContinuation H K hH E initial fallback path δ c₁ c₂ h k s)^2)) := by
    intro h k
    let sa := onlineActualStageRowSequence H K hH initial fallback planner path h k.val
    let V := onlineTrueSuffixRowFamily E (h, sa)
    let P := onlineActualPolicyContinuation H K hH E initial fallback path δ c₁ c₂ h k
    let U := onlineActualOptimisticContinuation H K hH E initial fallback path δ c₁ c₂ h k
    have hPV : ∀ s, P s ≤ V s := by
      intro s
      let π := onlineCappedEpisodePolicy H hH E history k.val (Real.log (1 / δ)) c₁ c₂
      let a : Action := Classical.choice ((E h).action_nonempty)
      have hd := (EnvironmentStage.greedy_suffix_dominates (List.ofFn E) π (h.val + 1) s a).1
      simpa [P, V, π, onlineActualPolicyContinuation, onlineTrueSuffixRowFamily, history, planner,
        EnvironmentStage.greedy_suffix_value] using hd
    have hVU : ∀ s, V s ≤ U s := by
      intro s
      by_cases hn : h.val + 1 < H
      · let next : Fin H := ⟨h.val + 1, hn⟩
        have ho := (hoptimism k next).1 s
        simpa [V, U, next, onlineTrueSuffixRowFamily, onlineActualOptimisticContinuation,
          history, planner, EnvironmentStage.greedy_suffix_value] using ho
      · have he : H ≤ h.val + 1 := by omega
        have htrue : (List.ofFn E).drop (h.val + 1) = [] := by
          apply List.drop_eq_nil_of_le
          simpa using he
        have hobs : (onlinePreEpisodePlanningStages E history k.val).drop (h.val + 1) = [] := by
          apply List.drop_eq_nil_of_le
          simpa [onlinePreEpisodePlanningStages] using he
        change EnvironmentStage.optimalValue ((List.ofFn E).drop (h.val + 1)) s ≤
          onlineCappedBackwardValue (H : ℝ) (Real.log (1 / δ)) c₁ c₂
            ((onlinePreEpisodePlanningStages E history k.val).drop (h.val + 1)) s
        rw [htrue, hobs]
        rfl
    change ((E h).transition sa.1 sa.2).variance V ≤
      2 * ((E h).transition sa.1 sa.2).variance P +
      2 * ((E h).transition sa.1 sa.2).expectation (fun s => (U s - P s)^2)
    exact onlineVariance_ordered_three _ V P U hPV hVU
  unfold onlineActualW1T6Optimal onlineActualT6Policy onlineActualT6Difference
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro h hh
  apply Finset.sum_le_sum
  intro k hk
  exact hpoint h k
/-- On the same observed W₁ certificate and optimism event, replace optimal
variance by the actual policy variance plus the actual squared gap. -/
theorem onlineActualW1_le_policyVarianceBudget
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (initial : Fin K → State) (fallback : State) (path : OnlineOutcomePath State (K * H))
    (δ c₁ c₂ : ℝ) (hδ : 0 < δ) (hδsmall : δ ≤ 2 / 5)
    (hcert : onlineObservedTrueW1Certificates H K E δ
      (onlineSequentialPathHistory
        (onlineEpisodicChoose H K hH initial fallback
          (onlineCappedGreedyPlanner E (Real.log (1 / δ)) c₁ c₂))
        (K * H) [] path))
    (hoptimism : onlineHistoryAllStageTrajectoryOptimism H K E δ c₁ c₂
      (onlineSequentialPathHistory
        (onlineEpisodicChoose H K hH initial fallback
          (onlineCappedGreedyPlanner E (Real.log (1 / δ)) c₁ c₂))
        (K * H) [] path)) :
    let L := Real.log (1 / (2 * δ))
    let A := (Fintype.card State : ℝ) * (Fintype.card Action : ℝ) * H
    let R := A * (1 + Real.log (K + 1 : ℝ))
    (∑ k : Fin K, onlineActualEpisodeW1 H K hH E initial fallback path k δ c₁ c₂) ≤
      (H : ℝ) * (3 * A) +
      Real.sqrt (2 * L * (2 * onlineActualT6Policy H K hH E initial fallback path δ c₁ c₂ +
        2 * onlineActualT6Difference H K hH E initial fallback path δ c₁ c₂)) * Real.sqrt R +
      (2 * H * L / 3) * R := by
  let L := Real.log (1 / (2 * δ))
  let A := (Fintype.card State : ℝ) * (Fintype.card Action : ℝ) * H
  let R := A * (1 + Real.log (K + 1 : ℝ))
  have hL : 0 ≤ L := by
    apply (Real.log_pos ?_).le
    apply (lt_div_iff₀ (by positivity : 0 < 2 * δ)).2
    linarith
  have hb := onlineActualW1_le_trueVarianceBudget H K hH E initial fallback path δ c₁ c₂ hδ hδsmall hcert
  have hv := onlineActualT6Optimal_le_policy_difference H K hH E initial fallback path δ c₁ c₂ hoptimism
  have hr := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hv (show 0 ≤ 2 * L by positivity))
  have hm := mul_le_mul_of_nonneg_right hr (Real.sqrt_nonneg R)
  change (∑ k : Fin K, onlineActualEpisodeW1 H K hH E initial fallback path k δ c₁ c₂) ≤
      (H : ℝ) * (3 * A) +
      Real.sqrt (2 * L * (2 * onlineActualT6Policy H K hH E initial fallback path δ c₁ c₂ +
        2 * onlineActualT6Difference H K hH E initial fallback path δ c₁ c₂)) * Real.sqrt R +
      (2 * H * L / 3) * R
  linarith
end StatisticalRL.OnlineRL
