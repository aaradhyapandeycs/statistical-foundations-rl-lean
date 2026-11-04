import Formalization.Online.Regret.Gap.OnlineJ1SourceConfidence

/-! Actual-law variance and gap proof component: OnlineT6DifferenceAssembly.
This module supplies an intermediate proof, not the complete T56 theorem. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators
universe uState uAction
variable {State : Type uState} {Action : Type uAction} [Fintype State] [Fintype Action]
noncomputable local instance t6diffState : DecidableEq State := Classical.decEq State
noncomputable local instance t6diffAction : DecidableEq Action := Classical.decEq Action

/-- J2 is the unmodified optimistic-minus-policy gap at each actually stored
successor, including the terminal successor whose continuation is zero. -/
noncomputable def onlineActualJ2
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (initial : Fin K → State) (fallback : State) (path : OnlineOutcomePath State (K * H))
    (δ c₁ c₂ : ℝ) : ℝ :=
  ∑ h : Fin H, ∑ k : Fin K,
    let U := onlineActualOptimisticContinuation H K hH E initial fallback path δ c₁ c₂ h k
    let P := onlineActualPolicyContinuation H K hH E initial fallback path δ c₁ c₂ h k
    let x := onlineT5ActualSuccessor H K hH E initial fallback path δ c₁ c₂ h k
    U x - P x

/-- The source identity and bounded positive gap imply D≤H(J1+J2) on the
actual optimism event, with no concentration or target-shaped premise. -/
theorem onlineActualT6Difference_le_H_J1_add_J2
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (initial : Fin K → State) (fallback : State) (path : OnlineOutcomePath State (K * H))
    (δ c₁ c₂ : ℝ) (hL : 0 ≤ Real.log (1 / δ)) (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂)
    (hoptimism : onlineHistoryAllStageTrajectoryOptimism H K E δ c₁ c₂
      (onlineSequentialPathHistory (onlineEpisodicChoose H K hH initial fallback
        (onlineCappedGreedyPlanner E (Real.log (1 / δ)) c₁ c₂)) (K * H) [] path)) :
    onlineActualT6Difference H K hH E initial fallback path δ c₁ c₂ ≤
      (H : ℝ) * (onlineActualJ1 H K hH E initial fallback path δ c₁ c₂ +
        onlineActualJ2 H K hH E initial fallback path δ c₁ c₂) := by
  classical
  unfold onlineActualT6Difference onlineActualJ1 onlineActualJ2
  simp only [← Finset.sum_add_distrib, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro h hh
  apply Finset.sum_le_sum
  intro k hk
  let planner := onlineCappedGreedyPlanner E (Real.log (1 / δ)) c₁ c₂
  let sa := onlineActualStageRowSequence H K hH initial fallback planner path h k.val
  let U := onlineActualOptimisticContinuation H K hH E initial fallback path δ c₁ c₂ h k
  let P := onlineActualPolicyContinuation H K hH E initial fallback path δ c₁ c₂ h k
  let d := (E h).transition sa.1 sa.2
  have hpoint (s : State) : (U s - P s)^2 ≤ (H : ℝ) * (U s - P s) := by
    have ho := onlineActualW2_gap_order H K hH E initial fallback path δ c₁ c₂ hL hc₁ hc₂ hoptimism h k s
    have h0 : 0 ≤ U s - P s := le_trans ho.1 ho.2.1
    nlinarith [mul_nonneg h0 (sub_nonneg.mpr ho.2.2)]
  have hm := d.expectation_mono hpoint
  rw [d.expectation_mul] at hm
  dsimp only [planner, sa, U, P, d] at hm ⊢
  linarith

/-- The source AM-GM step; it is independent of any stochastic event. -/
theorem onlineT6Difference_young (H D L : ℝ)
    (hH : 0 < H) (hD : 0 ≤ D) (hL : 0 ≤ L) :
    Real.sqrt (8 * D * L) + 5 * H * L ≤ D / (2 * H) + 9 * H * L := by
  have hA : 0 ≤ D / (2 * H) := by positivity
  have hB : 0 ≤ 4 * H * L := by positivity
  have hp : (D / (2 * H)) * (4 * H * L) = 2 * D * L := by field_simp; ring
  have hr : Real.sqrt (8 * D * L) ≤ D / (2 * H) + 4 * H * L := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · nlinarith [sq_nonneg (D / (2 * H) - 4 * H * L)]
  linarith

/-- Final scalar rearrangement after independent J1 and J2 bounds have been
proved on their common event. -/
theorem onlineT6Difference_assemble (H D J1 J2 T0 L : ℝ)
    (hH : 0 < H) (hD : 0 ≤ D) (hL : 0 ≤ L)
    (hexpand : D ≤ H * (J1 + J2))
    (hJ1 : J1 ≤ Real.sqrt (8 * D * L) + 5 * H * L)
    (hJ2 : J2 ≤ H * T0) :
    D ≤ 2 * H^2 * T0 + 18 * H^2 * L := by
  have hy := onlineT6Difference_young H D L hH hD hL
  have hm := mul_le_mul_of_nonneg_left (add_le_add (hJ1.trans hy) hJ2) (le_of_lt hH)
  have hdiv : H * (D / (2 * H)) = D / 2 := by field_simp
  nlinarith [hm]
end StatisticalRL.OnlineRL
