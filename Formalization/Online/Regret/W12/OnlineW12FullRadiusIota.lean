import Formalization.Online.Regret.W12.OnlineW12FullRadiusBudget
import Formalization.Online.Regret.W1.OnlineW1RestrictedSourceBudget
import Formalization.Online.Regret.W2.OnlineW2RestrictedSourceBudget

/-! Same-experiment suffix proof component: OnlineW12FullRadiusIota.
Scope and source confidence are established only by the final applying theorem. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators
variable {State Action : Type*} [Fintype State] [Fintype Action]

theorem onlineActualW12_fullRadii_le_iota
    (H K : ℕ) (hH : 0 < H) (hK : 2 ≤ K) (E : Fin H → EnvironmentStage State Action)
    (initial : Fin K → State) (fallback : State) (path : OnlineOutcomePath State (K * H))
    (δ c₁ c₂ : ℝ) (hδ : 0 < δ) (hδsmall : δ ≤ 1 / 100) (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂)
    (hoptimism : onlineHistoryAllStageTrajectoryOptimism H K E δ c₁ c₂
      (onlineSequentialPathHistory (onlineEpisodicChoose H K hH initial fallback
        (onlineCappedGreedyPlanner E (Real.log (1 / δ)) c₁ c₂)) (K * H) [] path)) :
    let S := (Fintype.card State : ℝ)
    let A := (Fintype.card Action : ℝ)
    let I := onlineW1SourceIota (Fintype.card State) (Fintype.card Action) H K δ
    let p := onlineActualT6Policy H K hH E initial fallback path δ c₁ c₂
    let d := onlineActualT6Difference H K hH E initial fallback path δ c₁ c₂
    (∑ i : Fin H × Fin K, onlineActualW1RadiusTerm H K hH E initial fallback path δ c₁ c₂ i.1 i.2) ≤
      (1 / 8 : ℝ) * Real.sqrt (S * A * H * p * I) +
      (1 / 8 : ℝ) * Real.sqrt (S * A * H * d * I) + (1 / 8 : ℝ) * S * A * H^2 * I ∧
    (∑ i : Fin H × Fin K, onlineActualW2RadiusTerm H K hH E initial fallback path δ c₁ c₂ i.1 i.2) ≤
      (1 / 8 : ℝ) * Real.sqrt (S^2 * A * H * d * I) + (1 / 8 : ℝ) * S^2 * A * H^2 * I := by
  classical
  letI : Nonempty State := (E ⟨0, hH⟩).state_nonempty
  letI : Nonempty Action := (E ⟨0, hH⟩).action_nonempty
  let S := Fintype.card State
  let A := Fintype.card Action
  let Q := 1 + Real.log (K + 1 : ℝ)
  let L1 := Real.log (1 / (2 * δ))
  let L2 := Real.log (1 / δ)
  let I := onlineW1SourceIota S A H K δ
  let p := onlineActualT6Policy H K hH E initial fallback path δ c₁ c₂
  let d := onlineActualT6Difference H K hH E initial fallback path δ c₁ c₂
  have hS : 0 < S := Fintype.card_pos
  have hA : 0 < A := Fintype.card_pos
  have hs : (1 : ℝ) ≤ S := by exact_mod_cast hS
  have hL1 : 0 ≤ L1 := by
    apply (Real.log_pos ?_).le
    apply (lt_div_iff₀ (by positivity : 0 < 2 * δ)).2
    linarith
  have hL2 : 0 ≤ L2 := Real.log_nonneg ((one_le_div hδ).2 (by linarith))
  have hL1half : (1 / 2 : ℝ) ≤ L1 := by
    have hr : (2 : ℝ) ≤ 1 / (2 * δ) := by apply (le_div_iff₀ (by positivity : 0 < 2 * δ)).2; linarith
    have hm := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hr
    have ht := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at ht
    dsimp [L1]
    linarith
  have hL2half : (1 / 2 : ℝ) ≤ L2 := by
    have hr : (2 : ℝ) ≤ 1 / δ := by apply (le_div_iff₀ hδ).2; linarith
    have hm := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hr
    have ht := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at ht
    dsimp [L2]
    linarith
  have hQ : 1 ≤ Q := by
    have hh : 0 ≤ Real.log (K + 1 : ℝ) := Real.log_nonneg (by have hk : (0 : ℝ) ≤ K := Nat.cast_nonneg _; linarith)
    dsimp [Q]
    linarith
  have hi1 := onlineW1SourceIota_bounds S A H K δ hS hA hH hK hδ hδsmall
  have hi2 := onlineW2SourceIota_bounds S A H K δ hS hA hH hK hδ hδsmall
  have hi2561 : 256 * L1 * Q ≤ I := hi1.1
  have hi2562 : 256 * L2 * Q ≤ I := hi2.1
  have hi48 : 48 ≤ I := by nlinarith [mul_nonneg (sub_nonneg.mpr hL1half) (sub_nonneg.mpr hQ)]
  have hp : 0 ≤ p := by
    unfold p onlineActualT6Policy
    apply Finset.sum_nonneg; intro h hh; apply Finset.sum_nonneg; intro k hk
    exact FiniteDistribution.variance_nonneg _ _
  have hd : 0 ≤ d := by
    unfold d onlineActualT6Difference
    apply Finset.sum_nonneg; intro h hh; apply Finset.sum_nonneg; intro k hk
    exact FiniteDistribution.expectation_nonneg _ (fun _ => sq_nonneg _)
  have hw1 := onlineActualW1_fullRadius_le_trueVarianceBudget H K hH E initial fallback path δ c₁ c₂ hδ (by linarith)
  have hw2 := onlineActualW2_fullRadius_le_policyDifferenceBudget H K hH E initial fallback path δ c₁ c₂ hδ (by linarith) hc₁ hc₂
  have hv := onlineActualT6Optimal_le_policy_difference H K hH E initial fallback path δ c₁ c₂ hoptimism
  have hr := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hv (show 0 ≤ 2 * L1 by positivity))
  have hm := mul_le_mul_of_nonneg_right hr (Real.sqrt_nonneg (((S : ℝ) * A * H) * Q))
  have ha1 := onlineW1_coarse_to_iota_algebra ((S : ℝ) * A * H) H L1 Q I p d
    (by positivity) (by positivity) hL1 (by linarith) hp hd hi2561 hi48
  have ha2 := onlineW2_coarse_to_iota_algebra S ((S : ℝ) * A * H) H L2 Q I d
    hs (by positivity) (by positivity) hL2 (by linarith) hd hi2562 hi48
  have heq : (S : ℝ) * ((S : ℝ) * A * H) * d * I = (S : ℝ)^2 * A * H * d * I := by ring
  rw [heq] at ha2
  change (∑ i : Fin H × Fin K, onlineActualW1RadiusTerm H K hH E initial fallback path δ c₁ c₂ i.1 i.2) ≤
      (1 / 8 : ℝ) * Real.sqrt ((S : ℝ) * A * H * p * I) +
      (1 / 8 : ℝ) * Real.sqrt ((S : ℝ) * A * H * d * I) + (1 / 8 : ℝ) * S * A * H^2 * I ∧
    (∑ i : Fin H × Fin K, onlineActualW2RadiusTerm H K hH E initial fallback path δ c₁ c₂ i.1 i.2) ≤
      (1 / 8 : ℝ) * Real.sqrt ((S : ℝ)^2 * A * H * d * I) + (1 / 8 : ℝ) * S^2 * A * H^2 * I
  constructor
  · have hcoarse : (∑ i : Fin H × Fin K, onlineActualW1RadiusTerm H K hH E initial fallback path δ c₁ c₂ i.1 i.2) ≤
      (H : ℝ) * (3 * ((S : ℝ) * A * H)) +
      Real.sqrt (2 * L1 * (2 * p + 2 * d)) * Real.sqrt (((S : ℝ) * A * H) * Q) +
      (2 * H * L1 / 3) * (((S : ℝ) * A * H) * Q) := by
      change (∑ i : Fin H × Fin K, onlineActualW1RadiusTerm H K hH E initial fallback path δ c₁ c₂ i.1 i.2) ≤
      (H : ℝ) * (3 * ((S : ℝ) * A * H)) +
      Real.sqrt (2 * L1 * (2 * p + 2 * d)) * Real.sqrt (((S : ℝ) * A * H) * Q) +
      (2 * H * L1 / 3) * (((S : ℝ) * A * H) * Q)
      linarith [hw1, hm]
    have hf := hcoarse.trans ha1
    have hpoly : (1 / 8 : ℝ) * ((S : ℝ) * A * H) * H * I = (1 / 8 : ℝ) * S * A * H^2 * I := by ring
    rw [hpoly] at hf
    exact hf
  · have hcoarse : (∑ i : Fin H × Fin K, onlineActualW2RadiusTerm H K hH E initial fallback path δ c₁ c₂ i.1 i.2) ≤
      (H : ℝ) * (3 * ((S : ℝ) * A * H)) +
      Real.sqrt (2 * ((S : ℝ) * L2) * d) * Real.sqrt (((S : ℝ) * A * H) * Q) +
      (S : ℝ) * H * L2 * (((S : ℝ) * A * H) * Q) := hw2
    have hf := hcoarse.trans ha2
    have hpoly : (1 / 8 : ℝ) * S * ((S : ℝ) * A * H) * H * I = (1 / 8 : ℝ) * S^2 * A * H^2 * I := by ring
    rw [hpoly] at hf
    exact hf
end StatisticalRL.OnlineRL
