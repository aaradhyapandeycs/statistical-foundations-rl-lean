import Formalization.Online.Regret.W3.OnlineW3ActualProbability
import Formalization.Online.Regret.W3.OnlineW3IotaBounds
import Formalization.Online.Regret.W3.OnlineW3Absorption
import Formalization.Online.Regret.W1.OnlineW1PolicySourceAllocation

/-! Corrected zero-count, fixed-tie and K≥2 W₃ source clause. The joint
W₁/W₂/W₃ probability statement requires a separate shared-event proof. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators
open MeasureTheory ProbabilityTheory
variable {State Action : Type*} [Fintype State] [Fintype Action]
local instance w3RestrictedStateMeasurable : MeasurableSpace State := ⊤
local instance w3RestrictedAtomMeasurable (K n : ℕ) :
    MeasurableSpace ((Fin K → State) × OnlineOutcomePath State n) := ⊤

noncomputable def onlineActualW3RestrictedIotaEvent
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (fallback : State) (δ c₁ c₂ : ℝ) :
    Set ((Fin K → State) × OnlineOutcomePath State (K * H)) :=
  {sample |
    let S : ℝ := Fintype.card State
    let A : ℝ := Fintype.card Action
    let I := onlineW1SourceIota (Fintype.card State) (Fintype.card Action) H K δ
    let p := onlineActualT6Policy H K hH E sample.1 fallback sample.2 δ c₁ c₂
    let d := onlineActualT6Difference H K hH E sample.1 fallback sample.2 δ c₁ c₂
    (∑ h : Fin H, ∑ k : Fin K, onlineActualW3Point H K hH E sample.1 fallback sample.2 δ c₁ c₂ h k) ≤
      (1 / 8 : ℝ) * Real.sqrt (S * A * H^3 * p * I) +
      (1 / 8 : ℝ) * Real.sqrt (S^2 * A * H^3 * d * I) +
      (1 / 8 : ℝ) * S^2 * A * H^3 * I}

theorem onlineActualW3CoarseBudget_implies_restrictedIota
    (H K : ℕ) (hH : 0 < H) (hK : 2 ≤ K)
    (E : Fin H → EnvironmentStage State Action) (fallback : State)
    (δ c₁ c₂ : ℝ) (hδ : 0 < δ) (hδsmall : δ ≤ 1 / 100) :
    onlineActualW3CoarseBudgetEvent H K hH E fallback δ c₁ c₂ ⊆
      onlineActualW3RestrictedIotaEvent H K hH E fallback δ c₁ c₂ := by
  classical
  letI : Nonempty State := (E ⟨0, hH⟩).state_nonempty
  letI : Nonempty Action := (E ⟨0, hH⟩).action_nonempty
  let S := Fintype.card State
  let A := Fintype.card Action
  let L₀ := Real.log (1 / (2 * δ))
  let L := Real.log (1 / δ)
  let Q := 1 + Real.log (K + 1 : ℝ)
  let I := onlineW1SourceIota S A H K δ
  have hS : 0 < S := Fintype.card_pos
  have hA : 0 < A := Fintype.card_pos
  have hs : (1 : ℝ) ≤ S := by exact_mod_cast hS
  have hL₀ : 0 ≤ L₀ := by
    apply (Real.log_pos ?_).le
    apply (lt_div_iff₀ (by positivity : 0 < 2 * δ)).2
    linarith
  have hLle : L₀ ≤ L := by
    apply Real.log_le_log (by positivity : 0 < 1 / (2 * δ))
    apply div_le_div_of_nonneg_left (by norm_num : (0:ℝ) ≤ 1) hδ
    linarith
  have hL : 1 ≤ L := onlineSmallConfidence_log_ge_one δ hδ hδsmall
  have hQ : 1 ≤ Q := by
    have hh : 0 ≤ Real.log (K + 1 : ℝ) := Real.log_nonneg (by
      have hk : (0 : ℝ) ≤ K := Nat.cast_nonneg _
      linarith)
    dsimp [Q]
    linarith
  have hi := onlineW3SourceIota_bounds S A H K δ hS hA hH hK hδ hδsmall
  have hi4096 : 4096 * L * Q ≤ I := hi.1
  have hi192 : 192 ≤ I := by nlinarith [mul_nonneg (sub_nonneg.mpr hL) (sub_nonneg.mpr hQ)]
  intro sample hsample
  let p := onlineActualT6Policy H K hH E sample.1 fallback sample.2 δ c₁ c₂
  let d := onlineActualT6Difference H K hH E sample.1 fallback sample.2 δ c₁ c₂
  have hp : 0 ≤ p := by
    unfold p onlineActualT6Policy
    apply Finset.sum_nonneg
    intro h hh
    apply Finset.sum_nonneg
    intro k hk
    exact FiniteDistribution.variance_nonneg _ _
  have hd : 0 ≤ d := by
    unfold d onlineActualT6Difference
    apply Finset.sum_nonneg
    intro h hh
    apply Finset.sum_nonneg
    intro k hk
    exact FiniteDistribution.expectation_nonneg _ (fun _ => sq_nonneg _)
  have hc := onlineW3_coarse_to_iota_algebra S ((S : ℝ) * A * H) H L₀ L Q I p d
    hs (by positivity) (by positivity) hL₀ (by linarith) hLle (by linarith) hp hd hi4096 hi192
  change (∑ h : Fin H, ∑ k : Fin K, onlineActualW3Point H K hH E sample.1 fallback sample.2 δ c₁ c₂ h k) ≤
    (1 / 8 : ℝ) * Real.sqrt ((S : ℝ) * A * H^3 * p * I) +
    (1 / 8 : ℝ) * Real.sqrt ((S : ℝ)^2 * A * H^3 * d * I) +
    (1 / 8 : ℝ) * (S : ℝ)^2 * A * H^3 * I
  change (∑ h : Fin H, ∑ k : Fin K, onlineActualW3Point H K hH E sample.1 fallback sample.2 δ c₁ c₂ h k) ≤
    6 * (H : ℝ)^2 * ((S : ℝ) * A * H) +
      Real.sqrt (2 * L₀ * (4 * H^2 * (2 * p + 2 * d))) * Real.sqrt (((S : ℝ) * A * H) * Q) +
      Real.sqrt (2 * ((S : ℝ) * L) * (4 * H^2 * d)) * Real.sqrt (((S : ℝ) * A * H) * Q) +
      (2 * H^2 * L₀ / 3 + (S : ℝ) * H^2 * L) * (((S : ℝ) * A * H) * Q) at hsample
  have hpEq : ((S : ℝ) * A * H) * H^2 * p * I = (S : ℝ) * A * H^3 * p * I := by ring
  have hdEq : (S : ℝ) * ((S : ℝ) * A * H) * H^2 * d * I = (S : ℝ)^2 * A * H^3 * d * I := by ring
  rw [hpEq, hdEq] at hc
  nlinarith

theorem onlineSourceAllocated_actualW3RestrictedIota_strict
    (H K : ℕ) (hH : 0 < H) (hK : 2 ≤ K)
    (E : Fin H → EnvironmentStage State Action) (ρ : FiniteDistribution State)
    (fallback : State) (δ c₁ c₂ : ℝ) (hδ : 0 < δ) (hδone : δ ≤ 1)
    (hc₁ : 4 ≤ c₁) (hc₂ : c₁^2 ≤ c₂) :
    let δ' := onlineSourceOptimismDeltaPrime δ (Fintype.card State) (Fintype.card Action) H K
    let planner := onlineCappedGreedyPlanner E (Real.log (1 / δ')) c₁ c₂
    1 - (4 * (Fintype.card State : ℝ) + 6) *
      (Fintype.card (OnlineMDPRow State Action H) : ℝ) * K * δ' <
      (onlineSequentialEpisodeLaw H K hH E ρ fallback planner (K * H)).rowMeasure.real
        (onlineActualW3RestrictedIotaEvent H K hH E fallback δ' c₁ c₂) := by
  letI : Nonempty State := (E ⟨0, hH⟩).state_nonempty
  letI : Nonempty Action := (E ⟨0, hH⟩).action_nonempty
  let δ' := onlineSourceOptimismDeltaPrime δ (Fintype.card State) (Fintype.card Action) H K
  let planner := onlineCappedGreedyPlanner E (Real.log (1 / δ')) c₁ c₂
  let ν := onlineSequentialEpisodeLaw H K hH E ρ fallback planner (K * H)
  have hk : 0 < K := by omega
  have hd := onlineSourceOptimismDeltaPrime_domain δ (Fintype.card State)
    (Fintype.card Action) H K hδ hδone Fintype.card_pos Fintype.card_pos hH hk
  have hp := onlineSequential_actualW3CoarseBudget_strict H K hH hk E ρ fallback δ' c₁ c₂
    hd.1 hd.2 hc₁ hc₂
  have hsub := onlineActualW3CoarseBudget_implies_restrictedIota H K hH hK E fallback δ' c₁ c₂ hd.1 hd.2
  have hm := measureReal_mono hsub (measure_ne_top ν.rowMeasure _)
  exact hp.trans_le hm
end StatisticalRL.OnlineRL
