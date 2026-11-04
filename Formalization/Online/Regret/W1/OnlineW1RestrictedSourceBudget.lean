import Formalization.Online.Regret.W1.W1Definitions
import Formalization.Online.Regret.W1.OnlineW1IotaBounds
import Formalization.Online.Regret.W1.OnlineW1AbsorptionAlgebra
import Formalization.Online.Regret.W1.OnlineW1PolicySourceAllocation

/-! OnlineW1RestrictedSourceBudget: an intermediate component for the corrected-zero-count, fixed-tie W₁ analysis. Source-facing K≥2 scope and remaining W₂/regret obligations are stated at the final export. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators
open MeasureTheory ProbabilityTheory
variable {State Action : Type*} [Fintype State] [Fintype Action]
local instance w1RestrictedStateMeasurable : MeasurableSpace State := ⊤
local instance w1RestrictedAtomMeasurable (K n : ℕ) :
    MeasurableSpace ((Fin K → State) × OnlineOutcomePath State n) := ⊤


/-- Source iota absorbs the proved coarse same-path W₁ policy budget for K≥2.
The K≥2 restriction and zero-count correction are explicit. -/
theorem onlineActualW1PolicyBudget_implies_restrictedIota
    (H K : ℕ) (hH : 0 < H) (hK : 2 ≤ K)
    (E : Fin H → EnvironmentStage State Action) (fallback : State)
    (δ' c₁ c₂ : ℝ) (hδ : 0 < δ') (hδsmall : δ' ≤ 1 / 100) :
    onlineActualW1PolicyBudgetEvent H K hH E fallback δ' c₁ c₂ ⊆
      onlineActualW1RestrictedIotaEvent H K hH E fallback δ' c₁ c₂ := by
  classical
  letI : Nonempty State := (E ⟨0, hH⟩).state_nonempty
  letI : Nonempty Action := (E ⟨0, hH⟩).action_nonempty
  let S := Fintype.card State
  let A := Fintype.card Action
  let L := Real.log (1 / (2 * δ'))
  let Q := 1 + Real.log (K + 1 : ℝ)
  let I := onlineW1SourceIota S A H K δ'
  have hS : 0 < S := Fintype.card_pos
  have hA : 0 < A := Fintype.card_pos
  have hs : (1 : ℝ) ≤ S := by exact_mod_cast hS
  have hs0 : (0 : ℝ) ≤ S := by positivity
  have ha0 : (0 : ℝ) ≤ A := by positivity
  have hh0 : (0 : ℝ) ≤ H := by positivity
  have hL : 0 ≤ L := by
    apply (Real.log_pos ?_).le
    apply (lt_div_iff₀ (by positivity : 0 < 2 * δ')).2
    linarith
  have hLhalf : (1 / 2 : ℝ) ≤ L := by
    have hr : (2 : ℝ) ≤ 1 / (2 * δ') := by
      apply (le_div_iff₀ (by positivity : 0 < 2 * δ')).2
      linarith
    have hm := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hr
    have ht := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at ht
    dsimp [L]
    linarith
  have hQ : 1 ≤ Q := by
    have hh : 0 ≤ Real.log (K + 1 : ℝ) := Real.log_nonneg (by
      have hk : (0 : ℝ) ≤ K := Nat.cast_nonneg _
      linarith)
    dsimp [Q]
    linarith
  have hi := onlineW1SourceIota_bounds S A H K δ' hS hA hH hK hδ hδsmall
  have hi256 : 256 * L * Q ≤ I := hi.1
  have hi48 : 48 ≤ I := by nlinarith [mul_nonneg (sub_nonneg.mpr hLhalf) (sub_nonneg.mpr hQ)]
  intro sample hsample
  let p := onlineActualT6Policy H K hH E sample.1 fallback sample.2 δ' c₁ c₂
  let d := onlineActualT6Difference H K hH E sample.1 fallback sample.2 δ' c₁ c₂
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
  have hcoarse := onlineW1_coarse_to_iota_algebra ((S : ℝ) * A * H) H L Q I p d
    (by positivity) hh0 hL (by linarith : 0 ≤ Q) hp hd hi256 hi48
  change (∑ k : Fin K, onlineActualEpisodeW1 H K hH E sample.1 fallback sample.2 k δ' c₁ c₂) ≤
    (1 / 8 : ℝ) * Real.sqrt ((S : ℝ) * A * H * p * I) +
    (1 / 8 : ℝ) * Real.sqrt ((S : ℝ) * A * H * d * I) +
    (1 / 8 : ℝ) * S * A * H^2 * I
  change (∑ k : Fin K, onlineActualEpisodeW1 H K hH E sample.1 fallback sample.2 k δ' c₁ c₂) ≤
      (H : ℝ) * (3 * ((S : ℝ) * A * H)) +
      Real.sqrt (2 * L * (2 * p + 2 * d)) * Real.sqrt (((S : ℝ) * A * H) * Q) +
      (2 * H * L / 3) * (((S : ℝ) * A * H) * Q) at hsample
  nlinarith

/-- Source-allocated same-law W₁ inequality for the explicitly restricted
K≥2 corrected convention. This is not the unrestricted named source lemma. -/
theorem onlineSourceAllocated_actualW1RestrictedIota_strict
    (H K : ℕ) (hH : 0 < H) (hK : 2 ≤ K)
    (E : Fin H → EnvironmentStage State Action) (ρ : FiniteDistribution State)
    (fallback : State) (δ c₁ c₂ : ℝ) (hδ : 0 < δ) (hδone : δ ≤ 1)
    (hc₁ : 4 ≤ c₁) (hc₂ : c₁^2 ≤ c₂) :
    let δ' := onlineSourceOptimismDeltaPrime δ
      (Fintype.card State) (Fintype.card Action) H K
    let planner := onlineCappedGreedyPlanner E (Real.log (1 / δ')) c₁ c₂
    1 - 6 * (Fintype.card State : ℝ) * (Fintype.card Action : ℝ) * H * K * δ' <
      (onlineSequentialEpisodeLaw H K hH E ρ fallback planner (K * H)).rowMeasure.real
        (onlineActualW1RestrictedIotaEvent H K hH E fallback δ' c₁ c₂) := by
  letI : Nonempty State := (E ⟨0, hH⟩).state_nonempty
  letI : Nonempty Action := (E ⟨0, hH⟩).action_nonempty
  let δ' := onlineSourceOptimismDeltaPrime δ (Fintype.card State) (Fintype.card Action) H K
  let planner := onlineCappedGreedyPlanner E (Real.log (1 / δ')) c₁ c₂
  let ν := onlineSequentialEpisodeLaw H K hH E ρ fallback planner (K * H)
  have hk : 0 < K := by omega
  have hd := onlineSourceOptimismDeltaPrime_domain δ (Fintype.card State)
    (Fintype.card Action) H K hδ hδone Fintype.card_pos Fintype.card_pos hH hk
  have hp := onlineSourceAllocated_actualW1PolicyBudget_strict H K hH hk E ρ fallback δ c₁ c₂
    hδ hδone hc₁ hc₂
  have hsub := onlineActualW1PolicyBudget_implies_restrictedIota H K hH hK E fallback δ' c₁ c₂ hd.1 hd.2
  have hm := measureReal_mono hsub (measure_ne_top ν.rowMeasure _)
  exact hp.trans_le hm
end StatisticalRL.OnlineRL
