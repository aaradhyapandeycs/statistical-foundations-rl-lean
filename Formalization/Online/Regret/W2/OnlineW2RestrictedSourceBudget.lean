import Formalization.Online.Regret.W2.OnlineW2ActualProbability
import Formalization.Online.Regret.W2.OnlineW2IotaBounds
import Formalization.Online.Regret.W2.OnlineW2Absorption
import Formalization.Online.Regret.W1.OnlineW1PolicySourceAllocation

/-! Restricted K≥2 W₂ source-bound wrapper under the corrected zero-count
convention and fixed deterministic tie. The joint W₁/W₂/W₃ lemma remains open. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators
open MeasureTheory ProbabilityTheory
variable {State Action : Type*} [Fintype State] [Fintype Action]
local instance w2RestrictedStateMeasurable : MeasurableSpace State := ⊤
local instance w2RestrictedAtomMeasurable (K n : ℕ) :
    MeasurableSpace ((Fin K → State) × OnlineOutcomePath State n) := ⊤

noncomputable def onlineActualW2RestrictedIotaEvent
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (fallback : State) (δ c₁ c₂ : ℝ) :
    Set ((Fin K → State) × OnlineOutcomePath State (K * H)) :=
  {sample |
    let S : ℝ := Fintype.card State
    let A : ℝ := Fintype.card Action
    let I := onlineW1SourceIota (Fintype.card State) (Fintype.card Action) H K δ
    (∑ k : Fin K, onlineActualEpisodeW2 H K hH E sample.1 fallback sample.2 k δ c₁ c₂) ≤
      (1 / 8 : ℝ) * Real.sqrt (S^2 * A * H * onlineActualT6Difference H K hH E sample.1 fallback sample.2 δ c₁ c₂ * I) +
      (1 / 8 : ℝ) * S^2 * A * H^2 * I}

/-- The actual coarse budget implies the printed W₂ expression when K≥2. -/
theorem onlineActualW2PolicyBudget_implies_restrictedIota
    (H K : ℕ) (hH : 0 < H) (hK : 2 ≤ K)
    (E : Fin H → EnvironmentStage State Action) (fallback : State)
    (δ c₁ c₂ : ℝ) (hδ : 0 < δ) (hδsmall : δ ≤ 1 / 100) :
    onlineActualW2PolicyBudgetEvent H K hH E fallback δ c₁ c₂ ⊆
      onlineActualW2RestrictedIotaEvent H K hH E fallback δ c₁ c₂ := by
  classical
  letI : Nonempty State := (E ⟨0, hH⟩).state_nonempty
  letI : Nonempty Action := (E ⟨0, hH⟩).action_nonempty
  let S := Fintype.card State
  let A := Fintype.card Action
  let L := Real.log (1 / δ)
  let Q := 1 + Real.log (K + 1 : ℝ)
  let I := onlineW1SourceIota S A H K δ
  have hS : 0 < S := Fintype.card_pos
  have hA : 0 < A := Fintype.card_pos
  have hs : (1 : ℝ) ≤ S := by exact_mod_cast hS
  have hL : 0 ≤ L := by
    apply Real.log_nonneg
    apply (one_le_div hδ).2
    linarith
  have hLhalf : (1 / 2 : ℝ) ≤ L := by
    have hr : (2 : ℝ) ≤ 1 / δ := by
      apply (le_div_iff₀ hδ).2
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
  have hi := onlineW2SourceIota_bounds S A H K δ hS hA hH hK hδ hδsmall
  have hi256 : 256 * L * Q ≤ I := hi.1
  have hi48 : 48 ≤ I := by nlinarith [mul_nonneg (sub_nonneg.mpr hLhalf) (sub_nonneg.mpr hQ)]
  intro sample hsample
  let d := onlineActualT6Difference H K hH E sample.1 fallback sample.2 δ c₁ c₂
  have hd : 0 ≤ d := by
    unfold d onlineActualT6Difference
    apply Finset.sum_nonneg
    intro h hh
    apply Finset.sum_nonneg
    intro k hk
    exact FiniteDistribution.expectation_nonneg _ (fun _ => sq_nonneg _)
  have hc := onlineW2_coarse_to_iota_algebra S ((S : ℝ) * A * H) H L Q I d
    hs (by positivity) (by positivity) hL (by linarith) hd hi256 hi48
  change (∑ k : Fin K, onlineActualEpisodeW2 H K hH E sample.1 fallback sample.2 k δ c₁ c₂) ≤
    (1 / 8 : ℝ) * Real.sqrt ((S : ℝ)^2 * A * H * d * I) +
      (1 / 8 : ℝ) * (S : ℝ)^2 * A * H^2 * I
  change (∑ k : Fin K, onlineActualEpisodeW2 H K hH E sample.1 fallback sample.2 k δ c₁ c₂) ≤
    (H : ℝ) * (3 * ((S : ℝ) * A * H)) +
      Real.sqrt (2 * ((S : ℝ) * L) * d) * Real.sqrt (((S : ℝ) * A * H) * Q) +
      (S : ℝ) * H * L * (((S : ℝ) * A * H) * Q) at hsample
  have heq : (S : ℝ) * ((S : ℝ) * A * H) * d * I = (S : ℝ)^2 * A * H * d * I := by ring
  rw [heq] at hc
  nlinarith

end StatisticalRL.OnlineRL
