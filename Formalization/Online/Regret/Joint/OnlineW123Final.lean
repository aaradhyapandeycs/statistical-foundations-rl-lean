import Formalization.Online.Regret.Joint.OnlineW123SharedEvent

/-! Source-allocated joint W₁/W₂/W₃ confidence, corrected zero counts,
fixed deterministic ties and explicitly restricted to K≥2. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators
open MeasureTheory ProbabilityTheory
variable {State Action : Type*} [Fintype State] [Fintype Action]
local instance w123FinalStateMeasurable : MeasurableSpace State := ⊤
local instance w123FinalAtomMeasurable (K n : ℕ) : MeasurableSpace ((Fin K → State) × OnlineOutcomePath State n) := ⊤

theorem onlineSingleton_W123_event_univ [Subsingleton State]
    (H K : ℕ) (hH : 0 < H) (hK : 2 ≤ K) (E : Fin H → EnvironmentStage State Action)
    (fallback : State) (δ c₁ c₂ : ℝ) (hδ : 0 < δ) (hδsmall : δ ≤ 1 / 100) :
    onlineActualW123RestrictedEvent H K hH E fallback δ c₁ c₂ = Set.univ := by
  classical
  letI : Nonempty State := (E ⟨0, hH⟩).state_nonempty
  letI : Nonempty Action := (E ⟨0, hH⟩).action_nonempty
  have hi := onlineW1SourceIota_bounds (Fintype.card State) (Fintype.card Action) H K δ
    Fintype.card_pos Fintype.card_pos hH hK hδ hδsmall
  have hI : 0 ≤ onlineW1SourceIota (Fintype.card State) (Fintype.card Action) H K δ := by linarith [hi.2.2]
  ext sample
  simp only [Set.mem_univ, iff_true]
  have hz := onlineSingleton_W123_zero H K hH E sample.1 fallback sample.2 δ c₁ c₂
  have hp : 0 ≤ onlineActualT6Policy H K hH E sample.1 fallback sample.2 δ c₁ c₂ := by
    unfold onlineActualT6Policy
    apply Finset.sum_nonneg
    intro h hh
    apply Finset.sum_nonneg
    intro k hk
    exact FiniteDistribution.variance_nonneg _ _
  have hd : 0 ≤ onlineActualT6Difference H K hH E sample.1 fallback sample.2 δ c₁ c₂ := by
    unfold onlineActualT6Difference
    apply Finset.sum_nonneg
    intro h hh
    apply Finset.sum_nonneg
    intro k hk
    exact FiniteDistribution.expectation_nonneg _ (fun _ => sq_nonneg _)
  change _ ∧ _ ∧ _
  unfold onlineActualW1RestrictedIotaEvent onlineActualW2RestrictedIotaEvent onlineActualW3RestrictedIotaEvent
  simp only [Set.mem_setOf_eq, hz.1, hz.2.1, hz.2.2]
  exact ⟨by positivity, by positivity, by positivity⟩

/-- Joint printed W₁/W₂/W₃ inequalities on one source-allocated experiment,
under K≥2 and the corrected zero-count and fixed-tie conventions. -/
theorem onlineSourceAllocated_actualW123Restricted_strict
    (H K : ℕ) (hH : 0 < H) (hK : 2 ≤ K)
    (E : Fin H → EnvironmentStage State Action) (ρ : FiniteDistribution State)
    (fallback : State) (δ c₁ c₂ : ℝ) (hδ : 0 < δ) (hδone : δ ≤ 1)
    (hc₁ : 4 ≤ c₁) (hc₂ : c₁^2 ≤ c₂) :
    let δ' := onlineSourceOptimismDeltaPrime δ (Fintype.card State) (Fintype.card Action) H K
    let planner := onlineCappedGreedyPlanner E (Real.log (1 / δ')) c₁ c₂
    1 - 12 * (Fintype.card State : ℝ)^2 * (Fintype.card Action : ℝ) * H * K * δ' <
      (onlineSequentialEpisodeLaw H K hH E ρ fallback planner (K * H)).rowMeasure.real
        (onlineActualW123RestrictedEvent H K hH E fallback δ' c₁ c₂) := by
  classical
  letI : Nonempty State := (E ⟨0, hH⟩).state_nonempty
  letI : Nonempty Action := (E ⟨0, hH⟩).action_nonempty
  let δ' := onlineSourceOptimismDeltaPrime δ (Fintype.card State) (Fintype.card Action) H K
  let planner := onlineCappedGreedyPlanner E (Real.log (1 / δ')) c₁ c₂
  let ν := onlineSequentialEpisodeLaw H K hH E ρ fallback planner (K * H)
  have hk : 0 < K := by omega
  have hd := onlineSourceOptimismDeltaPrime_domain δ (Fintype.card State)
    (Fintype.card Action) H K hδ hδone Fintype.card_pos Fintype.card_pos hH hk
  have hspos : (0 : ℝ) < Fintype.card State := by exact_mod_cast (Fintype.card_pos (α := State))
  have hapos : (0 : ℝ) < Fintype.card Action := by exact_mod_cast (Fintype.card_pos (α := Action))
  have hhpos : (0 : ℝ) < H := by exact_mod_cast hH
  have hkpos : (0 : ℝ) < K := by exact_mod_cast hk
  have hδpos : 0 < δ' := hd.1
  by_cases hs : Fintype.card State = 1
  · letI : Subsingleton State := Fintype.card_le_one_iff_subsingleton.mp (by omega)
    have he := onlineSingleton_W123_event_univ H K hH hK E fallback δ' c₁ c₂ hd.1 hd.2
    change _ < ν.rowMeasure.real (onlineActualW123RestrictedEvent H K hH E fallback δ' c₁ c₂)
    rw [he, probReal_univ]
    have hpos : 0 < 12 * (Fintype.card State : ℝ)^2 * (Fintype.card Action : ℝ) * H * K * δ' := by positivity
    linarith
  · have hs2 : 2 ≤ Fintype.card State := by have := Fintype.card_pos (α := State); omega
    have hp := onlineSequential_actualW123_shared_strict H K hH hK E ρ fallback δ' c₁ c₂ hd.1 hd.2 hc₁ hc₂
    have hs2' : (2 : ℝ) ≤ Fintype.card State := by exact_mod_cast hs2
    have hcoeff : 4 * (Fintype.card State : ℝ) + 10 ≤ 12 * (Fintype.card State : ℝ) := by linarith
    have hnonneg : 0 ≤ (Fintype.card State : ℝ) * (Fintype.card Action : ℝ) * H * K * δ' := by positivity
    have hbound := mul_le_mul_of_nonneg_right hcoeff hnonneg
    change 1 - (4 * (Fintype.card State : ℝ) + 10) * (Fintype.card (OnlineMDPRow State Action H) : ℝ) * K * δ' <
      ν.rowMeasure.real (onlineActualW123RestrictedEvent H K hH E fallback δ' c₁ c₂) at hp
    change _ < ν.rowMeasure.real (onlineActualW123RestrictedEvent H K hH E fallback δ' c₁ c₂)
    simp only [OnlineMDPRow, Fintype.card_prod, Fintype.card_fin, Nat.cast_mul] at hp
    nlinarith
end StatisticalRL.OnlineRL
