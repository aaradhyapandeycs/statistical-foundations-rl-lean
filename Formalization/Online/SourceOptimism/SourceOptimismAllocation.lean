import Formalization.Online.SourceOptimism.GreedySequentialTrajectoryOptimism

/-! Exact source delta-prime allocation for the
same-law trajectory optimism construction. Uses the printed 100 denominator, not the
commented-out 200 expression. The deterministic tie rule and explicit N=0
correction remain those of the imported capped planner. -/
namespace StatisticalRL.OnlineRL
open MeasureTheory ProbabilityTheory
variable {State Action : Type*} [Fintype State] [Fintype Action]
local instance onlineSourceOptimismStateMeasurable : MeasurableSpace State := ⊤

/-- Source equation definition_delta_prime, with natural finite cardinalities. -/
noncomputable def onlineSourceOptimismDeltaPrime (δ : ℝ) (S A H K : ℕ) : ℝ :=
  δ / (100 * (S : ℝ)^2 * (A : ℝ)^2 * (H : ℝ)^2 * (K : ℝ)^2)

/-- The printed source allocation supplies the exact domain needed by both
concentration and deterministic small-count saturation. -/
theorem onlineSourceOptimismDeltaPrime_domain
    (δ : ℝ) (S A H K : ℕ) (hδ : 0 < δ) (hδone : δ ≤ 1)
    (hS : 0 < S) (hA : 0 < A) (hH : 0 < H) (hK : 0 < K) :
    0 < onlineSourceOptimismDeltaPrime δ S A H K ∧
      onlineSourceOptimismDeltaPrime δ S A H K ≤ 1 / 100 := by
  have hSr : (1 : ℝ) ≤ S := by exact_mod_cast (Nat.succ_le_iff.mpr hS)
  have hAr : (1 : ℝ) ≤ A := by exact_mod_cast (Nat.succ_le_iff.mpr hA)
  have hHr : (1 : ℝ) ≤ H := by exact_mod_cast (Nat.succ_le_iff.mpr hH)
  have hKr : (1 : ℝ) ≤ K := by exact_mod_cast (Nat.succ_le_iff.mpr hK)
  have hSsq : (1 : ℝ) ≤ (S : ℝ)^2 := by nlinarith
  have hAsq : (1 : ℝ) ≤ (A : ℝ)^2 := by nlinarith
  have hHsq : (1 : ℝ) ≤ (H : ℝ)^2 := by nlinarith
  have hKsq : (1 : ℝ) ≤ (K : ℝ)^2 := by nlinarith
  have hden : (100 : ℝ) ≤
      100 * (S : ℝ)^2 * (A : ℝ)^2 * (H : ℝ)^2 * (K : ℝ)^2 := by
    calc
      (100 : ℝ) = 100 * 1 * 1 * 1 * 1 := by norm_num
      _ ≤ 100 * (S : ℝ)^2 * (A : ℝ)^2 * (H : ℝ)^2 * (K : ℝ)^2 := by
        gcongr <;> assumption
  have hdenpos : 0 < 100 * (S : ℝ)^2 * (A : ℝ)^2 * (H : ℝ)^2 * (K : ℝ)^2 := by
    linarith
  constructor
  · exact div_pos hδ hdenpos
  · apply (div_le_iff₀ hdenpos).2
    nlinarith

/-- The row index set has exactly S*A*H elements, not an additional factor K
or a terminal Q stage. -/
theorem onlineMDPRow_card_real (H : ℕ) :
    (Fintype.card (OnlineMDPRow State Action H) : ℝ) =
      (Fintype.card State : ℝ) * (Fintype.card Action : ℝ) * H := by
  simp only [OnlineMDPRow, Fintype.card_prod, Fintype.card_fin, Nat.cast_mul]
  ring

/-- Source-facing allocation wrapper of the actual-law trajectory event.
All played active Q/V tables are optimistic under exactly the same causal
fixed greedy planner. The zero-count branch is the explicit candidate source
repair. Compilation and independent audit are required before any claim that
this establishes the printed named lemma. -/
theorem onlineSourceAllocated_allStageTrajectoryOptimism_strict
    (H K : ℕ) (hH : 0 < H) (hK : 0 < K)
    (E : Fin H → EnvironmentStage State Action) (ρ : FiniteDistribution State)
    (fallback : State) (δ c₁ c₂ : ℝ)
    (hδ : 0 < δ) (hδone : δ ≤ 1) (hc₁ : 4 ≤ c₁) (hc₂ : c₁^2 ≤ c₂) :
    let δ' := onlineSourceOptimismDeltaPrime δ
      (Fintype.card State) (Fintype.card Action) H K
    let planner := onlineCappedGreedyPlanner E (Real.log (1 / δ')) c₁ c₂
    1 - 2 * (Fintype.card State : ℝ) * (Fintype.card Action : ℝ) * H * K * δ' <
      (onlineSequentialEpisodeLaw H K hH E ρ fallback planner (K * H)).rowMeasure.real
        {sample | onlineHistoryAllStageTrajectoryOptimism H K E δ' c₁ c₂
          (onlineSequentialPathHistory (onlineEpisodicChoose H K hH sample.1 fallback planner)
            (K * H) [] sample.2)} := by
  letI : Nonempty State := (E ⟨0, hH⟩).state_nonempty
  letI : Nonempty Action := (E ⟨0, hH⟩).action_nonempty
  let δ' := onlineSourceOptimismDeltaPrime δ
    (Fintype.card State) (Fintype.card Action) H K
  have hdomain := onlineSourceOptimismDeltaPrime_domain δ
    (Fintype.card State) (Fintype.card Action) H K hδ hδone
    Fintype.card_pos Fintype.card_pos hH hK
  have hp := onlineGreedySequential_allStageTrajectoryOptimism_strict H K hH hK
    E ρ fallback δ' c₁ c₂ hdomain.1 hdomain.2 hc₁ hc₂
  rw [onlineMDPRow_card_real] at hp
  simpa only [mul_assoc] using hp

end StatisticalRL.OnlineRL
