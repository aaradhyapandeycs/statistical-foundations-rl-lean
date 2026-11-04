import Formalization.Online.Regret.T3.OnlineT3SuffixFamily
import Formalization.Online.Regret.T3.OnlineT3SuffixEpisodeArray

/-! Transport of the simultaneous stage-suffix Freedman event to the exact
source episode-major T₃ sums. This is an event equality under the same actual
reset/path law; no additional probability or independence premise is used. -/

namespace StatisticalRL.OnlineRL
open MeasureTheory ProbabilityTheory

universe uState uAction
variable {State : Type uState} {Action : Type uAction}
  [Fintype State] [Fintype Action]
noncomputable local instance t3SuffixActualStateMeasurable : MeasurableSpace State :=
  StatisticalRL.FiniteDistribution.empiricalRowStateMeasurable
noncomputable local instance t3SuffixActualSampleMeasurable (H K : ℕ) :
    MeasurableSpace ((Fin K → State) × OnlineOutcomePath.{uState, 0} State (K * H)) :=
  StatisticalRL.FiniteDistribution.empiricalRowStateMeasurable
noncomputable local instance t3SuffixActualStateDecidable : DecidableEq State := Classical.decEq State
noncomputable local instance t3SuffixActualActionDecidable : DecidableEq Action := Classical.decEq Action

/-- The all-suffix event written directly with the episode-major source sum
and the actual T₆-UCB radius. -/
noncomputable def onlineT3AllSuffixActualEpisodeArrayRadiusSet
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (fallback : State) (c₁ c₂ δ' : ℝ) :
    Set ((Fin K → State) × OnlineOutcomePath.{uState, 0} State (K * H)) :=
  {sample | ∀ j : Fin H,
    |onlineT3ActualSuffixEpisodeArray H K hH E sample.1 fallback sample.2 δ' c₁ c₂ j| ≤
      Real.sqrt (8 * onlineActualT6UCB H K hH E sample.1 fallback sample.2 δ' c₁ c₂ *
        Real.log (1 / δ')) + 5 * (H : ℝ) * Real.log (1 / δ')}

/-- The source episode-major event is extensionally the event controlled by
suffix-masking and finite union. -/
theorem onlineT3AllSuffixActualEpisodeArrayRadiusSet_eq
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (ρ : FiniteDistribution State) (fallback : State) (c₁ c₂ δ' : ℝ) :
    onlineT3AllSuffixActualEpisodeArrayRadiusSet H K hH E fallback c₁ c₂ δ' =
      onlineT3AllSuffixSourceRadiusSet H K hH E ρ fallback c₁ c₂ δ' := by
  classical
  ext sample
  rw [onlineT3AllSuffixActualEpisodeArrayRadiusSet,
    onlineT3AllSuffixSourceRadiusSet]
  simp only [Set.mem_setOf_eq, Set.mem_iInter]
  constructor
  · intro h j
    have hsum := onlineT3SuffixMaskedY_sum_eq_actualEpisodeArray
      H K hH E ρ sample.1 fallback sample.2 δ' c₁ c₂ j
    have hj := h j
    rw [← hsum] at hj
    simpa [onlineT3SuffixSourceRadiusSet, incrementSum] using hj
  · intro h j
    have hsum := onlineT3SuffixMaskedY_sum_eq_actualEpisodeArray
      H K hH E ρ sample.1 fallback sample.2 δ' c₁ c₂ j
    have hj := h j
    rw [onlineT3SuffixSourceRadiusSet] at hj
    change |incrementSum
      (onlineT3SuffixMaskedY H K hH E ρ fallback
        (onlineCappedGreedyPlanner E (Real.log (1 / δ')) c₁ c₂)
        (Real.log (1 / δ')) c₁ c₂ j) (K * H) sample| ≤ _ at hj
    rw [← hsum]
    simpa [incrementSum] using hj

/-- All source episode-major suffix sums obey their actual T₆-UCB radius with
the same confidence supplied by the finite union theorem. -/
theorem onlineT3AllSuffixActualEpisodeArrayRadius_probability
    (H K : ℕ) (hH : 0 < H) (hN : 2 ≤ K * H)
    (E : Fin H → EnvironmentStage State Action) (ρ : FiniteDistribution State)
    (fallback : State) (c₁ c₂ δ' : ℝ)
    (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) (hδ' : 0 < δ')
    (hδsmall : δ' ≤ 1 / 100) :
    1 - 2 * (H : ℝ) * (Nat.log2 (K * H) : ℝ) * δ' ≤
      (onlineSequentialEpisodeLaw H K hH E ρ fallback
        (onlineCappedGreedyPlanner E (Real.log (1 / δ')) c₁ c₂) (K * H)).rowMeasure.real
        (onlineT3AllSuffixActualEpisodeArrayRadiusSet H K hH E fallback c₁ c₂ δ') := by
  by_cases hbranch : 2 * Nat.log2 (K * H) * δ' < 1
  · rw [onlineT3AllSuffixActualEpisodeArrayRadiusSet_eq]
    exact onlineT3AllSuffixSourceRadius_probability H K hH hN E ρ fallback c₁ c₂ δ'
      hc₁ hc₂ hδ' hδsmall hbranch
  · have hq : 1 ≤ 2 * (Nat.log2 (K * H) : ℝ) * δ' := le_of_not_gt hbranch
    have hHreal : (1 : ℝ) ≤ (H : ℝ) := by
      exact_mod_cast (Nat.succ_le_iff.mpr hH)
    have hfactor : 1 ≤ (H : ℝ) * (2 * (Nat.log2 (K * H) : ℝ) * δ') := by
      calc
        1 ≤ 1 * (2 * (Nat.log2 (K * H) : ℝ) * δ') := by simpa using hq
        _ ≤ (H : ℝ) * (2 * (Nat.log2 (K * H) : ℝ) * δ') :=
          mul_le_mul_of_nonneg_right hHreal (by positivity)
    have hmeasure : 0 ≤
        (onlineSequentialEpisodeLaw H K hH E ρ fallback
          (onlineCappedGreedyPlanner E (Real.log (1 / δ')) c₁ c₂) (K * H)).rowMeasure.real
          (onlineT3AllSuffixActualEpisodeArrayRadiusSet H K hH E fallback c₁ c₂ δ') := by
      positivity
    linarith

end StatisticalRL.OnlineRL
