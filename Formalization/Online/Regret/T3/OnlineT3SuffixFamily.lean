import Formalization.Online.Regret.T3.OnlineT3SuffixSourceRadius

/-! Uniform suffix-start control for all `j : Fin H`, obtained by a finite
union under the same actual sequential episode law. -/

namespace StatisticalRL.OnlineRL
open MeasureTheory ProbabilityTheory

universe uState uAction
variable {State : Type uState} {Action : Type uAction}
  [Fintype State] [Fintype Action]
noncomputable local instance t3SuffixFamilyStateMeasurable : MeasurableSpace State :=
  StatisticalRL.FiniteDistribution.empiricalRowStateMeasurable
noncomputable local instance t3SuffixFamilySampleMeasurable (H K : ℕ) :
    MeasurableSpace ((Fin K → State) × OnlineOutcomePath.{uState, 0} State (K * H)) :=
  StatisticalRL.FiniteDistribution.empiricalRowStateMeasurable
noncomputable local instance t3SuffixFamilyStateDecidable : DecidableEq State := Classical.decEq State
noncomputable local instance t3SuffixFamilyActionDecidable : DecidableEq Action := Classical.decEq Action

/-- The common event that every deterministic stage suffix has its actual
T₆-UCB radius bound. -/
@[irreducible] noncomputable def onlineT3AllSuffixSourceRadiusSet
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (ρ : FiniteDistribution State) (fallback : State) (c₁ c₂ δ' : ℝ) :
    Set ((Fin K → State) × OnlineOutcomePath.{uState, 0} State (K * H)) :=
  ⋂ j : Fin H, onlineT3SuffixSourceRadiusSet H K hH E ρ fallback c₁ c₂ δ' j

/-- A single source confidence allocation controls every deterministic stage
suffix, under the same actual joint reset/transition law. -/
theorem onlineT3AllSuffixSourceRadius_probability
    (H K : ℕ) (hH : 0 < H) (hN : 2 ≤ K * H)
    (E : Fin H → EnvironmentStage State Action) (ρ : FiniteDistribution State)
    (fallback : State) (c₁ c₂ δ' : ℝ)
    (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) (hδ' : 0 < δ')
    (hδsmall : δ' ≤ 1 / 100)
    (hbranch : 2 * Nat.log2 (K * H) * δ' < 1) :
    1 - 2 * (H : ℝ) * (Nat.log2 (K * H) : ℝ) * δ' ≤
      (onlineSequentialEpisodeLaw H K hH E ρ fallback
        (onlineCappedGreedyPlanner E (Real.log (1 / δ')) c₁ c₂) (K * H)).rowMeasure.real
        (onlineT3AllSuffixSourceRadiusSet H K hH E ρ fallback c₁ c₂ δ') := by
  classical
  let q := Nat.log2 (K * H)
  let planner := onlineCappedGreedyPlanner E (Real.log (1 / δ')) c₁ c₂
  let μ : Measure ((Fin K → State) × OnlineOutcomePath.{uState, 0} State (K * H)) :=
    (onlineSequentialEpisodeLaw H K hH E ρ fallback planner (K * H)).rowMeasure
  have hprob (j : Fin H) :
      1 - 2 * q * δ' ≤ μ.real
        (onlineT3SuffixSourceRadiusSet H K hH E ρ fallback c₁ c₂ δ' j) := by
    simpa [q, μ, planner] using
      onlineT3Suffix_source_radius_probability H K q hH hN E
        ρ fallback c₁ c₂ δ' hc₁ hc₂ hδ' hδsmall rfl hbranch j
  have hmeas (j : Fin H) :
      MeasurableSet (onlineT3SuffixSourceRadiusSet H K hH E ρ fallback c₁ c₂ δ' j) := by
    exact MeasurableSpace.measurableSet_top
  let bad : Fin H → Set ((Fin K → State) × OnlineOutcomePath.{uState, 0} State (K * H)) :=
    fun j => (onlineT3SuffixSourceRadiusSet H K hH E ρ fallback c₁ c₂ δ' j)ᶜ
  have hbad (j : Fin H) : μ.real (bad j) ≤ 2 * q * δ' := by
    have hc := measureReal_compl (μ := μ) (hmeas j)
    rw [probReal_univ] at hc
    have hp := hprob j
    dsimp [bad]
    linarith
  have hbadUnion : μ.real (⋃ j : Fin H, bad j) ≤
      (H : ℝ) * (2 * q * δ') := by
    calc
      μ.real (⋃ j : Fin H, bad j) ≤ ∑ j : Fin H, μ.real (bad j) :=
        measureReal_iUnion_fintype_le _
      _ ≤ ∑ _j : Fin H, (2 * q * δ') := Finset.sum_le_sum fun j _ => hbad j
      _ = (H : ℝ) * (2 * q * δ') := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hgood : (⋃ j : Fin H, bad j)ᶜ =
      onlineT3AllSuffixSourceRadiusSet H K hH E ρ fallback c₁ c₂ δ' := by
    ext sample
    simp [bad, onlineT3AllSuffixSourceRadiusSet]
  have hbadMeas (j : Fin H) : MeasurableSet (bad j) := (hmeas j).compl
  have hc := measureReal_compl (μ := μ) (MeasurableSet.iUnion hbadMeas)
  rw [hgood, probReal_univ] at hc
  change 1 - 2 * (H : ℝ) * (Nat.log2 (K * H) : ℝ) * δ' ≤ μ.real _
  dsimp [q] at hbadUnion hc
  linarith

end StatisticalRL.OnlineRL
