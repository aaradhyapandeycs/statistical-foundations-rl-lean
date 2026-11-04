import Formalization.Online.Regret.T3.OnlineT3SuffixMasked

/-! One deterministic stage-suffix T₃ event, transported to the source's
actual optimistic-variance proxy. The finite union over suffix starts is a
separate theorem. -/

namespace StatisticalRL.OnlineRL
open MeasureTheory ProbabilityTheory

universe uState uAction
variable {State : Type uState} {Action : Type uAction}
  [Fintype State] [Fintype Action]
noncomputable local instance t3SuffixRadiusStateMeasurable : MeasurableSpace State :=
  StatisticalRL.FiniteDistribution.empiricalRowStateMeasurable
noncomputable local instance t3SuffixRadiusSampleMeasurable (H K : ℕ) :
    MeasurableSpace ((Fin K → State) × OnlineOutcomePath.{uState, 0} State (K * H)) :=
  StatisticalRL.FiniteDistribution.empiricalRowStateMeasurable
noncomputable local instance t3SuffixRadiusStateDecidable : DecidableEq State := Classical.decEq State
noncomputable local instance t3SuffixRadiusActionDecidable : DecidableEq Action := Classical.decEq Action

/-- Explicit actual-law suffix event, kept folded to control consumer
elaboration. Its body is the actual T₆-UCB source radius. -/
@[irreducible] noncomputable def onlineT3SuffixSourceRadiusSet
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (ρ : FiniteDistribution State) (fallback : State) (c₁ c₂ δ' : ℝ)
    (j : Fin H) :
    Set ((Fin K → State) × OnlineOutcomePath.{uState, 0} State (K * H)) := by
  let L := Real.log (1 / δ')
  let planner := onlineCappedGreedyPlanner E L c₁ c₂
  exact {sample | |incrementSum
      (onlineT3SuffixMaskedY H K hH E ρ fallback planner L c₁ c₂ j) (K * H) sample| ≤
    Real.sqrt (8 * onlineActualT6UCB H K hH E sample.1 fallback sample.2 δ' c₁ c₂ * L) +
      5 * (H : ℝ) * L}

/-- A single stage-suffix source radius event, with the genuine actual T₆-UCB
proxy on the right-hand side. -/
theorem onlineT3Suffix_source_radius_probability
    (H K q : ℕ) (hH : 0 < H) (hN : 2 ≤ K * H)
    (E : Fin H → EnvironmentStage State Action) (ρ : FiniteDistribution State)
    (fallback : State) (c₁ c₂ δ' : ℝ)
    (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) (hδ' : 0 < δ')
    (hδsmall : δ' ≤ 1 / 100) (hq : q = Nat.log2 (K * H))
    (hbranch : 2 * q * δ' < 1) (j : Fin H) :
    1 - 2 * q * δ' ≤
      (onlineSequentialEpisodeLaw H K hH E ρ fallback
        (onlineCappedGreedyPlanner E (Real.log (1 / δ')) c₁ c₂) (K * H)).rowMeasure.real
        (onlineT3SuffixSourceRadiusSet H K hH E ρ fallback c₁ c₂ δ' j) := by
  classical
  let L := Real.log (1 / δ')
  let planner := onlineCappedGreedyPlanner E L c₁ c₂
  let μ : Measure ((Fin K → State) × OnlineOutcomePath.{uState, 0} State (K * H)) :=
    (onlineSequentialEpisodeLaw H K hH E ρ fallback planner (K * H)).rowMeasure
  let ℱ := onlineT3ActualPrefixFiltration H K hH fallback planner
  let X := onlineT3SuffixMaskedY H K hH E ρ fallback planner L c₁ c₂ j
  change 1 - 2 * q * δ' ≤ μ.real
    (onlineT3SuffixSourceRadiusSet H K hH E ρ fallback c₁ c₂ δ' j)
  have hqpos : 0 < q := by
    rw [hq]
    exact (onlineT3_natLog2_ratio_bounds (K * H) hN).1
  have hL : 2 ≤ L := onlineT3_sourceLog_ge_two δ' hδ' hδsmall
  have hL0 : 0 ≤ L := by linarith
  let δF : ℝ := 2 * q * δ'
  have hδF : 0 < δF := by dsimp [δF]; positivity
  have hδF1 : δF < 1 := by simpa [δF] using hbranch
  have hlog : Real.log (2 * (q : ℝ) / δF) = L := by
    dsimp [L, δF]
    congr 1
    field_simp
  have hX : ∀ n, StronglyMeasurable[ℱ (n + 1)] (X n) := by
    intro n
    exact (onlineT3SuffixMaskedY_measurable_next
      H K hH E ρ fallback planner L c₁ c₂ j n).stronglyMeasurable
  have hb : ∀ n, ∀ᵐ sample ∂μ, |X n sample| ≤ (H : ℝ) := by
    intro n
    exact Filter.Eventually.of_forall (fun sample =>
      onlineT3SuffixMaskedY_abs_le_H H K hH E ρ fallback planner
        L c₁ c₂ hL0 hc₁ hc₂ j n sample)
  have hc : ∀ n, μ[X n | ℱ n] =ᵐ[μ] fun _ => 0 := by
    intro n
    exact onlineT3SuffixMaskedY_condExp_zero H K hH E ρ fallback planner L c₁ c₂ j n
  have hsum := onlineT3SuffixPredictableSecondMomentSum_eq_maskedRowVarianceSum
    H K hH E ρ fallback planner L c₁ c₂ j (K * H)
  have hcap : ∀ᵐ sample ∂μ,
      predictableSecondMomentSum μ ℱ X (K * H) sample ≤ (K : ℝ) * (H : ℝ)^3 := by
    filter_upwards [hsum] with sample hsum
    rw [hsum]
    calc
      (∑ n ∈ Finset.range (K * H),
        if j.val ≤ n % H then
          onlineT3PaddedRowVariance H K hH E fallback planner L c₁ c₂ n sample
        else 0) ≤
        ∑ _n ∈ Finset.range (K * H), (H : ℝ)^2 := by
          apply Finset.sum_le_sum
          intro n hn
          split_ifs with hkeep
          · exact (onlineT3PaddedRowVariance_le_H_sq H K hH E fallback planner
              L c₁ c₂ hL0 hc₁ hc₂ n sample).2
          · positivity
      _ = (K : ℝ) * (H : ℝ)^3 := by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast
        ring
  have hfixedRaw := StatisticalRL.freedman_source_bound μ ℱ X (H : ℝ)
    ((K : ℝ) * (H : ℝ)^3) (by positivity) (by positivity)
    hX hb hc (K * H) q hqpos hcap δF hδF hδF1
  have hfixed : 1 - δF ≤ μ.real
      (onlineFreedmanPeeledRadiusSet μ ℱ X (K * H) (H : ℝ)
        ((K : ℝ) * (H : ℝ)^3) q L) := by
    change 1 - δF ≤ μ.real {sample | _} at hfixedRaw
    simpa [onlineFreedmanPeeledRadiusSet, μ, ℱ, X, L, planner, hlog] using hfixedRaw
  have hvar := predictableSecondMomentSum_nonneg μ ℱ X (K * H)
  let N := K * H
  let qreal : ℝ := (N : ℝ) / (2 : ℝ)^q
  have hqrange := onlineT3_natLog2_ratio_bounds N hN
  dsimp [N] at hqrange
  rw [← hq] at hqrange
  rcases hqrange with ⟨_, hqone, hqtwo⟩
  have hq0 : 0 ≤ qreal := by
    dsimp [qreal]
    positivity
  have hqle2 : qreal ≤ 2 := le_of_lt hqtwo
  have hσq : ((K : ℝ) * (H : ℝ)^3) / (2 : ℝ)^q = qreal * (H : ℝ)^2 := by
    dsimp [qreal, N]
    push_cast
    field_simp
  have hproxyRadius := onlineFreedman_peeledProbability_le_source μ ℱ X (K * H)
    (H : ℝ) ((K : ℝ) * (H : ℝ)^3) qreal L δF q hvar
    (by positivity) hσq hq0 hqle2 hL hfixed
  have hproxyT6 := onlineT3SuffixPredictableSecondMomentSum_le_actualT6UCB
    H K hH E ρ fallback c₁ c₂ δ' hL0 hc₁ hc₂ j
  have hsubset : onlineFreedmanSourceRadiusSet μ ℱ X (K * H) (H : ℝ) L ≤ᵐ[μ]
      {sample | |incrementSum X (K * H) sample| ≤
        Real.sqrt (8 * onlineActualT6UCB H K hH E sample.1 fallback sample.2
          δ' c₁ c₂ * L) + 5 * (H : ℝ) * L} := by
    filter_upwards [hproxyT6, hvar] with sample hproxy hnonneg
    intro hgood
    dsimp [onlineFreedmanSourceRadiusSet] at hgood
    have ht6nonneg : 0 ≤ onlineActualT6UCB H K hH E sample.1 fallback sample.2
        δ' c₁ c₂ := le_trans hnonneg hproxy
    have hrad : 8 * predictableSecondMomentSum μ ℱ X (K * H) sample * L ≤
        8 * onlineActualT6UCB H K hH E sample.1 fallback sample.2 δ' c₁ c₂ * L :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hproxy (by norm_num)) hL0
    have hsqrt := Real.sqrt_le_sqrt hrad
    exact hgood.trans (by nlinarith [hsqrt])
  have hmono := ENNReal.toReal_mono
    (measure_ne_top μ {sample | |incrementSum X (K * H) sample| ≤
      Real.sqrt (8 * onlineActualT6UCB H K hH E sample.1 fallback sample.2
        δ' c₁ c₂ * L) + 5 * (H : ℝ) * L})
    (measure_mono_ae hsubset)
  change 1 - 2 * q * δ' ≤ _ at hproxyRadius
  have hprob := hproxyRadius.trans hmono
  simpa [δF, L, planner, μ, X, onlineT3SuffixSourceRadiusSet] using hprob

end StatisticalRL.OnlineRL
