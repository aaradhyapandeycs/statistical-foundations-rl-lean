import Formalization.Online.Regret.T3.OnlineRegretT3VarianceTransport
import Formalization.Online.Regret.T3.OnlineRegretT3SourceBound

/-! Deterministically suffix-masked actual T₃ increments on the existing
common full-horizon experiment. The stage mask depends only on the time
index, so it is predictable and preserves conditional centering. -/

namespace StatisticalRL.OnlineRL
open MeasureTheory ProbabilityTheory
open scoped BigOperators

universe uState uAction
variable {State : Type uState} {Action : Type uAction}
  [Fintype State] [Fintype Action]
noncomputable local instance t3SuffixStateMeasurable : MeasurableSpace State :=
  StatisticalRL.FiniteDistribution.empiricalRowStateMeasurable
noncomputable local instance t3SuffixSampleMeasurable (H K : ℕ) :
    MeasurableSpace ((Fin K → State) × OnlineOutcomePath.{uState, 0} State (K * H)) :=
  StatisticalRL.FiniteDistribution.empiricalRowStateMeasurable
noncomputable local instance t3SuffixStateDecidable : DecidableEq State := Classical.decEq State
noncomputable local instance t3SuffixActionDecidable : DecidableEq Action := Classical.decEq Action

/-- The T₃ process retaining only stages at or after `j` in every episode.
The mask is the deterministic condition `j ≤ n % H`. -/
noncomputable def onlineT3SuffixMaskedY
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (ρ : FiniteDistribution State) (fallback : State)
    (planner : OnlineEpisodePlanner State Action H) (L c₁ c₂ : ℝ)
    (j : Fin H) (n : ℕ)
    (sample : (Fin K → State) × OnlineOutcomePath.{uState, 0} State (K * H)) : ℝ :=
  if j.val ≤ n % H then
    onlineT3PaddedY H K hH E ρ fallback planner L c₁ c₂ n sample
  else 0

/-- The masked process remains measurable at the next actual prefix. -/
theorem onlineT3SuffixMaskedY_measurable_next
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (ρ : FiniteDistribution State) (fallback : State)
    (planner : OnlineEpisodePlanner State Action H) (L c₁ c₂ : ℝ)
    (j : Fin H) (n : ℕ) :
    Measurable[onlineT3CommonPrefixSigma H K (K * H) hH fallback planner (n + 1)]
      (onlineT3SuffixMaskedY H K hH E ρ fallback planner L c₁ c₂ j n) := by
  change Measurable[onlineT3CommonPrefixSigma H K (K * H) hH fallback planner (n + 1)]
    (fun sample => if j.val ≤ n % H then
      onlineT3PaddedY H K hH E ρ fallback planner L c₁ c₂ n sample else 0)
  by_cases hmask : j.val ≤ n % H
  · simpa [onlineT3SuffixMaskedY, hmask] using
      onlineT3PaddedY_measurable_next H K hH E ρ fallback planner L c₁ c₂ n
  · simpa [hmask] using (measurable_const : Measurable[onlineT3CommonPrefixSigma
      H K (K * H) hH fallback planner (n + 1)] (fun _ => (0 : ℝ)))

/-- Deterministic masking preserves conditional centering under the actual
sequential episode law. -/
theorem onlineT3SuffixMaskedY_condExp_zero
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (ρ : FiniteDistribution State) (fallback : State)
    (planner : OnlineEpisodePlanner State Action H) (L c₁ c₂ : ℝ)
    (j : Fin H) (n : ℕ) :
    let μ := (onlineSequentialEpisodeLaw H K hH E ρ fallback planner (K * H)).rowMeasure
    μ[onlineT3SuffixMaskedY H K hH E ρ fallback planner L c₁ c₂ j n |
      onlineT3CommonPrefixSigma H K (K * H) hH fallback planner n] =ᵐ[μ] 0 := by
  classical
  let μ := (onlineSequentialEpisodeLaw H K hH E ρ fallback planner (K * H)).rowMeasure
  change μ[(fun sample => if j.val ≤ n % H then
      onlineT3PaddedY H K hH E ρ fallback planner L c₁ c₂ n sample else 0) |
      onlineT3CommonPrefixSigma H K (K * H) hH fallback planner n] =ᵐ[μ] 0
  by_cases hmask : j.val ≤ n % H
  · simpa [hmask] using
      (onlineT3PaddedY_condExp_zero H K hH E ρ fallback planner L c₁ c₂ n)
  · have hz : (fun sample : (Fin K → State) × OnlineOutcomePath.{uState, 0} State (K * H) =>
        if j.val ≤ n % H then
          onlineT3PaddedY H K hH E ρ fallback planner L c₁ c₂ n sample else 0) =
        fun _ => (0 : ℝ) := by
      funext sample
      simp [hmask]
    rw [hz]
    have hzero : μ[(0 : ((Fin K → State) × OnlineOutcomePath.{uState, 0} State (K * H)) → ℝ) |
        onlineT3CommonPrefixSigma H K (K * H) hH fallback planner n] =
        (0 : ((Fin K → State) × OnlineOutcomePath.{uState, 0} State (K * H)) → ℝ) :=
      MeasureTheory.condExp_zero
    change μ[(0 : ((Fin K → State) × OnlineOutcomePath.{uState, 0} State (K * H)) → ℝ) |
        onlineT3CommonPrefixSigma H K (K * H) hH fallback planner n] =ᵐ[μ]
      (0 : ((Fin K → State) × OnlineOutcomePath.{uState, 0} State (K * H)) → ℝ)
    rw [hzero]

/-- The suffix-masked increment keeps the source cap `H`. -/
theorem onlineT3SuffixMaskedY_abs_le_H
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (ρ : FiniteDistribution State) (fallback : State)
    (planner : OnlineEpisodePlanner State Action H) (L c₁ c₂ : ℝ)
    (hL : 0 ≤ L) (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂)
    (j : Fin H) (n : ℕ)
    (sample : (Fin K → State) × OnlineOutcomePath.{uState, 0} State (K * H)) :
    |onlineT3SuffixMaskedY H K hH E ρ fallback planner L c₁ c₂ j n sample| ≤ H := by
  by_cases hmask : j.val ≤ n % H
  · simpa [onlineT3SuffixMaskedY, hmask] using
      onlineT3PaddedY_abs_le_H H K hH E ρ fallback planner L c₁ c₂
        hL hc₁ hc₂ n sample
  · simp [onlineT3SuffixMaskedY, hmask]

/-- The predictable second-moment sum of a deterministic suffix mask equals
the sum of the selected row variances at the retained stages. -/
theorem onlineT3SuffixPredictableSecondMomentSum_eq_maskedRowVarianceSum
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (ρ : FiniteDistribution State) (fallback : State)
    (planner : OnlineEpisodePlanner State Action H) (L c₁ c₂ : ℝ)
    (j : Fin H) :
    let μ := (onlineSequentialEpisodeLaw H K hH E ρ fallback planner (K * H)).rowMeasure
    let ℱ := onlineT3ActualPrefixFiltration H K hH fallback planner
    ∀ N, ∀ᵐ sample ∂μ,
      predictableSecondMomentSum μ ℱ
        (onlineT3SuffixMaskedY H K hH E ρ fallback planner L c₁ c₂ j) N sample =
      ∑ n ∈ Finset.range N,
        if j.val ≤ n % H then
          onlineT3PaddedRowVariance H K hH E fallback planner L c₁ c₂ n sample
        else 0 := by
  classical
  dsimp
  let μ := (onlineSequentialEpisodeLaw H K hH E ρ fallback planner (K * H)).rowMeasure
  let ℱ := onlineT3ActualPrefixFiltration H K hH fallback planner
  let X := onlineT3SuffixMaskedY H K hH E ρ fallback planner L c₁ c₂ j
  let V := onlineT3PaddedRowVariance H K hH E fallback planner L c₁ c₂
  have hterm (n : ℕ) :
      μ[(fun sample => X n sample ^ 2) | ℱ n] =ᵐ[μ]
        fun sample => if j.val ≤ n % H then V n sample else 0 := by
    by_cases hmask : j.val ≤ n % H
    · simpa [X, hmask, onlineT3SuffixMaskedY, V] using
        (onlineT3PaddedY_sq_condExp_eq_rowVariance
          H K hH E ρ fallback planner L c₁ c₂ n)
    · have hz : X n = (fun _ => (0 : ℝ)) := by
        funext sample
        simp [X, onlineT3SuffixMaskedY, hmask]
      rw [hz]
      have hcond : μ[(fun _ : (Fin K → State) × OnlineOutcomePath.{uState, 0} State (K * H) =>
          (0 : ℝ)) | ℱ n] = (fun _ => (0 : ℝ)) := by
        exact MeasureTheory.condExp_zero
      filter_upwards [] with sample
      simpa [hmask, hcond]
  intro N
  induction N with
  | zero => filter_upwards [] with sample; simp [predictableSecondMomentSum]
  | succ N ih =>
      filter_upwards [ih, hterm N] with sample hprev hlast
      change (∑ n ∈ Finset.range (N + 1), μ[fun ω => X n ω ^ 2 | ℱ n] sample) = _
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      change (∑ n ∈ Finset.range N, μ[fun ω => X n ω ^ 2 | ℱ n] sample) = _ at hprev
      rw [hprev, hlast]

/-- Masking can only reduce the actual predictable variance, pointwise almost
surely; the unmasked sum is exactly the source T₆-UCB proxy. -/
theorem onlineT3SuffixPredictableSecondMomentSum_le_actualT6UCB
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (ρ : FiniteDistribution State) (fallback : State) (c₁ c₂ δ : ℝ)
    (hL : 0 ≤ Real.log (1 / δ)) (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) (j : Fin H) :
    let planner := onlineCappedGreedyPlanner E (Real.log (1 / δ)) c₁ c₂
    let μ := (onlineSequentialEpisodeLaw H K hH E ρ fallback planner (K * H)).rowMeasure
    let ℱ := onlineT3ActualPrefixFiltration H K hH fallback planner
    ∀ᵐ sample ∂μ,
      predictableSecondMomentSum μ ℱ
        (onlineT3SuffixMaskedY H K hH E ρ fallback planner
          (Real.log (1 / δ)) c₁ c₂ j) (K * H) sample ≤
        onlineActualT6UCB H K hH E sample.1 fallback sample.2 δ c₁ c₂ := by
  classical
  dsimp
  let planner := onlineCappedGreedyPlanner E (Real.log (1 / δ)) c₁ c₂
  let μ : Measure ((Fin K → State) × OnlineOutcomePath.{uState, 0} State (K * H)) :=
    (onlineSequentialEpisodeLaw H K hH E ρ fallback planner (K * H)).rowMeasure
  let ℱ := onlineT3ActualPrefixFiltration H K hH fallback planner
  let V := onlineT3PaddedRowVariance H K hH E fallback planner
    (Real.log (1 / δ)) c₁ c₂
  have hmasked := onlineT3SuffixPredictableSecondMomentSum_eq_maskedRowVarianceSum
    H K hH E ρ fallback planner (Real.log (1 / δ)) c₁ c₂ j (K * H)
  filter_upwards [hmasked] with sample hsample
  rw [hsample]
  calc
    (∑ n ∈ Finset.range (K * H), if j.val ≤ n % H then V n sample else 0) ≤
        ∑ n ∈ Finset.range (K * H), V n sample := by
          apply Finset.sum_le_sum
          intro n hn
          split_ifs
          · exact le_rfl
          · exact (onlineT3PaddedRowVariance_le_H_sq H K hH E fallback planner
              (Real.log (1 / δ)) c₁ c₂ hL hc₁ hc₂ n sample).1
    _ = onlineActualT6UCB H K hH E sample.1 fallback sample.2 δ c₁ c₂ :=
      onlineT3PaddedRowVarianceSum_eq_actualT6UCB H K hH E sample.1 fallback
        sample.2 δ c₁ c₂

end StatisticalRL.OnlineRL
