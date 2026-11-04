import Formalization.Online.Regret.MVP.Probability.MVPActualPositiveParts

/-! Uniform actual-product positive-part concentration with explicit log budget. -/
namespace StatisticalRL.FiniteHorizonGenerative
open MeasureTheory ProbabilityTheory StatisticalRL.OnlineRL
open scoped BigOperators
variable {State Action ι : Type*} [Fintype State] [Fintype Action] [Fintype ι] [Nonempty ι]
local instance : MeasurableSpace State := ⊤
noncomputable local instance mvpUniformStateDecidable : DecidableEq State := Classical.decEq State
noncomputable local instance mvpUniformActionDecidable : DecidableEq Action := Classical.decEq Action

theorem mvp_finiteUniform_positiveParts {H : ℕ} (E : Fin H → EnvironmentStage State Action)
    (K : ℕ) (n : ι → ℕ) (hn : ∀ i, 2*n i ≤ K) (hnpos : ∀ i, 0<n i)
    (V : (i : ι) → (h : Fin H) → State → Action → FutureCode (State := State) (Action := Action) h K → State → ℝ)
    (hV : ∀ i h s a code x, 0 ≤ V i h s a code x ∧ V i h s a code x ≤ H)
    (peels : ℕ) (hp : 0 < peels) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    let Mask := Fin H → State → Action → Bool
    let ε := δ / (Fintype.card (ι × Mask) : ℝ)
    1 - δ ≤ (samplingLaw E K).real {data | ∀ i : ι,
      (∑ h : Fin H, ∑ s : State, ∑ a : Action,
        max ((FiniteDistribution.empiricalRow (n i) (hnpos i)
            (fun j => data ((h,s,a),mvpBatchIndex K (n i) (hn i) j))).expectation
                (V i h s a (futureData h K data)) -
              ((E h).transition s a).expectation (V i h s a (futureData h K data))) 0) ≤
      (Real.sqrt (8 * max
          (((n i : ℕ) : ℝ) * ∑ h : Fin H, ∑ s : State, ∑ a : Action,
            ((E h).transition s a).variance (V i h s a (futureData h K data)))
          ((((n i : ℕ) : ℝ) * H * Fintype.card State * Fintype.card Action * (H : ℝ)^2) / (2 : ℝ)^peels) *
          Real.log (2 * peels / ε)) + (4/3) * H * Real.log (2 * peels / ε)) / n i} := by
  classical
  let Mask := Fin H → State → Action → Bool
  let m : ℝ := Fintype.card (ι × Mask)
  let ε := δ / m
  have hm : 0 < m := by dsimp [m]; exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
  have hm1 : 1 ≤ m := by dsimp [m]; exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
  have heps : 0 < ε := div_pos hδ hm
  have heps1 : ε < 1 := (div_lt_iff₀ hm).2 (by linarith)
  have hp1 : (1:ℝ) ≤ peels := by exact_mod_cast hp
  have hL : 0 ≤ Real.log (2*peels/ε) := by
    apply Real.log_nonneg
    apply (le_div_iff₀ heps).2
    nlinarith
  let A := ⋂ i : ι, ⋂ mask : Mask,
    mvpFixedMaskBatchEvent E K (n i) (hn i) (hnpos i) mask (V i) peels ε
  have hA : 1-δ ≤ (samplingLaw E K).real A :=
    mvp_uniform_allMasks_batchFreedman E K n hn hnpos V hV peels hp δ hδ hδ1
  have hsub : A ⊆ {data | ∀ i : ι,
      (∑ h : Fin H, ∑ s : State, ∑ a : Action,
        max ((FiniteDistribution.empiricalRow (n i) (hnpos i)
            (fun j => data ((h,s,a),mvpBatchIndex K (n i) (hn i) j))).expectation
                (V i h s a (futureData h K data)) -
              ((E h).transition s a).expectation (V i h s a (futureData h K data))) 0) ≤
      (Real.sqrt (8 * max
          (((n i : ℕ) : ℝ) * ∑ h : Fin H, ∑ s : State, ∑ a : Action,
            ((E h).transition s a).variance (V i h s a (futureData h K data)))
          ((((n i : ℕ) : ℝ) * H * Fintype.card State * Fintype.card Action * (H : ℝ)^2) / (2 : ℝ)^peels) *
          Real.log (2 * peels / ε)) + (4/3) * H * Real.log (2 * peels / ε)) / n i} := by
    intro data hd i
    have hgood : ∀ mask : Mask, data ∈ mvpFixedMaskBatchEvent E K (n i) (hn i) (hnpos i) mask (V i) peels ε := by
      have hd' : ∀ i : ι, ∀ mask : Mask, data ∈ mvpFixedMaskBatchEvent E K (n i) (hn i) (hnpos i) mask (V i) peels ε := by
        simpa [A] using hd
      exact hd' i
    exact mvp_allMasks_imply_positiveParts E K (n i) (hn i) (hnpos i) (V i) peels ε hL data hgood
  have hm := measureReal_mono hsub (measure_ne_top (samplingLaw E K) _)
  exact hA.trans hm
end StatisticalRL.FiniteHorizonGenerative
