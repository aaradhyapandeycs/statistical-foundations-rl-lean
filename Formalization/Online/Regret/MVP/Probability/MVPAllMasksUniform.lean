import Formalization.Online.Regret.MVP.Probability.MVPFiniteUniformFreedman

/-! Uniform actual-product Freedman simultaneously over all fixed row masks. -/
namespace StatisticalRL.FiniteHorizonGenerative
open MeasureTheory ProbabilityTheory StatisticalRL.OnlineRL
variable {State Action ι : Type*} [Fintype State] [Fintype Action] [Fintype ι] [Nonempty ι]
local instance : MeasurableSpace State := ⊤
noncomputable local instance mvpMaskStateDecidable : DecidableEq State := Classical.decEq State
noncomputable local instance mvpMaskActionDecidable : DecidableEq Action := Classical.decEq Action

theorem mvp_uniform_allMasks_batchFreedman {H : ℕ} (E : Fin H → EnvironmentStage State Action)
    (K : ℕ) (n : ι → ℕ) (hn : ∀ i, 2*n i ≤ K) (hnpos : ∀ i, 0<n i)
    (V : (i : ι) → (h : Fin H) → State → Action → FutureCode (State := State) (Action := Action) h K → State → ℝ)
    (hV : ∀ i h s a code x, 0 ≤ V i h s a code x ∧ V i h s a code x ≤ H)
    (peels : ℕ) (hp : 0 < peels) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    let Mask := Fin H → State → Action → Bool
    let ε := δ / (Fintype.card (ι × Mask) : ℝ)
    1 - δ ≤ (samplingLaw E K).real (⋂ i : ι, ⋂ mask : Mask,
      mvpFixedMaskBatchEvent E K (n i) (hn i) (hnpos i) mask (V i) peels ε) := by
  classical
  let Mask := Fin H → State → Action → Bool
  have h := mvp_finiteUniform_batchFreedman (ι := ι × Mask) E K
    (fun p => n p.1) (fun p => hn p.1) (fun p => hnpos p.1)
    (fun p => p.2) (fun p => V p.1) (fun p => hV p.1) peels hp δ hδ hδ1
  have heq : (⋂ p : ι × Mask, mvpFixedMaskBatchEvent E K (n p.1) (hn p.1)
      (hnpos p.1) p.2 (V p.1) peels (δ / Fintype.card (ι × Mask))) =
      (⋂ i : ι, ⋂ mask : Mask, mvpFixedMaskBatchEvent E K (n i) (hn i)
        (hnpos i) mask (V i) peels (δ / Fintype.card (ι × Mask))) := by
    ext x
    simp only [Set.mem_iInter]
    constructor
    · intro h i mask
      exact h (i,mask)
    · intro h p
      exact h p.1 p.2
  rw [heq] at h
  exact h
end StatisticalRL.FiniteHorizonGenerative
