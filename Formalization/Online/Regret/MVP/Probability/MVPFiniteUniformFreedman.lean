import Formalization.Online.Regret.MVP.Probability.MVPActualBatchFreedman
import Formalization.Online.Regret.MVP.Probability.MVPFiniteUnion

/-! Simultaneous actual-product aggregate Freedman over any finite index type. -/
namespace StatisticalRL.FiniteHorizonGenerative
open MeasureTheory ProbabilityTheory StatisticalRL.OnlineRL
open scoped BigOperators
variable {State Action ι : Type*} [Fintype State] [Fintype Action] [Fintype ι] [Nonempty ι]
local instance : MeasurableSpace State := ⊤

noncomputable def mvpFixedMaskBatchEvent {H : ℕ} (E : Fin H → EnvironmentStage State Action)
    (K n : ℕ) (hn : 2*n ≤ K) (hnpos : 0<n) (mask : Fin H → State → Action → Bool)
    (V : (h : Fin H) → State → Action → FutureCode (State := State) (Action := Action) h K → State → ℝ)
    (peels : ℕ) (δ : ℝ) : Set (Samples State Action H K) := {data |
      |∑ h : Fin H, ∑ s : State, ∑ a : Action,
        if mask h s a then
          (FiniteDistribution.empiricalRow n hnpos (fun j => data ((h,s,a),mvpBatchIndex K n hn j))).expectation
              (V h s a (futureData h K data)) -
            ((E h).transition s a).expectation (V h s a (futureData h K data))
        else 0| ≤
      (Real.sqrt (8 * max
          ((n : ℝ) * ∑ h : Fin H, ∑ s : State, ∑ a : Action,
            if mask h s a then ((E h).transition s a).variance (V h s a (futureData h K data)) else 0)
          (((n : ℝ) * H * Fintype.card State * Fintype.card Action * (H : ℝ)^2) / (2 : ℝ)^peels) *
          Real.log (2 * peels / δ)) + (4/3) * H * Real.log (2 * peels / δ)) / n}

theorem mvp_finiteUniform_batchFreedman {H : ℕ} (E : Fin H → EnvironmentStage State Action)
    (K : ℕ) (n : ι → ℕ) (hn : ∀ i, 2*n i ≤ K) (hnpos : ∀ i, 0<n i)
    (mask : ι → Fin H → State → Action → Bool)
    (V : (i : ι) → (h : Fin H) → State → Action → FutureCode (State := State) (Action := Action) h K → State → ℝ)
    (hV : ∀ i h s a code x, 0 ≤ V i h s a code x ∧ V i h s a code x ≤ H)
    (peels : ℕ) (hp : 0 < peels) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    1 - δ ≤ (samplingLaw E K).real (⋂ i : ι,
      mvpFixedMaskBatchEvent E K (n i) (hn i) (hnpos i) (mask i) (V i) peels
        (δ / Fintype.card ι)) := by
  classical
  let m : ℝ := Fintype.card ι
  have hm : 0 < m := by dsimp [m]; exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
  have hm1 : 1 ≤ m := by dsimp [m]; exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
  have hε : 0 < δ/m := div_pos hδ hm
  have hε1 : δ/m < 1 := (div_lt_iff₀ hm).2 (by linarith)
  have hg : ∀ i : ι, 1 - δ/m ≤ (samplingLaw E K).real
      (mvpFixedMaskBatchEvent E K (n i) (hn i) (hnpos i) (mask i) (V i) peels (δ/m)) := by
    intro i
    exact mvp_actualBatchFixedMask_freedman E K (n i) (hn i) (hnpos i)
      (mask i) (V i) (hV i) peels hp (δ/m) hε hε1
  have h := mvp_finite_goodEvent_union (samplingLaw E K)
    (fun i : ι => mvpFixedMaskBatchEvent E K (n i) (hn i) (hnpos i) (mask i) (V i) peels (δ/m)) (δ/m) hg
  have hmne : m ≠ 0 := ne_of_gt hm
  have heq : m*(δ/m) = δ := by field_simp
  simpa [m, heq] using h
end StatisticalRL.FiniteHorizonGenerative
