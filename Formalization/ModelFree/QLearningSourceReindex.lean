import Formalization.ModelFree.QLearningOptimalFluctuationWindow

/-! exact source indexing of fixed-terminal ξ. -/
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace StatisticalRL.QLearning
variable {State Action : Type*} [Fintype State] [Fintype Action]
local instance qOptReindexStateMeasurable : MeasurableSpace State := ⊤
local instance qOptReindexActionMeasurable : MeasurableSpace Action := ⊤

/-- Active sample layers, matching positive source update times. -/
noncomputable def qActiveLayers (T u : ℕ) : Finset ℕ :=
  (Finset.range T).filter (fun t ↦ T/2 < t+1 ∧ t+1 ≤ u)

/-- Source update i=t+1 is a bijection between active layers and the interval
floor(T/2)+1,…,u, including empty intervals. -/
noncomputable def qActiveLayerEquiv (T u : ℕ) (hu : u ≤ T) :
    {t // t ∈ qActiveLayers T u} ≃ {i // i ∈ Finset.Icc (T/2+1) u} where
  toFun t := ⟨t.1+1, by
    have ht := Finset.mem_filter.mp t.2
    exact Finset.mem_Icc.mpr ⟨by omega, ht.2.2⟩⟩
  invFun i := ⟨i.1-1, by
    have hi := Finset.mem_Icc.mp i.2
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_range.mpr (by omega), by omega, by omega⟩⟩
  left_inv t := by apply Subtype.ext; simp
  right_inv i := by
    have hi := Finset.mem_Icc.mp i.2
    apply Subtype.ext
    change i.1 - 1 + 1 = i.1
    omega

/-- Exact source-indexed fluctuation sum, on the actual common sample array. -/
theorem qOptimalFluctuation_eq_sourceIndexed (M : DiscountedMDP State Action) (η : ℕ → ℝ)
    (T u : ℕ) (hu : u ≤ T) (s : State) (a : Action) (data : QSamples State Action T) :
    qOptimalFluctuation M η T u s a data = qSourceIndexedFluctuation M η T u hu s a data := by
  classical
  unfold qOptimalFluctuation qSourceIndexedFluctuation
  have hf : (∑ t ∈ Finset.range T, qOptimalFluctuationIncrement M η T u s a t data) =
      ∑ t ∈ qActiveLayers T u, qOptimalFluctuationIncrement M η T u s a t data := by
    apply (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
    intro t ht hnot
    have htT := Finset.mem_range.mp ht
    have hn : ¬ (T/2 < t+1 ∧ t+1 ≤ u) := by
      simpa [qActiveLayers, ht] using hnot
    have hn' : ¬ (t < T ∧ T/2 < t+1 ∧ t+1 ≤ u) := by tauto
    exact congrFun (qOptimalFluctuation_inactive M η T u t s a hn') data
  rw [hf]
  let e := qActiveLayerEquiv T u hu
  rw [Finset.sum_subtype (qActiveLayers T u) (fun _ ↦ Iff.rfl)]
  apply Fintype.sum_equiv e
  intro t
  have ht := Finset.mem_filter.mp t.2
  have hactive : t.1 < T ∧ T/2 < t.1+1 ∧ t.1+1 ≤ u :=
    ⟨Finset.mem_range.mp ht.1, ht.2.1, ht.2.2⟩
  simp [qOptimalFluctuationIncrement, hactive, e, qActiveLayerEquiv]

end StatisticalRL.QLearning
