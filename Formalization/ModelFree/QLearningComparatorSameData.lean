import Formalization.ModelFree.QLearningComparatorSandwich
import Formalization.ModelFree.QLearningChiSourceRadiusUnion

/-! Same-data source-index bridge and actual-law
comparator sandwich consumption. No coupling or independently resampled law. -/
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace StatisticalRL.QLearning
variable {State Action : Type*} [Fintype State] [Fintype Action]
local instance qComparatorSameStateMeasurable : MeasurableSpace State := ⊤
local instance qComparatorSameActionMeasurable : MeasurableSpace Action := ⊤

/-- Generic deterministic value: padded actual sample-layer sum is exactly the
source positive-update Icc sum on the very same data extension. -/
theorem qChiFixedFluctuationSum_eq_pathSum (M : DiscountedMDP State Action) (v : State → ℝ)
    (η : ℕ → ℝ) (T u : ℕ) (hu : u ≤ T) (s : State) (a : Action) (data : QSamples State Action T) :
    qChiFixedFluctuationSum M v η T u s a data = M.discount *
      ∑ i ∈ Finset.Icc (T/2+1) u, qPositiveWeight η u i *
        (v (qSamplesExtend M T data i s a) - (M.transition s a).expectation v) := by
  classical
  unfold qChiFixedFluctuationSum
  rw [Finset.mul_sum]
  have hf : (∑ n ∈ Finset.range T, qChiFixedFluctuationIncrement M v η T u s a n data) =
      ∑ n ∈ qActiveLayers T u, qChiFixedFluctuationIncrement M v η T u s a n data := by
    apply (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
    intro n hn hnot
    have hnT := Finset.mem_range.mp hn
    have hnot' : ¬(T/2 < n+1 ∧ n+1 ≤ u) := by simpa [qActiveLayers, hn] using hnot
    have hinactive : ¬(n<T ∧ T/2<n+1 ∧ n+1≤u) := by tauto
    exact congrFun (qChiFixedFluctuation_inactive M v η T u n s a hinactive) data
  rw [hf]
  let e := qActiveLayerEquiv T u hu
  rw [Finset.sum_subtype (qActiveLayers T u) (fun _ ↦ Iff.rfl),
    Finset.sum_subtype (Finset.Icc (T/2+1) u) (fun _ ↦ Iff.rfl)]
  apply Fintype.sum_equiv e
  intro n
  have hn := Finset.mem_filter.mp n.2
  have hactive : n.val<T ∧ T/2<n.val+1 ∧ n.val+1≤u :=
    ⟨Finset.mem_range.mp hn.1, hn.2.1, hn.2.2⟩
  simp [qChiFixedFluctuationIncrement, qChiFixedValueIncrement, hactive, e, qActiveLayerEquiv,
    qSamplesExtend_succ M T data n.val hactive.1]
  ring

/-- The exact comparator fluctuation in the probability event agrees with the
pathwise sandwich's source fluctuation, not merely in distribution. -/
theorem qComparator_sampledFluctuation_eq (M : DiscountedMDP State Action) (η : ℕ → ℝ)
    (T u : ℕ) (hu : u ≤ T) (Q : State → Action → ℝ) (s : State) (a : Action)
    (data : QSamples State Action T) :
    qChiComparatorFluctuation M η T u Q s a data =
      qComparatorPathFluctuation M η (qSamplesExtend M T data) Q (T/2) u s a := by
  simpa only [qChiComparatorFluctuation, qChiFixedFluctuationSum, qChiFixedFluctuationIncrement,
    qComparatorPathFluctuation] using
      qChiFixedFluctuationSum_eq_pathSum M (qLearningValue M Q) η T u hu s a data

noncomputable def qComparatorSampledSandwichEvent (M : DiscountedMDP State Action)
    (ρ : ℝ) (hρ : 0 ≤ ρ) (η : ℕ → ℝ) (T : ℕ) (Q₀ : State → Action → ℝ) :
    Set (QSamples State Action T) := {data | ∀ t, T/2 ≤ t → t ≤ T → ∀ s a,
      (qRobustMinusFixedPoint M ρ (2*ρ*M.effectiveHorizon) hρ s a -
        ((1+2*ρ+Real.sqrt ρ)*M.effectiveHorizon)*qComparatorRadiusProduct M.discount η (T/2) t ≤
          qLearningIterate M η (qSamplesExtend M T data) Q₀ t s a) ∧
      (qLearningIterate M η (qSamplesExtend M T data) Q₀ t s a ≤
        qRobustPlusFixedPoint M ρ (2*ρ*M.effectiveHorizon) hρ s a +
          ((1+2*ρ+Real.sqrt ρ)*M.effectiveHorizon)*qComparatorRadiusProduct M.discount η (T/2) t)}

/-- Every outcome in the actual common absorption event has the actual
pathwise sandwich throughout the full source terminal interval. -/
theorem qComparator_absorptionEvent_subset_sandwichEvent (M : DiscountedMDP State Action)
    (ρ : ℝ) (hρ : 0 ≤ ρ) (η : ℕ → ℝ) (T : ℕ) (Q₀ : State → Action → ℝ)
    (h₀ : ∀ s a, 0 ≤ Q₀ s a ∧ Q₀ s a ≤ M.effectiveHorizon)
    (hη : ∀ i, 1 ≤ i → i ≤ T → 0 ≤ η i ∧ η i ≤ 1) :
    qChiComparatorAbsorptionEvent M η T ρ hρ ⊆ qComparatorSampledSandwichEvent M ρ hρ η T Q₀ := by
  intro data hd
  have hplus (t : ℕ) (ht : T/2 < t) (htT : t ≤ T) (s : State) (a : Action) :
      |qComparatorPathFluctuation M η (qSamplesExtend M T data)
        (qRobustPlusFixedPoint M ρ (2*ρ*M.effectiveHorizon) hρ) (T/2) t s a| ≤
      qComparatorResidualPlus M (qRobustPlusFixedPoint M ρ (2*ρ*M.effectiveHorizon) hρ) s a := by
    let j : Fin T := ⟨t-1, by omega⟩
    have hj : j.val+1 = t := by dsimp [j]; omega
    have hh := hd s a j (by simpa only [hj] using ht)
    rw [hj] at hh
    rw [← qComparator_sampledFluctuation_eq M η T t htT]
    exact hh.1
  have hminus (t : ℕ) (ht : T/2 < t) (htT : t ≤ T) (s : State) (a : Action) :
      |qComparatorPathFluctuation M η (qSamplesExtend M T data)
        (qRobustMinusFixedPoint M ρ (2*ρ*M.effectiveHorizon) hρ) (T/2) t s a| ≤
      qComparatorResidualMinus M (qRobustMinusFixedPoint M ρ (2*ρ*M.effectiveHorizon) hρ) s a := by
    let j : Fin T := ⟨t-1, by omega⟩
    have hj : j.val+1 = t := by dsimp [j]; omega
    have hh := hd s a j (by simpa only [hj] using ht)
    rw [hj] at hh
    rw [← qComparator_sampledFluctuation_eq M η T t htT]
    exact hh.2
  exact qComparator_actual_sandwich M ρ hρ η (qSamplesExtend M T data) Q₀ h₀ (T/2) T
    (Nat.div_le_self _ _) hη hplus hminus

/-- Source-parameter actual product-law sandwich, with the very same sample
array in the concentration event and every Q-learning iterate. -/
theorem qComparator_actualSandwich_probability (M : DiscountedMDP State Action)
    (η : ℕ → ℝ) (c₁ c₂ δ : ℝ) (T : ℕ) (hT : 2 ≤ T)
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hs : qSourceRateSchedule M.discount c₁ c₂ T η)
    (Q₀ : State → Action → ℝ) (h₀ : ∀ s a, 0 ≤ Q₀ s a ∧ Q₀ s a ≤ M.effectiveHorizon) :
    let ρ := qChiSourceRadius (qChiSourceRateEnvelope M.discount c₂ T) δ
      (Fintype.card State) (Fintype.card Action) T
    ∃ hρ : 0 ≤ ρ, 1 - δ ≤ (qSamplingLaw M T).real (qComparatorSampledSandwichEvent M ρ hρ η T Q₀) := by
  obtain ⟨hρ, hp⟩ := qChi_actualComparatorAbsorption_probability M η c₁ c₂ δ T hT hc₁ hc₂ hδ hδ1 hs
  refine ⟨hρ, hp.trans ?_⟩
  apply measureReal_mono
  · apply qComparator_absorptionEvent_subset_sandwichEvent M _ hρ η T Q₀ h₀
    intro i hi hiT
    exact qSourceRate_unit_interval M.discount c₁ c₂ T η hT M.discount_lt_one hc₁ hc₂ hs i hiT
  · exact measure_ne_top _ _

end StatisticalRL.QLearning
