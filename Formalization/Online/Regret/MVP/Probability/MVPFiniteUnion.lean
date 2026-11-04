import Formalization.Probability.BernsteinFamily

/-! Finite-union accounting for a family of simultaneous good events. -/
namespace StatisticalRL.OnlineRL
open MeasureTheory ProbabilityTheory
open scoped BigOperators
variable {Ω ι : Type*} [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
  [Fintype ι]

/-- Uniformize already-proved single-index estimates; this lemma itself
makes no assertion about how those estimates are obtained. -/
theorem mvp_finite_goodEvent_union (μ : Measure Ω) [IsProbabilityMeasure μ]
    (good : ι → Set Ω) (ε : ℝ)
    (hgood : ∀ i, 1-ε ≤ μ.real (good i)) :
    1 - (Fintype.card ι : ℝ)*ε ≤ μ.real (⋂ i, good i) := by
  classical
  let bad : ι → Set Ω := fun i => (good i)ᶜ
  have hb (i : ι) : μ.real (bad i) ≤ ε := by
    have hc := measureReal_compl (μ := μ) ((Set.to_countable (good i)).measurableSet)
    rw [probReal_univ] at hc
    dsimp [bad]
    linarith [hgood i]
  have hsum : μ.real (⋃ i, bad i) ≤ (Fintype.card ι : ℝ)*ε := by
    calc
      _ ≤ ∑ i, μ.real (bad i) := measureReal_iUnion_fintype_le _
      _ ≤ ∑ _i : ι, ε := Finset.sum_le_sum (fun i _ => hb i)
      _ = _ := by simp
  have heq : (⋂ i, good i) = (⋃ i, bad i)ᶜ := by
    ext x
    simp [bad]
  rw [heq]
  have hc := measureReal_compl (μ := μ) ((Set.to_countable (⋃ i, bad i)).measurableSet)
  rw [probReal_univ] at hc
  linarith
end StatisticalRL.OnlineRL
