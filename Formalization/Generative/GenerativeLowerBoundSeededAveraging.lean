import Formalization.Generative.GenerativeLowerBoundRandomSeed

/-! Choosing a single hard model after averaging over a common random seed. -/
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
namespace StatisticalRL.GenerativeLowerBound

/-- If every fixed seed has average model error at least c, and each decoder
error is included in its model's risk event, then one model has seeded risk at
least c. The model is selected after the seed has been averaged out. -/
theorem finiteSeed_averageTesting_to_oneRisk {I Ω Ξ : Type*}
    [Fintype I] [Nonempty I] [Fintype Ω] [Fintype Ξ]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    [MeasurableSpace Ξ] [MeasurableSingletonClass Ξ]
    (P : I → Measure Ω) [∀ i, IsProbabilityMeasure (P i)]
    (σ : Measure Ξ) [IsProbabilityMeasure σ]
    (D R : I → Set (Ω × Ξ)) (c : ℝ)
    (hsubset : ∀ i, D i ⊆ R i)
    (htest : ∀ r : Ξ, c ≤ (∑ i : I, (P i).real {x | (x,r) ∈ D i}) / Fintype.card I) :
    ∃ i : I, c ≤ (independentSeedLaw (P i) σ).real (R i) := by
  classical
  let w (r : Ξ) : ℝ := σ.real {r}
  let E (i : I) (r : Ξ) : ℝ := (P i).real {x | (x,r) ∈ D i}
  let T (i : I) (r : Ξ) : ℝ := (P i).real {x | (x,r) ∈ R i}
  have hw (r : Ξ) : 0 ≤ w r := measureReal_nonneg
  have hw1 : ∑ r, w r = 1 := by
    dsimp [w]
    rw [sum_measureReal_singleton, Finset.coe_univ, probReal_univ]
  have hcard : (0 : ℝ) < Fintype.card I := by exact_mod_cast Fintype.card_pos
  have hE (i : I) (r : Ξ) : E i r ≤ T i r := by
    apply measureReal_mono _ (measure_ne_top _ _)
    exact fun x hx ↦ hsubset i hx
  have hsum : c * Fintype.card I ≤ ∑ r, (∑ i, E i r) * w r := by
    have h := Finset.sum_le_sum (fun r (_ : r ∈ Finset.univ) ↦
      mul_le_mul_of_nonneg_right ((le_div_iff₀ hcard).1 (htest r)) (hw r))
    rw [← Finset.mul_sum, hw1, mul_one] at h
    exact h
  have hsum' : (∑ r, (∑ i, E i r) * w r) ≤ ∑ i, ∑ r, T i r * w r := by
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_le_sum (fun i _ ↦ Finset.sum_le_sum (fun r _ ↦
      mul_le_mul_of_nonneg_right (hE i r) (hw r)))
  by_contra hn
  push_neg at hn
  have hs : (∑ i, ∑ r, T i r * w r) < ∑ _i : I, c := by
    apply Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
    intro i _
    have h := hn i
    rw [independentSeedLaw_real_event] at h
    exact h
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hs
  nlinarith

end StatisticalRL.GenerativeLowerBound
