import Formalization.ModelFree.AsyncQ.Arith
import Formalization.Probability.FiniteMarkov.Mixing
import Mathlib.MeasureTheory.Measure.Real

/-! # Preparations for the main assembly of Theorem 4.12

* `prob_biInter_ge`, `prob_inter_ge`: finite union bounds in "good event" form;
* `budget_hyps`: the printed budget gives the two inequalities of `ArithHyp`;
* `T_ge_two_of_card`: with `SA ≥ 2` the budget excludes `T = 1` (the weakest correction). -/

open MeasureTheory
open scoped BigOperators
open Finset

namespace StatisticalRL.AsyncQ

theorem prob_biInter_ge {Ω ι : Type*} [MeasurableSpace Ω] [DiscreteMeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (s : Finset ι) (G : ι → Set Ω) (d : ι → ℝ)
    (h : ∀ i ∈ s, 1 - d i ≤ μ.real (G i)) : 1 - ∑ i ∈ s, d i ≤ μ.real (⋂ i ∈ s, G i) := by
  have hc : (⋂ i ∈ s, G i)ᶜ = ⋃ i ∈ s, (G i)ᶜ := by simp [Set.compl_iInter]
  have h1 := measureReal_compl (μ := μ) (MeasurableSet.of_discrete (s := ⋂ i ∈ s, G i))
  rw [hc, probReal_univ] at h1
  have h2 := measureReal_biUnion_finset_le (μ := μ) s (fun i ↦ (G i)ᶜ)
  have h3 : ∀ i ∈ s, μ.real (G i)ᶜ ≤ d i := fun i hi ↦ by
    rw [measureReal_compl (MeasurableSet.of_discrete), probReal_univ]; linarith [h i hi]
  have h4 := sum_le_sum h3
  linarith

theorem prob_inter_ge {Ω : Type*} [MeasurableSpace Ω] [DiscreteMeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {A B : Set Ω} {a b : ℝ} (hA : 1 - a ≤ μ.real A)
    (hB : 1 - b ≤ μ.real B) : 1 - (a + b) ≤ μ.real (A ∩ B) := by
  have h1 := measureReal_compl (μ := μ) (MeasurableSet.of_discrete (s := A ∩ B))
  have hA' := measureReal_compl (μ := μ) (MeasurableSet.of_discrete (s := A))
  have hB' := measureReal_compl (μ := μ) (MeasurableSet.of_discrete (s := B))
  rw [Set.compl_inter, probReal_univ] at h1
  rw [probReal_univ] at hA' hB'
  have := measureReal_union_le (μ := μ) Aᶜ Bᶜ
  linarith

theorem budget_hyps {c₂ ι P γ ε μm T tmixr : ℝ} (hγ : 1 / 2 ≤ γ) (hγ1 : γ < 1) (hμ : 0 < μm)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hc₂ : 0 ≤ c₂) (hP : Real.log 2 ≤ P) (ht0 : 0 ≤ tmixr)
    (hbud : c₂ * ι ^ 2 / μm * max (P ^ 3 / ((1 - γ) ^ 4 * ε ^ 2)) (tmixr / (1 - γ)) ≤ T) :
    c₂ * ι ^ 2 * (1 / (1 - γ)) ^ 4 * P ^ 3 / ε ^ 2 ≤ T * μm ∧
    c₂ * ι ^ 2 * (1 / (1 - γ)) * max tmixr 1 ≤ T * μm := by
  set h := 1 / (1 - γ) with hh
  have h1γ : 0 < 1 - γ := by linarith
  have hh2 : 2 ≤ h := by rw [hh, le_div_iff₀ h1γ]; linarith
  set X := c₂ * ι ^ 2 / μm with hX
  have hX0 : 0 ≤ X := by positivity
  have hl2 := Real.log_two_gt_d9
  have hP0 : 0 < P := by linarith
  have e1 : P ^ 3 / ((1 - γ) ^ 4 * ε ^ 2) = h ^ 4 * P ^ 3 / ε ^ 2 := by
    rw [hh]; field_simp
  have e2 : tmixr / (1 - γ) = tmixr * h := by rw [hh]; field_simp
  rw [e1, e2] at hbud
  have hA : X * (h ^ 4 * P ^ 3 / ε ^ 2) ≤ T :=
    (mul_le_mul_of_nonneg_left (le_max_left _ _) hX0).trans hbud
  have hA' : c₂ * ι ^ 2 * h ^ 4 * P ^ 3 / ε ^ 2 ≤ T * μm := by
    have : c₂ * ι ^ 2 * h ^ 4 * P ^ 3 / ε ^ 2 = X * (h ^ 4 * P ^ 3 / ε ^ 2) * μm := by
      rw [hX]; field_simp
    rw [this]; exact mul_le_mul_of_nonneg_right hA hμ.le
  refine ⟨hA', ?_⟩
  rcases le_total 1 tmixr with ht | ht
  · rw [max_eq_left ht]
    have hB : X * (tmixr * h) ≤ T :=
      (mul_le_mul_of_nonneg_left (le_max_right _ _) hX0).trans hbud
    have : c₂ * ι ^ 2 * h * tmixr = X * (tmixr * h) * μm := by rw [hX]; field_simp
    rw [this]; exact mul_le_mul_of_nonneg_right hB hμ.le
  · rw [max_eq_right ht, mul_one]
    refine le_trans ?_ hA'
    have hP3 : 1 ≤ h ^ 3 * P ^ 3 := by
      have : 1 ≤ h * P := by nlinarith
      calc (1 : ℝ) = 1 ^ 3 := by norm_num
        _ ≤ (h * P) ^ 3 := pow_le_pow_left₀ (by norm_num) this 3
        _ = h ^ 3 * P ^ 3 := by ring
    have hε2 : 0 < ε ^ 2 := by positivity
    have hε21 : ε ^ 2 ≤ 1 := by nlinarith
    rw [le_div_iff₀ hε2]
    have hY : 0 ≤ c₂ * ι ^ 2 * h := by positivity
    have : c₂ * ι ^ 2 * h * ε ^ 2 ≤ c₂ * ι ^ 2 * h * (h ^ 3 * P ^ 3) := by
      apply mul_le_mul_of_nonneg_left _ hY; linarith
    nlinarith

/-- With at least two state–action pairs, `T = 1` violates the budget. -/
theorem budget_excludes_one {c₂ SA γ ε δ μm tmixr : ℝ} (hc₂ : 1 ≤ c₂) (hSA : 2 ≤ SA)
    (hγ : 1 / 2 ≤ γ) (hγ1 : γ < 1) (hδ : 0 < δ) (hδ1 : δ < 1) (hμ : 0 < μm) (hμ2 : μm ≤ 1 / 2)
    (ht : 1 ≤ tmixr) :
    ¬ (c₂ * Real.log (SA * 1 / δ) ^ 2 / μm *
        max (Real.log 1 ^ 3 / ((1 - γ) ^ 4 * ε ^ 2)) (tmixr / (1 - γ)) ≤ 1) := by
  intro hb
  have hl2 := Real.log_two_gt_d9
  have hι : Real.log 2 ≤ Real.log (SA * 1 / δ) := by
    apply Real.log_le_log (by norm_num)
    rw [le_div_iff₀ hδ]; nlinarith
  have hι2 : (0.48 : ℝ) ≤ Real.log (SA * 1 / δ) ^ 2 := by nlinarith
  have h1γ : 0 < 1 - γ := by linarith
  have hm : 2 ≤ max (Real.log 1 ^ 3 / ((1 - γ) ^ 4 * ε ^ 2)) (tmixr / (1 - γ)) := by
    refine le_trans ?_ (le_max_right _ _)
    rw [le_div_iff₀ h1γ]; nlinarith
  have hX : 2 * 0.48 ≤ c₂ * Real.log (SA * 1 / δ) ^ 2 / μm := by
    rw [le_div_iff₀ hμ]; nlinarith
  have : 2 * 0.48 * 2 ≤ c₂ * Real.log (SA * 1 / δ) ^ 2 / μm *
      max (Real.log 1 ^ 3 / ((1 - γ) ^ 4 * ε ^ 2)) (tmixr / (1 - γ)) := by
    apply mul_le_mul hX hm (by norm_num) (by linarith)
  have e : (2 : ℝ) * 0.48 * 2 = 1.92 := by norm_num
  linarith

end StatisticalRL.AsyncQ
