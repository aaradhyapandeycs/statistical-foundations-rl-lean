import Formalization.OfflineRL.OfflineCountChernoff
import Formalization.OfflineRL.StackProjection

/-!
# Count tails for coordinates of a product measure

The lower tail is `visitCount_lower_tail`; the upper tail applies the second part of
`lem:tail-bound-sum-Bernoulli` (`bernoulliTailBound_source`), with the case `p = 0` split off
(gap G1 of the plan check: the library tail needs `0 < p`). Both are then specialized to
coordinates of `Measure.pi` selected along an injective index map.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace StatisticalRL.FiniteVILCB

open StatisticalRL.OfflineRL

variable {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X] [DecidableEq X]

/-- Upper tail of a visitation count: `P(N_x > τ) ≤ 2 e^{-0.19 τ}` for `τ ≥ 2Np`, `τ ≥ 0`. -/
theorem visitCount_upper_tail
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ρ : Measure X) [IsProbabilityMeasure ρ] (N : ℕ) (Y : Fin N → Ω → X)
    (hYm : ∀ i, Measurable (Y i)) (hYind : iIndepFun Y μ)
    (hYlaw : ∀ i, HasLaw (Y i) ρ μ) (x : X) (τ : ℝ) (hτ0 : 0 ≤ τ)
    (hτ : 2 * ρ.real {x} * N ≤ τ) :
    μ.real {ω | τ < (visitCount Y x ω : ℝ)} ≤ 2 * Real.exp (-(0.19 : ℝ) * τ) := by
  set p := ρ.real {x} with hpdef
  have hcount : ∀ ω, (visitCount Y x ω : ℝ) = ∑ i, hitReal Y x i ω := by
    intro ω
    unfold visitCount hitReal
    push_cast
    rfl
  rcases eq_or_lt_of_le (measureReal_nonneg : 0 ≤ p) with hp0 | hp0
  · -- p = 0: each sample avoids x almost surely
    have hnull : ∀ i, μ (Y i ⁻¹' {x}) = 0 := by
      intro i
      rw [← Measure.map_apply (hYm i) (measurableSet_singleton x), (hYlaw i).map_eq]
      have : ρ.real {x} = 0 := hp0.symm
      rw [measureReal_eq_zero_iff] at this
      exact this
    have hsub : {ω | τ < (visitCount Y x ω : ℝ)} ⊆ ⋃ i, Y i ⁻¹' {x} := by
      intro ω hω
      simp only [Set.mem_setOf_eq] at hω
      by_contra hno
      simp only [Set.mem_iUnion, Set.mem_preimage, Set.mem_singleton_iff, not_exists] at hno
      have : visitCount Y x ω = 0 := by
        unfold visitCount
        simp [hno]
      rw [this] at hω
      norm_num at hω
      linarith
    have hzero : μ {ω | τ < (visitCount Y x ω : ℝ)} = 0 :=
      measure_mono_null hsub (measure_iUnion_null hnull)
    rw [measureReal_def, hzero, ENNReal.toReal_zero]
    positivity
  · have hp1 : p ≤ 1 := measureReal_le_one
    have hg := measurable_hitIndicator x
    have hZm : ∀ i, Measurable (hitReal Y x i) := fun i => hg.comp (hYm i)
    have hZi : iIndepFun (hitReal Y x) μ :=
      hYind.comp (fun _ y => if y = x then (1 : ℝ) else 0) (fun _ => hg)
    have hZlaw : ∀ i, HasLaw (hitReal Y x i)
        (StatisticalRL.Probability.bernoulliRealLaw p hp0.le hp1) μ := by
      intro i
      refine ⟨(hZm i).aemeasurable, ?_⟩
      have hcomp : hitReal Y x i = (fun y : X => if y = x then (1 : ℝ) else 0) ∘ Y i := rfl
      rw [hcomp, ← Measure.map_map hg (hYm i), (hYlaw i).map_eq]
      exact map_hitIndicator_eq_bernoulliRealLaw ρ x
    have h2 := (StatisticalRL.Probability.bernoulliTailBound_source Ω μ p hp0 hp1 N
      (hitReal Y x) hZm hZi hZlaw).2 τ (by linarith)
    have hset : {ω | τ < (visitCount Y x ω : ℝ)} = {ω | (∑ i : Fin N, hitReal Y x i ω) > τ} := by
      ext ω
      simp only [Set.mem_setOf_eq, hcount, gt_iff_lt]
    rw [hset]
    exact h2

variable {ι β : Type*} [Fintype ι] [MeasurableSpace β]

theorem pi_coords_iid (ν : ι → Measure β) [∀ i, IsProbabilityMeasure (ν i)] {N : ℕ}
    (g : Fin N → ι) (hg : Function.Injective g) (f : β → X) (hf : Measurable f)
    (law : Measure X) (hlaw : ∀ j, (ν (g j)).map f = law) :
    (∀ j, Measurable (fun ω : ι → β ↦ f (ω (g j)))) ∧
      iIndepFun (fun j (ω : ι → β) ↦ f (ω (g j))) (Measure.pi ν) ∧
      ∀ j, HasLaw (fun ω : ι → β ↦ f (ω (g j))) law (Measure.pi ν) := by
  refine ⟨fun j ↦ hf.comp (measurable_pi_apply (g j)), ?_, fun j ↦ ?_⟩
  · exact (OfflineRL.StackProjection.iIndepFun_comp_injective ν g hg).comp (fun _ ↦ f)
      (fun _ ↦ hf)
  · refine ⟨(hf.comp (measurable_pi_apply (g j))).aemeasurable, ?_⟩
    have : (fun ω : ι → β ↦ f (ω (g j))) = f ∘ (fun ω ↦ ω (g j)) := rfl
    rw [this, ← Measure.map_map hf (measurable_pi_apply (g j)),
      (measurePreserving_eval ν (g j)).map_eq, hlaw j]

/-- Lower tail for counts of selected coordinates of a product measure. -/
theorem pi_count_lower (ν : ι → Measure β) [∀ i, IsProbabilityMeasure (ν i)] {N : ℕ}
    (g : Fin N → ι) (hg : Function.Injective g) (f : β → X) (hf : Measurable f)
    (law : Measure X) [IsProbabilityMeasure law] (hlaw : ∀ j, (ν (g j)).map f = law) (x : X) :
    (Measure.pi ν).real {ω | (visitCount (fun j (ω : ι → β) ↦ f (ω (g j))) x ω : ℝ) <
      (N : ℝ) * law.real {x} / 2} ≤ Real.exp (-((N : ℝ) * law.real {x} / 8)) := by
  obtain ⟨hm, hi, hl⟩ := pi_coords_iid ν g hg f hf law hlaw
  exact visitCount_lower_tail (Measure.pi ν) law N _ hm hi hl x

/-- Upper tail for counts of selected coordinates of a product measure. -/
theorem pi_count_upper (ν : ι → Measure β) [∀ i, IsProbabilityMeasure (ν i)] {N : ℕ}
    (g : Fin N → ι) (hg : Function.Injective g) (f : β → X) (hf : Measurable f)
    (law : Measure X) [IsProbabilityMeasure law] (hlaw : ∀ j, (ν (g j)).map f = law) (x : X)
    (τ : ℝ) (hτ0 : 0 ≤ τ) (hτ : 2 * law.real {x} * N ≤ τ) :
    (Measure.pi ν).real {ω | τ < (visitCount (fun j (ω : ι → β) ↦ f (ω (g j))) x ω : ℝ)} ≤
      2 * Real.exp (-(0.19 : ℝ) * τ) := by
  obtain ⟨hm, hi, hl⟩ := pi_coords_iid ν g hg f hf law hlaw
  exact visitCount_upper_tail (Measure.pi ν) law N _ hm hi hl x τ hτ0 hτ

end StatisticalRL.FiniteVILCB
