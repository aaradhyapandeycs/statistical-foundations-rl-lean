import Formalization.OfflineRL.FiniteVILCB.IdealData
import Formalization.OfflineRL.FiniteVILCB.CountEvents

/-!
# One product space for the analysis (gap G3) and conditioning on atoms (gap G2)

* the iid dataset law is the product law `Measure.pi`;
* the product over `Fin K` is the image of (aux block) ⊗ (main block) under `joinData`;
* the main block is the image of the tape law (Lemma T);
* hence every event of the data has the probability of its pull-back on
  `Ω_T = (aux trajectories) × (initial states × action tapes × next-state tapes)`;
* a set whose every section has mass `≤ ε` has mass `≤ ε` (finite atoms, then integrate).
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace StatisticalRL.FiniteVILCB

variable {S A : Type*} [Fintype S] [Fintype A]
set_option linter.unusedSectionVars false

noncomputable local instance glDecS : DecidableEq S := Classical.decEq S
noncomputable local instance glDecA : DecidableEq A := Classical.decEq A
local instance glMS : MeasurableSpace S := ⊤
local instance glMA : MeasurableSpace A := ⊤
local instance glMT (H : ℕ) : MeasurableSpace (Traj S A H) := ⊤

/-- Sections bound (atoms then integrate). -/
theorem prod_real_le_of_sections {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) [IsProbabilityMeasure μ] (ν : Measure β) [IsProbabilityMeasure ν]
    {B : Set (α × β)} (hB : MeasurableSet B) (ε : ℝ) (hε : 0 ≤ ε)
    (h : ∀ x, ν.real (Prod.mk x ⁻¹' B) ≤ ε) : (μ.prod ν).real B ≤ ε := by
  rw [measureReal_def, Measure.prod_apply hB]
  have hle : ∫⁻ x, ν (Prod.mk x ⁻¹' B) ∂μ ≤ ∫⁻ _, ENNReal.ofReal ε ∂μ := by
    refine lintegral_mono fun x ↦ ?_
    rw [← ENNReal.ofReal_toReal (measure_ne_top ν _)]
    exact ENNReal.ofReal_le_ofReal (h x)
  rw [lintegral_const, measure_univ, mul_one] at hle
  have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hle
  rwa [ENNReal.toReal_ofReal hε] at this

theorem prod_real_fst {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) [IsProbabilityMeasure μ] (ν : Measure β) [IsProbabilityMeasure ν]
    (A' : Set α) : (μ.prod ν).real {p | p.1 ∈ A'} = μ.real A' := by
  have : {p : α × β | p.1 ∈ A'} = A' ×ˢ Set.univ := by ext p; simp
  rw [this, measureReal_def, Measure.prod_prod, measure_univ, mul_one, measureReal_def]

theorem prod_real_snd {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) [IsProbabilityMeasure μ] (ν : Measure β) [IsProbabilityMeasure ν]
    (B' : Set β) : (μ.prod ν).real {p | p.2 ∈ B'} = ν.real B' := by
  have : {p : α × β | p.2 ∈ B'} = Set.univ ×ˢ B' := by ext p; simp
  rw [this, measureReal_def, Measure.prod_prod, measure_univ, one_mul, measureReal_def]

section Join

variable {H K : ℕ}

/-- The iid product on `Fin K` splits into the auxiliary and main blocks. -/
theorem pi_eq_map_join (ν : Measure (Traj S A H)) [IsProbabilityMeasure ν] :
    Measure.pi (fun _ : Fin K ↦ ν) =
      ((Measure.pi fun _ : Fin (K / 2) ↦ ν).prod (Measure.pi fun _ : Fin (K - K / 2) ↦ ν)).map
        (fun p ↦ joinData p.1 p.2) := by
  apply Measure.ext_of_singleton
  intro x
  rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton x)]
  have hpre : (fun p : (Fin (K / 2) → Traj S A H) × (Fin (K - K / 2) → Traj S A H) ↦
      joinData p.1 p.2) ⁻¹' {x} =
      {fun i : Fin (K / 2) ↦ x ⟨i.val, by omega⟩} ×ˢ {fun j ↦ x (mainIdx j)} := by
    ext ⟨a, m⟩
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_prod]
    constructor
    · rintro rfl
      exact ⟨funext fun i ↦ (joinData_aux a m i).symm, funext fun j ↦ (joinData_mainIdx a m j).symm⟩
    · rintro ⟨rfl, rfl⟩
      funext k
      simp only [joinData]
      split_ifs with hk
      · rfl
      · congr 1
        exact Fin.ext (by simp [mainIdx]; omega)
  rw [hpre, Measure.prod_prod, ← Set.univ_pi_singleton, Measure.pi_pi, ← Set.univ_pi_singleton,
    Measure.pi_pi, ← Set.univ_pi_singleton, Measure.pi_pi]
  -- split the product over `Fin K`
  let e : Fin (K / 2) ⊕ Fin (K - K / 2) ≃ Fin K := finSumFinEquiv.trans (finCongr (by omega))
  rw [← e.prod_comp, Fintype.prod_sum_type]
  rfl

end Join

end StatisticalRL.FiniteVILCB
