import Formalization.OfflineRL.SampleSplitCorrectedStatement
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.HasLaw

open MeasureTheory ProbabilityTheory

namespace StatisticalRL
namespace OfflineRL

private theorem singleton_real_mass_sum
    {X : Type*} [Fintype X] [MeasurableSpace X] [MeasurableSingletonClass X]
    (d : Measure X) [IsProbabilityMeasure d] :
    ∑ x : X, d.real {x} = 1 := by
  classical
  have hdisj : Pairwise (fun x y : X => Disjoint ({x} : Set X) ({y} : Set X)) := by
    intro x y hxy
    exact Set.disjoint_singleton.mpr hxy
  have hmeas : ∀ x : X, MeasurableSet ({x} : Set X) :=
    fun x => measurableSet_singleton x
  have hUnion : (⋃ x : X, ({x} : Set X)) = Set.univ := by
    ext x
    simp
  calc
    ∑ x : X, d.real {x} = d.real (⋃ x : X, ({x} : Set X)) :=
      (measureReal_iUnion_fintype hdisj hmeas).symm
    _ = 1 := by rw [hUnion]; simp

/-- Proof of the restricted sample-splitting statement for `N ≥ 2`. The parent
sample-size regime implies this endpoint condition. -/
theorem sampleSplit_count_lower_corrected_holds :
    sampleSplit_count_lower_corrected := by
  intro State Action _ _ _ _ _ _ d hd N hN δ hδ hδ1
  classical
  let X := State × Action
  let μ : Measure (Fin N → X) := Measure.pi (fun _ : Fin N => d)
  let Y : Fin N → (Fin N → State × Action) → State × Action := fun i ω => ω i
  let S : ℝ := Fintype.card State
  let L : ℝ := Real.log (S * (N : ℝ) / δ)
  let Good : Set (Fin N → X) := sampleSplitCountLowerEvent d N δ
  let Heavy : Finset X := Finset.univ.filter fun sa =>
    8 * L ≤ (N : ℝ) * d.real {sa}
  let CountBad : X → Set (Fin N → X) := fun sa =>
    {ω | (visitCount Y sa ω : ℝ) < (N : ℝ) * d.real {sa} / 2}
  let Bad := Goodᶜ
  letI : IsProbabilityMeasure μ := by infer_instance
  have hNreal : (0 : ℝ) < (N : ℝ) := by
    have h : 0 < N := lt_of_lt_of_le (by decide) hN
    exact_mod_cast h
  have hSpos : 1 ≤ S := by
    dsimp [S]
    exact_mod_cast Fintype.card_pos_iff.mpr ‹Nonempty State›
  have hratio2 : 2 < S * (N : ℝ) / δ := by
    apply (lt_div_iff₀ hδ).2
    dsimp [S]
    have hSN : 2 ≤ (Fintype.card State : ℝ) * (N : ℝ) := by
      have hs : 1 ≤ (Fintype.card State : ℝ) := by
        exact_mod_cast Fintype.card_pos_iff.mpr ‹Nonempty State›
      have hN2 : 2 ≤ (N : ℝ) := by exact_mod_cast hN
      nlinarith [mul_le_mul_of_nonneg_right hs (show (0 : ℝ) ≤ N by positivity), hN2]
    nlinarith [hδ1]
  have hL2 : Real.log 2 ≤ L := by
    apply Real.log_le_log (by norm_num) (le_of_lt hratio2)
  have hhalf : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (x := (2 : ℝ)) (by norm_num)
    norm_num at h ⊢
    exact h
  have hLpos : 0 < L := by linarith
  have hSLlarge : 1 < 8 * S * L := by
    have hS : 0 < S := lt_of_lt_of_le (by norm_num) hSpos
    nlinarith
  have hsingleton : ∑ sa : X, d.real {sa} = 1 := singleton_real_mass_sum d
  have hHeavyMass : (Heavy.card : ℝ) * (8 * L / (N : ℝ)) ≤ 1 := by
    have hMass : ∑ sa ∈ Heavy, d.real {sa} ≤ 1 := by
      calc
        ∑ sa ∈ Heavy, d.real {sa} ≤ ∑ sa : X, d.real {sa} :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ Heavy)
            (fun sa _ _ => measureReal_nonneg)
        _ = 1 := hsingleton
    calc
      (Heavy.card : ℝ) * (8 * L / (N : ℝ)) =
          ∑ sa ∈ Heavy, (8 * L / (N : ℝ)) := by simp [mul_comm]
      _ ≤ ∑ sa ∈ Heavy, d.real {sa} := by
        apply Finset.sum_le_sum
        intro sa hsa
        have hmem := (Finset.mem_filter.mp hsa).2
        exact (div_le_iff₀ hNreal).2 (by nlinarith [hmem])
      _ ≤ 1 := hMass
  have hHeavyCard : (Heavy.card : ℝ) ≤ (N : ℝ) / (8 * L) := by
    have h8L : 0 < 8 * L := by positivity
    have hmul : (Heavy.card : ℝ) * (8 * L) ≤ (N : ℝ) := by
      have hm := mul_le_mul_of_nonneg_right hHeavyMass (le_of_lt hNreal)
      field_simp at hm
      nlinarith
    exact (le_div_iff₀ h8L).2 (by nlinarith [hmul])
  have hYmeas : ∀ i, Measurable (Y i) := fun i => measurable_pi_apply i
  have hYind : iIndepFun Y μ := by
    dsimp [Y, μ]
    exact iIndepFun_pi (μ := fun _ : Fin N => d) (X := fun _ : Fin N => id)
      (fun _ => measurable_id.aemeasurable)
  have hYlaw : ∀ i, HasLaw (Y i) d μ := by
    intro i
    dsimp [Y, μ]
    exact (MeasureTheory.measurePreserving_eval (μ := fun _ : Fin N => d) i).hasLaw
  have htail (sa : X) : μ.real (CountBad sa) ≤
      Real.exp (-((N : ℝ) * d.real {sa} / 8)) := by
    dsimp [CountBad, Y, μ]
    exact visitCount_lower_tail
      (Measure.pi (fun _ : Fin N => d)) d N (fun i ω => ω i)
      (fun i => measurable_pi_apply i)
      (by
        exact iIndepFun_pi (μ := fun _ : Fin N => d) (X := fun _ : Fin N => id)
          (fun _ => measurable_id.aemeasurable))
      (fun i : Fin N => (MeasureTheory.measurePreserving_eval (μ := fun _ : Fin N => d) i).hasLaw) sa
  have htailHeavy (sa : X) (hsa : sa ∈ Heavy) :
      μ.real (CountBad sa) ≤ δ / (S * (N : ℝ)) := by
    have hlarge := (Finset.mem_filter.mp hsa).2
    calc
      μ.real (CountBad sa) ≤ Real.exp (-((N : ℝ) * d.real {sa} / 8)) := htail sa
      _ ≤ Real.exp (-L) := Real.exp_le_exp.mpr (by linarith)
      _ = δ / (S * (N : ℝ)) := by
        dsimp [L]
        rw [Real.exp_neg, Real.exp_log (by positivity)]
        field_simp
  have hBadSubset : Bad ⊆ ⋃ sa ∈ Heavy, CountBad sa := by
    intro ω hω
    have hnot : ¬ ∀ sa : X,
        max (visitCount Y sa ω : ℝ) ((2 / 3 : ℝ) * L) ≥
          (N : ℝ) * d.real {sa} / 12 := by
      simpa only [Bad, Good, sampleSplitCountLowerEvent, Set.mem_compl_iff,
        Set.mem_setOf_eq, Y, S, L] using hω
    push_neg at hnot
    obtain ⟨sa, hsa⟩ := hnot
    have hmax : max (visitCount Y sa ω : ℝ) ((2 / 3 : ℝ) * L) <
        (N : ℝ) * d.real {sa} / 12 := hsa
    have hparts := (max_lt_iff).mp hmax
    have hheavy : sa ∈ Heavy := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      dsimp [L]
      linarith [hparts.2]
    have hcount : ω ∈ CountBad sa := by
      change (visitCount Y sa ω : ℝ) < (N : ℝ) * d.real {sa} / 2
      have hp : 0 ≤ d.real {sa} := measureReal_nonneg
      linarith [hparts.1, hparts.2, hp]
    exact Set.mem_iUnion.2 ⟨sa, Set.mem_iUnion.2 ⟨hheavy, hcount⟩⟩
  have hBad : μ.real Bad < δ := by
    calc
      μ.real Bad ≤ μ.real (⋃ sa ∈ Heavy, CountBad sa) :=
        measureReal_mono hBadSubset (measure_ne_top μ _)
      _ ≤ ∑ sa ∈ Heavy, μ.real (CountBad sa) := by
        simpa using (measureReal_biUnion_finset_le (μ := μ) Heavy CountBad)
      _ ≤ ∑ sa ∈ Heavy, δ / (S * (N : ℝ)) := by
        apply Finset.sum_le_sum
        intro sa hsa
        exact htailHeavy sa hsa
      _ = (Heavy.card : ℝ) * (δ / (S * (N : ℝ))) := by simp [mul_comm]
      _ ≤ δ / (8 * S * L) := by
        have hpositive : 0 ≤ δ / (S * (N : ℝ)) := by positivity
        calc
          (Heavy.card : ℝ) * (δ / (S * (N : ℝ))) ≤
              ((N : ℝ) / (8 * L)) * (δ / (S * (N : ℝ))) :=
            mul_le_mul_of_nonneg_right hHeavyCard hpositive
          _ = δ / (8 * S * L) := by field_simp
      _ < δ := by
        rw [div_lt_iff₀ (by positivity)]
        nlinarith [hSLlarge, hδ]
  have hGoodMeas : MeasurableSet Good := by
    apply Set.Finite.measurableSet
    exact Set.finite_univ.subset (Set.subset_univ Good)
  have hcompl : μ.real Bad = 1 - μ.real Good := by
    dsimp [Bad, μ]
    rw [measureReal_compl hGoodMeas]
    simp
  rw [hcompl] at hBad
  linarith

end OfflineRL
end StatisticalRL
