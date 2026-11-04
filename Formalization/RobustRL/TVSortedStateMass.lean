import Mathlib
import Formalization.RobustRL.TVCostLevels
import Formalization.RobustRL.TVSortedCrossing
import Formalization.RobustRL.TVTieFill

/-! TV proof state-mass bridge relating a sorted prefix
to state-indexed strict-above and tie masses. Later positivity and transfer
feasibility results are separate. -/

open scoped BigOperators

namespace StatisticalRL.RobustRL.TVProof.SortedState

variable {State : Type*} [Fintype State] [DecidableEq State]

private noncomputable abbrev support (p : State → ℝ) : Finset State :=
  StatisticalRL.RobustRL.TVProof.CostLevels.positiveMassStates p

private noncomputable abbrev levels (p c : State → ℝ) : Finset ℝ :=
  StatisticalRL.RobustRL.TVProof.CostLevels.positiveCostLevels p c

private noncomputable abbrev mass (p c : State → ℝ) (lam : ℝ) : ℝ :=
  StatisticalRL.RobustRL.TVProof.CostLevels.costLevelMass p c lam

/-- A supported cost fiber has the expected strict-above indicator. -/
theorem aboveMass_eq_levelAbove
    (p c : State → ℝ) (hp : ∀ s, 0 ≤ p s) (lam : ℝ) :
    StatisticalRL.RobustRL.TVProof.TieFill.aboveMass p c lam =
      ∑ μ ∈ levels p c, if lam < μ then mass p c μ else 0 := by
  classical
  let S := support p
  let L := levels p c
  have hsupport :
      (∑ s ∈ S, (if lam < c s then p s else 0)) =
        ∑ s, (if lam < c s then p s else 0) := by
    apply Finset.sum_subset (by simp [S])
    intro s hs hnot
    have hpzero : p s = 0 := by
      have hnotpos : ¬ 0 < p s := by
        intro hpPos
        exact hnot (by simp [S,
          StatisticalRL.RobustRL.TVProof.CostLevels.positiveMassStates,
          hpPos])
      exact le_antisymm (le_of_not_gt hnotpos) (hp s)
    simp [hpzero]
  have hpartition :
      (∑ μ ∈ L,
        ∑ s ∈ S with c s = μ, (if lam < c s then p s else 0)) =
        ∑ s ∈ S, (if lam < c s then p s else 0) := by
    exact Finset.sum_fiberwise_of_maps_to
      (fun s hs ↦ Finset.mem_image_of_mem c hs)
      (fun s ↦ if lam < c s then p s else 0)
  have hfiber (μ : ℝ) :
      (∑ s ∈ S with c s = μ, (if lam < c s then p s else 0)) =
        if lam < μ then mass p c μ else 0 := by
    calc
      (∑ s ∈ S with c s = μ, (if lam < c s then p s else 0)) =
          ∑ s ∈ S with c s = μ, if lam < μ then p s else 0 := by
        apply Finset.sum_congr rfl
        intro s hs
        simp [(Finset.mem_filter.mp hs).2]
      _ = if lam < μ then mass p c μ else 0 := by
        by_cases hμ : lam < μ <;>
          simp [S, support, mass, StatisticalRL.RobustRL.TVProof.CostLevels.costLevelMass,
            hμ]
  calc
    StatisticalRL.RobustRL.TVProof.TieFill.aboveMass p c lam =
        ∑ s, (if lam < c s then p s else 0) := rfl
    _ = ∑ s ∈ S, (if lam < c s then p s else 0) := hsupport.symm
    _ = ∑ μ ∈ L,
          ∑ s ∈ S with c s = μ, (if lam < c s then p s else 0) := hpartition.symm
    _ = ∑ μ ∈ L, if lam < μ then mass p c μ else 0 := by
      apply Finset.sum_congr rfl
      intro μ hμ
      exact hfiber μ

/-- On a represented cost level, the actual state tie mass is exactly its
aggregated nominal mass. -/
theorem tieMass_eq_levelMass_of_mem
    (p c : State → ℝ) (hp : ∀ s, 0 ≤ p s) {lam : ℝ}
    (hlam : lam ∈ levels p c) :
    StatisticalRL.RobustRL.TVProof.TieFill.tieMass p c lam = mass p c lam := by
  classical
  let S := support p
  have hsupport :
      (∑ s ∈ S, (if c s = lam then p s else 0)) =
        ∑ s, (if c s = lam then p s else 0) := by
    apply Finset.sum_subset (by simp [S])
    intro s hs hnot
    have hpzero : p s = 0 := by
      have hnotpos : ¬ 0 < p s := by
        intro hpPos
        exact hnot (by simp [S,
          StatisticalRL.RobustRL.TVProof.CostLevels.positiveMassStates,
          hpPos])
      exact le_antisymm (le_of_not_gt hnotpos) (hp s)
    simp [hpzero]
  calc
    StatisticalRL.RobustRL.TVProof.TieFill.tieMass p c lam =
        ∑ s, (if c s = lam then p s else 0) := rfl
    _ = ∑ s ∈ S, (if c s = lam then p s else 0) := hsupport.symm
    _ = ∑ s ∈ S.filter (fun s ↦ c s = lam), p s := by
      simp [Finset.sum_filter]
    _ = mass p c lam := by
      simp [S, support, mass, StatisticalRL.RobustRL.TVProof.CostLevels.costLevelMass]

private theorem list_sum_map_eq_finset_sum_of_nodup
    (l : List ℝ) (f : ℝ → ℝ) (hl : l.Nodup) :
    (l.map f).sum = ∑ x ∈ l.toFinset, f x := by
  calc
    (l.map f).sum = (l.toFinset.toList.map f).sum := by
      exact (List.toFinset_toList hl).symm.map f |>.sum_eq
    _ = ∑ x ∈ l.toFinset, f x := by
      simpa using l.toFinset.sum_map_toList f

/-- The sorted prefix is exactly the state mass strictly above its crossing
level, while the crossing tie is exactly one aggregated level mass. This is
the concrete list-to-state bridge needed by the finite-state threshold fill. -/
theorem sortedPrefix_stateAbove_and_tie
    (p c : State → ℝ) (hp : ∀ s, 0 ≤ p s)
    (pre post : List ℝ) (lam : ℝ)
    (hdecomp :
      StatisticalRL.RobustRL.TVProof.SortedCrossing.sortedPositiveCostLevels
        p c = pre ++ lam :: post)
    (hpre : ∀ μ ∈ pre, lam < μ)
    (hpost : ∀ μ ∈ post, μ < lam) :
    StatisticalRL.RobustRL.TVProof.TieFill.aboveMass p c lam =
        (pre.map (mass p c)).sum ∧
      StatisticalRL.RobustRL.TVProof.TieFill.tieMass p c lam = mass p c lam := by
  classical
  let L := levels p c
  have hL :
      (StatisticalRL.RobustRL.TVProof.SortedCrossing.sortedPositiveCostLevels
        p c).toFinset = L := by
    exact StatisticalRL.RobustRL.TVProof.SortedCrossing.sortedPositiveCostLevels_toFinset p c
  have hfiltered : L.filter (fun μ ↦ lam < μ) = pre.toFinset := by
    rw [← hL, hdecomp]
    ext μ
    simp only [Finset.mem_filter, List.mem_toFinset]
    constructor
    · rintro ⟨hmem, hgt⟩
      simp only [List.mem_append, List.mem_cons] at hmem
      rcases hmem with hpreMem | hrest
      · exact hpreMem
      · rcases hrest with heq | hpostMem
        · exact False.elim ((lt_irrefl lam) (heq ▸ hgt))
        · exact False.elim ((not_lt_of_ge (le_of_lt (hpost μ hpostMem))) hgt)
    · intro hmem
      exact ⟨by simp [hmem], hpre μ hmem⟩
  have hsortedNodup :
      (StatisticalRL.RobustRL.TVProof.SortedCrossing.sortedPositiveCostLevels
        p c).Nodup := by
    simp [StatisticalRL.RobustRL.TVProof.SortedCrossing.sortedPositiveCostLevels]
  have hpreNodup : pre.Nodup := by
    rw [hdecomp] at hsortedNodup
    exact (List.nodup_append.mp hsortedNodup).1
  have habove := aboveMass_eq_levelAbove p c hp lam
  have haboveFiltered :
      (∑ μ ∈ L, if lam < μ then mass p c μ else 0) =
        ∑ μ ∈ L.filter (fun μ ↦ lam < μ), mass p c μ := by
    simp [Finset.sum_filter]
  have habovePre :
      (∑ μ ∈ L.filter (fun μ ↦ lam < μ), mass p c μ) =
        (pre.map (mass p c)).sum := by
    rw [hfiltered]
    exact (list_sum_map_eq_finset_sum_of_nodup pre (mass p c) hpreNodup).symm
  have hlammem : lam ∈ L := by
    rw [← hL, hdecomp]
    simp
  exact ⟨by rw [habove, haboveFiltered, habovePre],
    tieMass_eq_levelMass_of_mem p c hp hlammem⟩


end StatisticalRL.RobustRL.TVProof.SortedState
