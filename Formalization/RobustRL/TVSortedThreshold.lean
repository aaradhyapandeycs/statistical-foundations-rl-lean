import Formalization.RobustRL.TVSortedStateMass
import Formalization.RobustRL.TVCrossingComposition

/-! TV proof: positive sorted crossing for the intermediate TV radius. -/
open scoped BigOperators
namespace StatisticalRL.RobustRL.TVProof.SortedState
variable {State : Type*} [Fintype State] [DecidableEq State]
private noncomputable abbrev mass (p c : State → ℝ) (lam : ℝ) : ℝ :=
  StatisticalRL.RobustRL.TVProof.CostLevels.costLevelMass p c lam

private theorem list_sum_map_eq_finset_sum_of_nodup
    (l : List ℝ) (f : ℝ → ℝ) (hl : l.Nodup) :
    (l.map f).sum = ∑ x ∈ l.toFinset, f x := by
  calc
    (l.map f).sum = (l.toFinset.toList.map f).sum := by
      exact (List.toFinset_toList hl).symm.map f |>.sum_eq
    _ = ∑ x ∈ l.toFinset, f x := by
      simpa using l.toFinset.sum_map_toList f

/-- A sorted prefix crossing below the total positive-cost mass is strictly
positive. In particular, the intermediate-capacity case never consumes the
zero-cost anchor as a crossing tie. -/
theorem crossing_threshold_positive
    (p c : State → ℝ) (σ : ℝ)
    (hp : ∀ s, 0 ≤ p s) (hc : ∀ s, 0 ≤ c s)
    (hσ : 0 < σ)
    (hσW : σ < ∑ s, if 0 < c s then p s else 0)
    (hσtotal : σ ≤ ∑ s, p s) :
    ∃ pre lam post,
      StatisticalRL.RobustRL.TVProof.SortedCrossing.sortedPositiveCostLevels
        p c = pre ++ lam :: post ∧
      (pre.map (mass p c)).sum < σ ∧
      σ ≤ (pre.map (mass p c)).sum + mass p c lam ∧
      (∀ μ ∈ pre, lam < μ) ∧ (∀ μ ∈ post, μ < lam) ∧ 0 < lam := by
  obtain ⟨pre, lam, post, hdecomp, hprefix, hcross, hpre, hpost⟩ :=
    StatisticalRL.RobustRL.TVProof.SortedCrossing.sorted_level_prefix_crossing
      p c σ hp hσ hσtotal
  have hlamlist : lam ∈
      StatisticalRL.RobustRL.TVProof.SortedCrossing.sortedPositiveCostLevels p c := by
    rw [hdecomp]
    simp
  have hlamlevel : lam ∈
      StatisticalRL.RobustRL.TVProof.CostLevels.positiveCostLevels p c := by
    rw [← StatisticalRL.RobustRL.TVProof.SortedCrossing.sortedPositiveCostLevels_toFinset p c]
    exact List.mem_toFinset.mpr hlamlist
  have hlamnonneg : 0 ≤ lam := by
    obtain ⟨s, hs, hcs⟩ := Finset.mem_image.mp hlamlevel
    rw [← hcs]
    exact hc s
  have hlampos : 0 < lam := by
    by_contra hnot
    have hlamzero : lam = 0 := le_antisymm (le_of_not_gt hnot) hlamnonneg
    have hpostEmpty : post = [] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro μ hμ
      have hμlevel : μ ∈
          StatisticalRL.RobustRL.TVProof.CostLevels.positiveCostLevels p c := by
        rw [← StatisticalRL.RobustRL.TVProof.SortedCrossing.sortedPositiveCostLevels_toFinset p c, hdecomp]
        simp [hμ]
      obtain ⟨s, hs, hcs⟩ := Finset.mem_image.mp hμlevel
      have hμnonneg : 0 ≤ μ := by rw [← hcs]; exact hc s
      have hμlt : μ < 0 := by simpa [hlamzero] using hpost μ hμ
      exact (not_lt_of_ge hμnonneg) hμlt
    have hpositiveLevelsInPre :
        (StatisticalRL.RobustRL.TVProof.CostLevels.positiveCostLevels
          p c).filter (fun μ ↦ 0 < μ) = pre.toFinset := by
      rw [← StatisticalRL.RobustRL.TVProof.SortedCrossing.sortedPositiveCostLevels_toFinset p c, hdecomp, hpostEmpty, hlamzero]
      ext μ
      simp only [Finset.mem_filter, List.mem_toFinset, List.mem_append,
        List.mem_cons, List.not_mem_nil, or_false]
      constructor
      · rintro ⟨hmem, hpos⟩
        rcases hmem with hpreMem | heq
        · exact hpreMem
        · exact False.elim (lt_irrefl 0 (heq ▸ hpos))
      · intro hmem
        exact ⟨Or.inl hmem, by simpa [hlamzero] using hpre μ hmem⟩
    have hmassPre :
        (pre.map (mass p c)).sum =
          ∑ μ ∈ (StatisticalRL.RobustRL.TVProof.CostLevels.positiveCostLevels p c).filter (fun μ ↦ 0 < μ), mass p c μ := by
      rw [hpositiveLevelsInPre]
      have hnodup : pre.Nodup := by
        have hsNodup :
            (StatisticalRL.RobustRL.TVProof.SortedCrossing.sortedPositiveCostLevels p c).Nodup := by
          simp [StatisticalRL.RobustRL.TVProof.SortedCrossing.sortedPositiveCostLevels]
        rw [hdecomp] at hsNodup
        exact (List.nodup_append.mp hsNodup).1
      exact list_sum_map_eq_finset_sum_of_nodup pre (mass p c) hnodup
    have hW :
        (∑ μ ∈ (StatisticalRL.RobustRL.TVProof.CostLevels.positiveCostLevels p c).filter (fun μ ↦ 0 < μ), mass p c μ) =
          ∑ s, if 0 < c s then p s else 0 := by
      exact StatisticalRL.RobustRL.TVProof.Crossing.positiveLevelMass_eq_state_positiveCostMass p c hp hc
    have : (∑ s, if 0 < c s then p s else 0) < σ := by
      rw [← hW, ← hmassPre]
      exact hprefix
    exact (not_lt_of_ge (le_of_lt hσW)) this
  refine ⟨pre, lam, post, hdecomp, hprefix, hcross, hpre, hpost, hlampos⟩


end StatisticalRL.RobustRL.TVProof.SortedState
