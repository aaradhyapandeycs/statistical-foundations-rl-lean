import Mathlib
import Formalization.RobustRL.TVCostLevels
import Formalization.RobustRL.TVSortedCrossing
import Formalization.RobustRL.TVTieFill
import Formalization.RobustRL.TVEventBridge
import Formalization.RobustRL.TVTransfer
import Formalization.RobustRL.TVDisaggregation

/-! TV proof corrected state-carrier composition for the
robust-TV fractional-knapsack construction. The threshold fill is applied to
the finite state carrier, so its finite sums include the actual tied states.
The list-level bridge is intentionally not imported: its generic
`thresholdFill` dependency requires a `Fintype` on the cost carrier, which is
not available for `ℝ`. -/

open scoped BigOperators

namespace StatisticalRL.RobustRL.TVProof.Crossing

variable {State : Type*} [Fintype State] [DecidableEq State]

private noncomputable abbrev levelSet (p c : State → ℝ) : Finset ℝ :=
  StatisticalRL.RobustRL.TVProof.CostLevels.positiveCostLevels p c

private noncomputable abbrev levelMass (p c : State → ℝ) (lam : ℝ) : ℝ :=
  StatisticalRL.RobustRL.TVProof.CostLevels.costLevelMass p c lam

/-- The total nominal mass carried by strictly positive shifted costs, written
both as a sum over distinct represented levels and as a state-indexed sum.
This is the endpoint normalization identity needed when the TV radius reaches
the entire positive-cost mass. -/
theorem positiveLevelMass_eq_state_positiveCostMass
    (p c : State → ℝ) (hp : ∀ s, 0 ≤ p s) (hc : ∀ s, 0 ≤ c s) :
    (∑ lam ∈ (levelSet p c).filter (fun lam ↦ 0 < lam), levelMass p c lam) =
      ∑ s, if 0 < c s then p s else 0 := by
  classical
  let S := StatisticalRL.RobustRL.TVProof.CostLevels.positiveMassStates p
  let L := levelSet p c
  let Sp := S.filter (fun s ↦ 0 < c s)
  let Lp := L.filter (fun lam ↦ 0 < lam)
  have hmap : ∀ s ∈ Sp, c s ∈ Lp := by
    intro s hs
    have hsS : s ∈ S := (Finset.mem_filter.mp hs).1
    have hsc : 0 < c s := (Finset.mem_filter.mp hs).2
    simp only [Lp, Finset.mem_filter]
    exact ⟨Finset.mem_image.mpr ⟨s, hsS, rfl⟩, hsc⟩
  have hpartition :
      (∑ lam ∈ Lp, ∑ s ∈ Sp with c s = lam, p s) = ∑ s ∈ Sp, p s :=
    Finset.sum_fiberwise_of_maps_to hmap p
  have hfiber (lam : ℝ) (hlam : lam ∈ Lp) :
      (∑ s ∈ Sp with c s = lam, p s) = levelMass p c lam := by
    have hfilters : Sp.filter (fun s ↦ c s = lam) = S.filter (fun s ↦ c s = lam) := by
      ext s
      simp only [Sp, Finset.mem_filter]
      constructor
      · rintro ⟨⟨hsS, hsc⟩, heq⟩
        exact ⟨hsS, heq⟩
      · rintro ⟨hsS, heq⟩
        refine ⟨⟨hsS, ?_⟩, heq⟩
        rw [heq]
        exact (Finset.mem_filter.mp hlam).2
    simpa [levelMass, StatisticalRL.RobustRL.TVProof.CostLevels.costLevelMass,
      Sp, S, hfilters]
  have hfibered : (∑ lam ∈ Lp, levelMass p c lam) = ∑ s ∈ Sp, p s := by
    calc
      (∑ lam ∈ Lp, levelMass p c lam) =
          ∑ lam ∈ Lp, ∑ s ∈ Sp with c s = lam, p s := by
            apply Finset.sum_congr rfl
            intro lam hlam
            exact (hfiber lam hlam).symm
      _ = ∑ s ∈ Sp, p s := hpartition
  have hsupport : (∑ s ∈ Sp, p s) = ∑ s, if 0 < c s then p s else 0 := by
    have hinside : (∑ s ∈ Sp, (if 0 < c s then p s else 0)) =
        ∑ s ∈ Sp, p s := by
      apply Finset.sum_congr rfl
      intro s hs
      simp [Sp, (Finset.mem_filter.mp hs).2]
    rw [← hinside]
    apply Finset.sum_subset (by simp [Sp])
    intro s hs hnot
    by_cases hsc : 0 < c s
    · have hsS : s ∉ S := by
        intro hsin
        exact hnot (Finset.mem_filter.mpr ⟨hsin, hsc⟩)
      have hpzero : p s = 0 := by
        have : ¬ 0 < p s := by
          intro hppos
          exact hsS (by simp [S,
            StatisticalRL.RobustRL.TVProof.CostLevels.positiveMassStates,
            hppos])
        exact le_antisymm (le_of_not_gt this) (hp s)
      simp [hsc, hpzero]
    · simp [hsc]
  calc
    (∑ lam ∈ (levelSet p c).filter (fun lam ↦ 0 < lam), levelMass p c lam) =
        ∑ s ∈ Sp, p s := by simpa [L, Lp] using hfibered
    _ = ∑ s, if 0 < c s then p s else 0 := hsupport

/-- The positive-cost mass is at most one under probability normalization.
The premise is kept as the actual finite-state normalization equation. -/
theorem statePositiveCostMass_le_one
    (p c : State → ℝ) (hp : ∀ s, 0 ≤ p s) (hc : ∀ s, 0 ≤ c s)
    (hpSum : ∑ s, p s = 1) :
    (∑ s, if 0 < c s then p s else 0) ≤ 1 := by
  rw [← hpSum]
  apply Finset.sum_le_sum
  intro s hs
  split_ifs with h
  · exact le_rfl
  · exact hp s

/-- Full removal of positive-cost levels uses exactly the positive-cost mass;
zero-cost levels receive zero, even at the over-budget endpoint. -/
theorem fullPositiveCostAllocation_sum
    (p c : State → ℝ) (hp : ∀ s, 0 ≤ p s) (hc : ∀ s, 0 ≤ c s) :
    (∑ lam ∈ levelSet p c,
      StatisticalRL.RobustRL.TVProof.Disaggregation.fullPositiveCostAllocation
        p c lam) = ∑ s, if 0 < c s then p s else 0 := by
  classical
  let L := levelSet p c
  have hsplit :
      (∑ lam ∈ L,
        StatisticalRL.RobustRL.TVProof.Disaggregation.fullPositiveCostAllocation
          p c lam) =
      ∑ lam ∈ L.filter (fun lam ↦ 0 < lam), levelMass p c lam := by
    unfold StatisticalRL.RobustRL.TVProof.Disaggregation.fullPositiveCostAllocation
    simp [L, levelMass, Finset.sum_filter]
  calc
    (∑ lam ∈ levelSet p c,
      StatisticalRL.RobustRL.TVProof.Disaggregation.fullPositiveCostAllocation
        p c lam) = ∑ lam ∈ L.filter (fun lam ↦ 0 < lam), levelMass p c lam := hsplit
    _ = ∑ s, if 0 < c s then p s else 0 :=
      positiveLevelMass_eq_state_positiveCostMass p c hp hc

/-- The endpoint allocation is within radius whenever the radius covers all
positive-cost mass. This explicitly includes zero positive-cost mass and
`σ ≥ 1`; it does not use a threshold at level zero. -/
theorem fullPositiveCostAllocation_budget
    (p c : State → ℝ) (σ : ℝ) (hp : ∀ s, 0 ≤ p s)
    (hc : ∀ s, 0 ≤ c s) (hpSum : ∑ s, p s = 1)
    (hW : (∑ s, if 0 < c s then p s else 0) ≤ σ) :
    (∑ lam ∈ levelSet p c,
      StatisticalRL.RobustRL.TVProof.Disaggregation.fullPositiveCostAllocation
        p c lam) ≤ σ := by
  rw [fullPositiveCostAllocation_sum p c hp hc]
  exact hW

end StatisticalRL.RobustRL.TVProof.Crossing
