import Mathlib

/-! TV proof finite aggregation bridge for robust-TV
fractional knapsack. It partitions strictly positive probability mass by the
finite image of the cost function. Tied states share one cost level; zero-mass
states are omitted from the level carrier and contribute zero to both source
sums. -/

open scoped BigOperators

namespace StatisticalRL.RobustRL.TVProof.CostLevels

variable {State : Type*} [Fintype State] [DecidableEq State]

/-- States carrying strictly positive probability mass. -/
noncomputable def positiveMassStates (p : State → ℝ) : Finset State := by
  classical
  exact Finset.univ.filter fun s ↦ 0 < p s

/-- Distinct cost values represented among positive-mass states. This is an
image finset, so equal costs are aggregated and each distinct level occurs
once. -/
noncomputable def positiveCostLevels (p c : State → ℝ) : Finset ℝ := by
  classical
  exact (positiveMassStates p).image c

/-- Probability mass of one cost level, summing over its full state fiber. -/
noncomputable def costLevelMass (p c : State → ℝ) (lam : ℝ) : ℝ := by
  classical
  exact ∑ s ∈ positiveMassStates p with c s = lam, p s

/-- Cost-weighted mass of one level. -/
noncomputable def costLevelPayoff (p c : State → ℝ) (lam : ℝ) : ℝ := by
  classical
  exact ∑ s ∈ positiveMassStates p with c s = lam, p s * c s

/-- The positive-mass level carrier is exhaustive for all state probability
mass when `p` is nonnegative. -/
theorem sum_costLevelMass_eq_sum
    (p c : State → ℝ) (hp : ∀ s, 0 ≤ p s) :
    (∑ lam ∈ positiveCostLevels p c, costLevelMass p c lam) = ∑ s, p s := by
  classical
  have hpartition :
      (∑ lam ∈ positiveCostLevels p c,
        ∑ s ∈ positiveMassStates p with c s = lam, p s) =
        ∑ s ∈ positiveMassStates p, p s := by
    exact Finset.sum_fiberwise_of_maps_to
      (fun s hs ↦ Finset.mem_image_of_mem c hs) p
  have hsupport :
      (∑ s ∈ positiveMassStates p, p s) = ∑ s, p s := by
    apply Finset.sum_subset (by simp [positiveMassStates])
    intro s hs hnot
    have hnotpos : ¬ 0 < p s := by
      intro h
      exact hnot (by simp [positiveMassStates, h])
    have hzero : p s = 0 := le_antisymm (le_of_not_gt hnotpos) (hp s)
    exact hzero
  simpa [positiveCostLevels, costLevelMass] using hpartition.trans hsupport

/-- The payoff within a cost fiber is its cost times aggregated probability
mass, including fibers with any number of tied states. -/
theorem costLevelPayoff_eq_cost_mul_mass
    (p c : State → ℝ) (lam : ℝ) :
    costLevelPayoff p c lam = lam * costLevelMass p c lam := by
  classical
  unfold costLevelPayoff costLevelMass
  calc
    (∑ s ∈ positiveMassStates p with c s = lam, p s * c s) =
        ∑ s ∈ positiveMassStates p with c s = lam, lam * p s := by
      apply Finset.sum_congr rfl
      intro s hs
      have hcs : c s = lam := (Finset.mem_filter.mp hs).2
      rw [hcs]
      ring
    _ = lam * (∑ s ∈ positiveMassStates p with c s = lam, p s) := by
      rw [Finset.mul_sum]

/-- Every represented level has strictly positive aggregated mass. The image
carrier therefore contains exactly the represented cost fibers of the positive
support, including a possible zero-cost level; tied states contribute together. -/
theorem costLevelMass_pos_of_mem
    (p c : State → ℝ) (hp : ∀ s, 0 ≤ p s)
    {lam : ℝ} (hlam : lam ∈ positiveCostLevels p c) :
    0 < costLevelMass p c lam := by
  classical
  obtain ⟨s, hs, hcs⟩ := Finset.mem_image.mp hlam
  have hsp : 0 < p s := (Finset.mem_filter.mp hs).2
  have hsFiber : s ∈ (positiveMassStates p).filter (fun t ↦ c t = lam) := by
    simp [positiveMassStates, (Finset.mem_filter.mp hs).1, hcs, hsp]
  have hmass : p s ≤ costLevelMass p c lam := by
    unfold costLevelMass
    exact Finset.single_le_sum (fun t _ ↦ hp t) hsFiber
  exact lt_of_lt_of_le hsp hmass

/-- Aggregating cost-weighted masses across represented cost levels recovers the
state-indexed expected cost. The result is exact even when some states have
zero mass or multiple states have the same cost. -/
theorem sum_costLevelPayoff_eq_sum
    (p c : State → ℝ) (hp : ∀ s, 0 ≤ p s) :
    (∑ lam ∈ positiveCostLevels p c, costLevelPayoff p c lam) =
      ∑ s, p s * c s := by
  classical
  have hpartition :
      (∑ lam ∈ positiveCostLevels p c,
        ∑ s ∈ positiveMassStates p with c s = lam, p s * c s) =
        ∑ s ∈ positiveMassStates p, p s * c s := by
    exact Finset.sum_fiberwise_of_maps_to
      (fun s hs ↦ Finset.mem_image_of_mem c hs) (fun s ↦ p s * c s)
  have hsupport :
      (∑ s ∈ positiveMassStates p, p s * c s) = ∑ s, p s * c s := by
    apply Finset.sum_subset (by simp [positiveMassStates])
    intro s hs hnot
    have hnotpos : ¬ 0 < p s := by
      intro h
      exact hnot (by simp [positiveMassStates, h])
    have hzero : p s = 0 := le_antisymm (le_of_not_gt hnotpos) (hp s)
    simp [hzero]
  simpa [positiveCostLevels, costLevelPayoff] using hpartition.trans hsupport

/-- Combining the fiber identity with exhaustive aggregation expresses the
state cost objective as a sum over distinct positive-mass levels. -/
theorem sum_cost_mul_levelMass_eq_sum
    (p c : State → ℝ) (hp : ∀ s, 0 ≤ p s) :
    (∑ lam ∈ positiveCostLevels p c, lam * costLevelMass p c lam) =
      ∑ s, p s * c s := by
  calc
    (∑ lam ∈ positiveCostLevels p c, lam * costLevelMass p c lam) =
        ∑ lam ∈ positiveCostLevels p c, costLevelPayoff p c lam := by
      apply Finset.sum_congr rfl
      intro lam hlam
      exact (costLevelPayoff_eq_cost_mul_mass p c lam).symm
    _ = ∑ s, p s * c s := sum_costLevelPayoff_eq_sum p c hp

end StatisticalRL.RobustRL.TVProof.CostLevels
