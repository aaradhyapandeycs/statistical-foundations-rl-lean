import Mathlib
import Formalization.RobustRL.TVPrefixCrossing
import Formalization.RobustRL.TVCostLevels

/-! TV proof minimal bridge from the finite distinct positive-mass
cost-level image to the generic list prefix-crossing helper. It deliberately
contains no list-level tie-fill theorem: tie filling is performed later on the
actual finite state carrier. Source-mass equalities come from
the cost-level aggregation module. -/

open scoped BigOperators

namespace StatisticalRL.RobustRL.TVProof.SortedCrossing

variable {State : Type*} [Fintype State] [DecidableEq State]

private theorem sortedList_sum_eq_finset_sum (s : Finset ℝ) (f : ℝ → ℝ) :
    ((s.sort (fun x y : ℝ ↦ y ≤ x)).map f).sum = ∑ x ∈ s, f x := by
  calc
    ((s.sort (fun x y : ℝ ↦ y ≤ x)).map f).sum =
        (s.toList.map f).sum := by
      exact (Finset.sort_perm_toList s (fun x y : ℝ ↦ y ≤ x)).map f |>.sum_eq
    _ = ∑ x ∈ s, f x := by simpa using s.sum_map_toList f

/-- Distinct positive-mass levels in descending order. The finite image has
already aggregated ties; sorting cannot introduce duplicate levels. -/
noncomputable def sortedPositiveCostLevels (p c : State → ℝ) : List ℝ := by
  classical
  exact (StatisticalRL.RobustRL.TVProof.CostLevels.positiveCostLevels
    p c).sort (fun x y ↦ y ≤ x)

/-- The descending sort is duplicate-free and contains exactly the finite
positive-cost image. -/
theorem sortedPositiveCostLevels_toFinset
    (p c : State → ℝ) :
    (sortedPositiveCostLevels p c).toFinset =
      StatisticalRL.RobustRL.TVProof.CostLevels.positiveCostLevels p c := by
  classical
  simp [sortedPositiveCostLevels]

/-- The sorted level list is strictly decreasing, including when all costs
are equal (then there is only one list element). -/
theorem sortedPositiveCostLevels_pairwise
    (p c : State → ℝ) :
    List.Pairwise (fun x y : ℝ ↦ y < x) (sortedPositiveCostLevels p c) := by
  classical
  simpa [sortedPositiveCostLevels] using
    (Finset.sortedGT_sort
      (StatisticalRL.RobustRL.TVProof.CostLevels.positiveCostLevels p c)).pairwise

/-- Sorting the finite level image preserves its total aggregated probability
mass, so state normalization directly supplies the crossing's total-weight
bound. -/
theorem sortedPositiveCostLevels_mass_eq_state_sum
    (p c : State → ℝ) (hp : ∀ s, 0 ≤ p s) :
    ((sortedPositiveCostLevels p c).map
      (StatisticalRL.RobustRL.TVProof.CostLevels.costLevelMass p c)).sum =
        ∑ s, p s := by
  classical
  rw [sortedPositiveCostLevels]
  calc
    (((StatisticalRL.RobustRL.TVProof.CostLevels.positiveCostLevels
        p c).sort (fun x y : ℝ ↦ y ≤ x)).map
        (StatisticalRL.RobustRL.TVProof.CostLevels.costLevelMass p c)).sum =
      ∑ level ∈ StatisticalRL.RobustRL.TVProof.CostLevels.positiveCostLevels
          p c,
        StatisticalRL.RobustRL.TVProof.CostLevels.costLevelMass p c level :=
      sortedList_sum_eq_finset_sum _ _
    _ = ∑ s, p s :=
      StatisticalRL.RobustRL.TVProof.CostLevels.sum_costLevelMass_eq_sum
        p c hp

/-- For a positive capacity that does not exceed the level mass, sorting the
finite image and applying the list crossing lemma yields a strict prefix
above a threshold and a strict suffix below it. These are precisely the
ordering hypotheses consumed by the tie-fill bridge. The total list-mass
bound is explicit; the companion aggregation results identify the finite
image's mass with the original state sum. -/
theorem sorted_level_prefix_crossing
    (p c : State → ℝ) (capacity : ℝ)
    (hp : ∀ s, 0 ≤ p s)
    (hcapacity : 0 < capacity)
    (hcapacityTotal : capacity ≤ ∑ s, p s) :
    ∃ pre level post,
      sortedPositiveCostLevels p c = pre ++ level :: post ∧
      (pre.map (StatisticalRL.RobustRL.TVProof.CostLevels.costLevelMass p c)).sum <
          capacity ∧
        capacity ≤
          (pre.map (StatisticalRL.RobustRL.TVProof.CostLevels.costLevelMass p c)).sum +
            StatisticalRL.RobustRL.TVProof.CostLevels.costLevelMass p c level ∧
      (∀ x ∈ pre, level < x) ∧ (∀ y ∈ post, y < level) := by
  let l := sortedPositiveCostLevels p c
  let w := StatisticalRL.RobustRL.TVProof.CostLevels.costLevelMass p c
  have hlistTotal : (l.map w).sum = ∑ s, p s := by
    simpa [l, w] using
      (sortedPositiveCostLevels_mass_eq_state_sum p c hp)
  have hlistCapacity : capacity ≤ (l.map w).sum := by
    rw [hlistTotal]
    exact hcapacityTotal
  have hweights : ∀ level ∈ l, 0 ≤ w level := by
    intro level hLevel
    have hmem : level ∈ (sortedPositiveCostLevels p c).toFinset := by
      simpa [l] using hLevel
    rw [sortedPositiveCostLevels_toFinset] at hmem
    exact (StatisticalRL.RobustRL.TVProof.CostLevels.costLevelMass_pos_of_mem
      p c hp hmem).le
  obtain ⟨pre, level, post, hdecomp, hprefix, hcross⟩ :=
    StatisticalRL.RobustRL.TVProof.PrefixCrossing.exists_weighted_prefix_crossing
      w l capacity hweights hcapacity (by simpa [l, w] using hlistCapacity)
  have hsorted : List.Pairwise (fun x y : ℝ ↦ y < x) l := by
    simpa [l] using sortedPositiveCostLevels_pairwise p c
  have hpair : List.Pairwise (fun x y : ℝ ↦ y < x) (pre ++ level :: post) := by
    rw [← hdecomp]
    exact hsorted
  have hpair' := hpair
  simp only [List.pairwise_append, List.pairwise_cons] at hpair'
  rcases hpair' with ⟨_, ⟨hLevelPost, _⟩, hpreTail⟩
  have hpreAbove : ∀ x ∈ pre, level < x := by
    intro x hx
    exact hpreTail x hx level (by simp)
  have hpostBelow : ∀ y ∈ post, y < level := by
    intro y hy
    exact hLevelPost y hy
  refine ⟨pre, level, post, hdecomp, ?_, ?_, hpreAbove, hpostBelow⟩
  · simpa [w] using hprefix
  · simpa [w] using hcross

end StatisticalRL.RobustRL.TVProof.SortedCrossing
