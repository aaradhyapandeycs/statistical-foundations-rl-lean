import Mathlib
import Formalization.RobustRL.TVCostLevels
import Formalization.RobustRL.TVEventBridge
import Formalization.RobustRL.TVTransfer

/-! TV proof state-level disaggregation helper for robust-TV
threshold allocations. An amount selected at a represented cost level is
split proportionally across the entire state fiber. Tied states are handled
together; zero-mass states receive zero. -/

open scoped BigOperators

namespace StatisticalRL.RobustRL.TVProof.Disaggregation

variable {State : Type*} [Fintype State] [DecidableEq State]

private noncomputable abbrev levelSet (p c : State → ℝ) : Finset ℝ :=
  StatisticalRL.RobustRL.TVProof.CostLevels.positiveCostLevels p c

private noncomputable abbrev levelMass (p c : State → ℝ) (lam : ℝ) : ℝ :=
  StatisticalRL.RobustRL.TVProof.CostLevels.costLevelMass p c lam

/-- Disaggregate a selected level mass proportionally among states in its
fiber. If a state's level is absent from the positive-support image, assign
zero directly, avoiding division by a zero-mass fiber. -/
noncomputable def stateRemoval (p c : State → ℝ) (a : ℝ → ℝ) (s : State) : ℝ := by
  classical
  exact if h : c s ∈ levelSet p c then
    (a (c s) / levelMass p c (c s)) * p s
  else 0

/-- Every represented cost level has positive aggregate probability mass. -/
theorem levelMass_pos
    (p c : State → ℝ) (hp : ∀ s, 0 ≤ p s)
    {lam : ℝ} (hlam : lam ∈ levelSet p c) :
    0 < levelMass p c lam := by
  exact StatisticalRL.RobustRL.TVProof.CostLevels.costLevelMass_pos_of_mem
    p c hp hlam

/-- An unrepresented cost value has no positive-probability state in its
fiber. -/
private theorem probability_eq_zero_of_level_not_mem
    (p c : State → ℝ) (hp : ∀ s, 0 ≤ p s) {s : State}
    (hlevel : c s ∉ levelSet p c) : p s = 0 := by
  classical
  by_contra hne
  have hpos : 0 < p s := lt_of_le_of_ne (hp s) (Ne.symm hne)
  apply hlevel
  exact Finset.mem_image.mpr
    ⟨s, by simp [StatisticalRL.RobustRL.TVProof.CostLevels.positiveMassStates,
      hpos], rfl⟩

/-- Statewise feasibility follows from a feasible level allocation. -/
theorem stateRemoval_bounds
    (p c : State → ℝ) (a : ℝ → ℝ) (hp : ∀ s, 0 ≤ p s)
    (ha : ∀ lam ∈ levelSet p c,
      0 ≤ a lam ∧ a lam ≤ levelMass p c lam) :
    ∀ s, 0 ≤ stateRemoval p c a s ∧ stateRemoval p c a s ≤ p s := by
  classical
  intro s
  by_cases hlevel : c s ∈ levelSet p c
  · have hmass := levelMass_pos p c hp hlevel
    have halloc := ha (c s) hlevel
    have hratio :
        0 ≤ a (c s) / levelMass p c (c s) ∧
          a (c s) / levelMass p c (c s) ≤ 1 := by
      constructor
      · exact div_nonneg halloc.1 (le_of_lt hmass)
      · calc
          a (c s) / levelMass p c (c s) ≤
              levelMass p c (c s) / levelMass p c (c s) :=
            div_le_div_of_nonneg_right halloc.2 (le_of_lt hmass)
          _ = 1 := div_self (ne_of_gt hmass)
    simp only [stateRemoval, dif_pos hlevel]
    refine ⟨mul_nonneg hratio.1 (hp s), ?_⟩
    simpa using mul_le_mul_of_nonneg_right hratio.2 (hp s)
  · have hpzero := probability_eq_zero_of_level_not_mem p c hp hlevel
    simp [stateRemoval, hlevel, hpzero]

/-- On a represented level fiber, the disaggregated state removals sum to the
level's prescribed amount. This is exact even when several states tie. -/
theorem stateRemoval_fiber_sum
    (p c : State → ℝ) (a : ℝ → ℝ) (hp : ∀ s, 0 ≤ p s)
    (ha : ∀ lam ∈ levelSet p c,
      0 ≤ a lam ∧ a lam ≤ levelMass p c lam)
    {lam : ℝ} (hlam : lam ∈ levelSet p c) :
    (∑ s ∈ StatisticalRL.RobustRL.TVProof.CostLevels.positiveMassStates p
        with c s = lam, stateRemoval p c a s) = a lam := by
  classical
  have hmpos := levelMass_pos p c hp hlam
  let r := a lam / levelMass p c lam
  calc
    (∑ s ∈ StatisticalRL.RobustRL.TVProof.CostLevels.positiveMassStates p
        with c s = lam, stateRemoval p c a s) =
      ∑ s ∈ StatisticalRL.RobustRL.TVProof.CostLevels.positiveMassStates p
          with c s = lam, r * p s := by
        apply Finset.sum_congr rfl
        intro s hs
        have hcs : c s = lam := (Finset.mem_filter.mp hs).2
        have hmem : c s ∈ levelSet p c := by rw [hcs]; exact hlam
        simp [stateRemoval, hmem, hlam, r, hcs]
    _ = r * levelMass p c lam := by
      rw [← Finset.mul_sum]
      rfl
    _ = a lam := by
      dsimp [r]
      field_simp [ne_of_gt hmpos]

/-- Outside positive support, disaggregated removal is zero. -/
private theorem stateRemoval_eq_zero_of_not_positive
    (p c : State → ℝ) (a : ℝ → ℝ) (hp : ∀ s, 0 ≤ p s) {s : State}
    (hnot : s ∉ StatisticalRL.RobustRL.TVProof.CostLevels.positiveMassStates p) :
    stateRemoval p c a s = 0 := by
  classical
  have hnotpos : ¬ 0 < p s := by
    intro h
    exact hnot (by simp [StatisticalRL.RobustRL.TVProof.CostLevels.positiveMassStates, h])
  have hpzero : p s = 0 := le_antisymm (le_of_not_gt hnotpos) (hp s)
  by_cases hlevel : c s ∈ levelSet p c
  · simp [stateRemoval, hlevel, hpzero]
  · simp [stateRemoval, hlevel]

/-- Total state-level removal is exactly the sum of selected level masses. -/
theorem sum_stateRemoval_eq_sum_levelAllocation
    (p c : State → ℝ) (a : ℝ → ℝ) (hp : ∀ s, 0 ≤ p s)
    (ha : ∀ lam ∈ levelSet p c,
      0 ≤ a lam ∧ a lam ≤ levelMass p c lam) :
    (∑ s, stateRemoval p c a s) = ∑ lam ∈ levelSet p c, a lam := by
  classical
  let S := StatisticalRL.RobustRL.TVProof.CostLevels.positiveMassStates p
  have hsupport : (∑ s ∈ S, stateRemoval p c a s) =
      ∑ s, stateRemoval p c a s := by
    apply Finset.sum_subset (by simp [S])
    intro s hs hnot
    exact stateRemoval_eq_zero_of_not_positive p c a hp hnot
  have hpartition :
      (∑ lam ∈ levelSet p c,
        ∑ s ∈ S with c s = lam, stateRemoval p c a s) =
        ∑ s ∈ S, stateRemoval p c a s := by
    exact Finset.sum_fiberwise_of_maps_to
      (fun s hs ↦ Finset.mem_image_of_mem c hs) (stateRemoval p c a)
  calc
    (∑ s, stateRemoval p c a s) =
        ∑ lam ∈ levelSet p c,
          ∑ s ∈ S with c s = lam, stateRemoval p c a s := by
      rw [← hsupport, hpartition.symm]
    _ = ∑ lam ∈ levelSet p c, a lam := by
      apply Finset.sum_congr rfl
      intro lam hlam
      exact stateRemoval_fiber_sum p c a hp ha hlam

/-- The removed shifted-value objective is exactly the level objective. -/
theorem sum_stateRemoval_mul_cost_eq_levelObjective
    (p c : State → ℝ) (a : ℝ → ℝ) (hp : ∀ s, 0 ≤ p s)
    (ha : ∀ lam ∈ levelSet p c,
      0 ≤ a lam ∧ a lam ≤ levelMass p c lam) :
    (∑ s, stateRemoval p c a s * c s) =
      ∑ lam ∈ levelSet p c, lam * a lam := by
  classical
  let S := StatisticalRL.RobustRL.TVProof.CostLevels.positiveMassStates p
  have hsupport :
      (∑ s ∈ S, stateRemoval p c a s * c s) =
        ∑ s, stateRemoval p c a s * c s := by
    apply Finset.sum_subset (by simp [S])
    intro s hs hnot
    rw [stateRemoval_eq_zero_of_not_positive p c a hp hnot]
    simp
  have hpartition :
      (∑ lam ∈ levelSet p c,
        ∑ s ∈ S with c s = lam, stateRemoval p c a s * c s) =
        ∑ s ∈ S, stateRemoval p c a s * c s := by
    exact Finset.sum_fiberwise_of_maps_to
      (fun s hs ↦ Finset.mem_image_of_mem c hs)
      (fun s ↦ stateRemoval p c a s * c s)
  calc
    (∑ s, stateRemoval p c a s * c s) =
        ∑ lam ∈ levelSet p c,
          ∑ s ∈ S with c s = lam, stateRemoval p c a s * c s := by
      rw [← hsupport, hpartition.symm]
    _ = ∑ lam ∈ levelSet p c, lam * a lam := by
      apply Finset.sum_congr rfl
      intro lam hlam
      calc
        (∑ s ∈ S with c s = lam, stateRemoval p c a s * c s) =
            ∑ s ∈ S with c s = lam, stateRemoval p c a s * lam := by
          apply Finset.sum_congr rfl
          intro s hs
          rw [(Finset.mem_filter.mp hs).2]
        _ = lam * (∑ s ∈ S with c s = lam, stateRemoval p c a s) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro s hs
          ring
        _ = lam * a lam := by rw [stateRemoval_fiber_sum p c a hp ha hlam]

/-- If no mass is selected from the zero-cost level, every minimum-value
anchor is untouched by the disaggregation. -/
theorem stateRemoval_eq_zero_at_zero_cost
    (p c : State → ℝ) (a : ℝ → ℝ) (hp : ∀ s, 0 ≤ p s)
    (ha : ∀ lam ∈ levelSet p c,
      0 ≤ a lam ∧ a lam ≤ levelMass p c lam)
    (hzero : a 0 = 0) {s₀ : State} (hc₀ : c s₀ = 0) :
    stateRemoval p c a s₀ = 0 := by
  classical
  by_cases hlevel : 0 ∈ levelSet p c
  · have hmpos := levelMass_pos p c hp hlevel
    simp [stateRemoval, hlevel, hc₀, hzero, hmpos]
  · have hpzero := probability_eq_zero_of_level_not_mem p c hp (s := s₀) (by
      simpa [hc₀] using hlevel)
    simp [stateRemoval, hlevel, hc₀, hpzero]

/-- Full positive-cost endpoint allocation: remove every level with positive
cost and none from the zero-cost anchor. This allocation is coordinatewise
feasible; its total budget is the aggregate positive-cost mass. -/
noncomputable def fullPositiveCostAllocation
    (p c : State → ℝ) (lam : ℝ) : ℝ :=
  if 0 < lam then levelMass p c lam else 0

theorem fullPositiveCostAllocation_bounds
    (p c : State → ℝ) (hp : ∀ s, 0 ≤ p s) (hc : ∀ s, 0 ≤ c s)
    {lam : ℝ} (hlam : lam ∈ levelSet p c) :
    0 ≤ fullPositiveCostAllocation p c lam ∧
      fullPositiveCostAllocation p c lam ≤ levelMass p c lam := by
  classical
  by_cases hpos : 0 < lam
  · simp [fullPositiveCostAllocation, hpos,
      le_of_lt (levelMass_pos p c hp hlam)]
  · have hnonneg : 0 ≤ lam := by
      obtain ⟨s, hs, hcs⟩ := Finset.mem_image.mp hlam
      rw [← hcs]
      exact hc s
    have hzero : lam = 0 := le_antisymm (le_of_not_gt hpos) hnonneg
    simp [fullPositiveCostAllocation, hpos,
      le_of_lt (levelMass_pos p c hp hlam)]

/-- Compose levelwise tie filling with statewise proportional disaggregation
and transfer to a minimum-value anchor. The result states probability
nonnegativity/normalization, exact half-L¹ and event-TV costs, and the exact
state-payoff reduction. The only allocation inputs are levelwise bounds and
the explicit level budget; no optimizer conclusion is assumed. -/
theorem disaggregated_transfer_source_feasible
    (p V : State → ℝ) (a : ℝ → ℝ) (s₀ : State) (vmin σ : ℝ)
    (hp : ∀ s, 0 ≤ p s) (hpSum : ∑ s, p s = 1)
    (hVmin : ∀ s, vmin ≤ V s) (hVanchor : V s₀ = vmin)
    (ha : ∀ lam ∈ levelSet p (fun s ↦ V s - vmin),
      0 ≤ a lam ∧ a lam ≤ levelMass p (fun s ↦ V s - vmin) lam)
    (hlevelBudget :
      (∑ lam ∈ levelSet p (fun s ↦ V s - vmin), a lam) ≤ σ)
    (hzero : a 0 = 0) :
    (∀ s, 0 ≤ StatisticalRL.RobustRL.TVProof.Transfer.transferToMinimum
      p (stateRemoval p (fun s ↦ V s - vmin) a) s₀ s) ∧
    (∑ s, StatisticalRL.RobustRL.TVProof.Transfer.transferToMinimum
      p (stateRemoval p (fun s ↦ V s - vmin) a) s₀ s) = 1 ∧
    StatisticalRL.QLearning.qFiniteTotalVariation p
      (StatisticalRL.RobustRL.TVProof.Transfer.transferToMinimum
        p (stateRemoval p (fun s ↦ V s - vmin) a) s₀) =
      ∑ lam ∈ levelSet p (fun s ↦ V s - vmin), a lam ∧
    StatisticalRL.RobustRL.TVProof.Event.qFiniteEventTV p
      (StatisticalRL.RobustRL.TVProof.Transfer.transferToMinimum
        p (stateRemoval p (fun s ↦ V s - vmin) a) s₀) =
      ∑ lam ∈ levelSet p (fun s ↦ V s - vmin), a lam ∧
    StatisticalRL.QLearning.qFiniteTotalVariation p
      (StatisticalRL.RobustRL.TVProof.Transfer.transferToMinimum
        p (stateRemoval p (fun s ↦ V s - vmin) a) s₀) ≤ σ ∧
    (∑ s, StatisticalRL.RobustRL.TVProof.Transfer.transferToMinimum
      p (stateRemoval p (fun s ↦ V s - vmin) a) s₀ s * V s) =
      (∑ s, p s * V s) -
        ∑ lam ∈ levelSet p (fun s ↦ V s - vmin), lam * a lam := by
  classical
  let c : State → ℝ := fun s ↦ V s - vmin
  let d : State → ℝ := stateRemoval p c a
  have hcNonneg : ∀ s, 0 ≤ c s := by
    intro s
    dsimp [c]
    exact sub_nonneg.mpr (hVmin s)
  have hdbounds : ∀ s, 0 ≤ d s ∧ d s ≤ p s := by
    intro s
    simpa [d, c] using stateRemoval_bounds p c a hp ha s
  have hdAnchor : d s₀ = 0 := by
    dsimp [d, c]
    exact stateRemoval_eq_zero_at_zero_cost p (fun s ↦ V s - vmin) a
      hp ha hzero (by simp [hVanchor])
  have hlevelSum : (∑ s, d s) = ∑ lam ∈ levelSet p c, a lam := by
    simpa [d, c] using sum_stateRemoval_eq_sum_levelAllocation p c a hp ha
  have hdBudget :
      StatisticalRL.RobustRL.TVProof.Transfer.removalMass d ≤ σ := by
    change (∑ s, d s) ≤ σ
    rw [hlevelSum]
    exact hlevelBudget
  let q := StatisticalRL.RobustRL.TVProof.Transfer.transferToMinimum
    p d s₀
  have hqnonneg : ∀ s, 0 ≤ q s := by
    simpa [q] using
      StatisticalRL.RobustRL.TVProof.Transfer.transferToMinimum_nonneg
        p d s₀ hp (fun s => (hdbounds s).1) (fun s => (hdbounds s).2) hdAnchor
  have hqsum : ∑ s, q s = 1 := by
    simpa [q] using
      StatisticalRL.RobustRL.TVProof.Transfer.transferToMinimum_sum
        p d s₀ hpSum
  have hTVexact :
      StatisticalRL.QLearning.qFiniteTotalVariation p q =
        ∑ lam ∈ levelSet p c, a lam := by
    calc
      StatisticalRL.QLearning.qFiniteTotalVariation p q =
          StatisticalRL.RobustRL.TVProof.Transfer.removalMass d := by
        simpa [q] using
          StatisticalRL.RobustRL.TVProof.Transfer.transferToMinimum_totalVariation_eq_removalMass
              p d s₀ (fun s => (hdbounds s).1) hdAnchor
      _ = ∑ lam ∈ levelSet p c, a lam := by
        change (∑ s, d s) = _
        exact hlevelSum
  have hEventExact :
      StatisticalRL.RobustRL.TVProof.Event.qFiniteEventTV p q =
        ∑ lam ∈ levelSet p c, a lam := by
    rw [StatisticalRL.RobustRL.TVProof.Event.qFiniteEventTV_eq_halfL1
      p q hp hqnonneg hpSum hqsum]
    exact hTVexact
  have hcost :
      (∑ s, d s * c s) = ∑ lam ∈ levelSet p c, lam * a lam := by
    simpa [d, c] using sum_stateRemoval_mul_cost_eq_levelObjective p c a hp ha
  have hvalue :=
    StatisticalRL.RobustRL.TVProof.Transfer.transferToMinimum_expectation_eq_nominal_sub_shiftedRemoval
      p d V s₀ vmin hdAnchor hVanchor
  refine ⟨?_, ?_, hTVexact, hEventExact, ?_, ?_⟩
  · simpa [q] using hqnonneg
  · simpa [q] using hqsum
  · rw [hTVexact]
    exact hlevelBudget
  · simpa [q, d, c] using hvalue.trans (congrArg (fun x ↦ (∑ s, p s * V s) - x) hcost)

end StatisticalRL.RobustRL.TVProof.Disaggregation
