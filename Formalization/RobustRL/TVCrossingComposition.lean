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

/-- At the full-positive-mass endpoint (including a zero positive-cost
mass), the already-proved disaggregation theorem gives an actual feasible
probability row without selecting or deleting any zero-cost anchor mass. -/
theorem fullPositiveCost_transfer_feasible
    (p V : State → ℝ) (s₀ : State) (vmin σ : ℝ)
    (hp : ∀ s, 0 ≤ p s) (hpSum : ∑ s, p s = 1)
    (hVmin : ∀ s, vmin ≤ V s) (hVanchor : V s₀ = vmin)
    (hbudget :
      (∑ s, if 0 < V s - vmin then p s else 0) ≤ σ) :
    (∀ s, 0 ≤ StatisticalRL.RobustRL.TVProof.Transfer.transferToMinimum
      p (StatisticalRL.RobustRL.TVProof.Disaggregation.stateRemoval p
        (fun s ↦ V s - vmin)
        (StatisticalRL.RobustRL.TVProof.Disaggregation.fullPositiveCostAllocation
          p (fun s ↦ V s - vmin))) s₀ s) ∧
    (∑ s, StatisticalRL.RobustRL.TVProof.Transfer.transferToMinimum
      p (StatisticalRL.RobustRL.TVProof.Disaggregation.stateRemoval p
        (fun s ↦ V s - vmin)
        (StatisticalRL.RobustRL.TVProof.Disaggregation.fullPositiveCostAllocation
          p (fun s ↦ V s - vmin))) s₀ s) = 1 ∧
    StatisticalRL.QLearning.qFiniteTotalVariation p
      (StatisticalRL.RobustRL.TVProof.Transfer.transferToMinimum
        p (StatisticalRL.RobustRL.TVProof.Disaggregation.stateRemoval p
          (fun s ↦ V s - vmin)
          (StatisticalRL.RobustRL.TVProof.Disaggregation.fullPositiveCostAllocation
            p (fun s ↦ V s - vmin))) s₀) ≤ σ := by
  let c : State → ℝ := fun s ↦ V s - vmin
  let a : ℝ → ℝ :=
    StatisticalRL.RobustRL.TVProof.Disaggregation.fullPositiveCostAllocation p c
  have hc : ∀ s, 0 ≤ c s := by
    intro s
    dsimp [c]
    exact sub_nonneg.mpr (hVmin s)
  have ha : ∀ lam ∈ levelSet p c,
      0 ≤ a lam ∧ a lam ≤ levelMass p c lam := by
    intro lam hlam
    exact StatisticalRL.RobustRL.TVProof.Disaggregation.fullPositiveCostAllocation_bounds p c hp hc hlam
  have hlevelBudget : (∑ lam ∈ levelSet p c, a lam) ≤ σ := by
    simpa [a, c] using fullPositiveCostAllocation_budget p c σ hp hc hpSum hbudget
  have hzero : a 0 = 0 := by
    simp [a, StatisticalRL.RobustRL.TVProof.Disaggregation.fullPositiveCostAllocation]
  have hresult := StatisticalRL.RobustRL.TVProof.Disaggregation.disaggregated_transfer_source_feasible
      p V a s₀ vmin σ hp hpSum hVmin hVanchor ha hlevelBudget hzero
  simpa [a, c] using ⟨hresult.1, hresult.2.1, hresult.2.2.2.2.1⟩

/-- State-carrier tie filling composes a genuine crossing into an exactly
budgeted feasible transfer. A positive threshold leaves every zero-cost
anchor untouched. This is the corrected carrier-level result; callers still
need to transport the sorted distinct-level crossing inequalities to the
state `aboveMass` and `tieMass` hypotheses below. -/
theorem positiveThresholdFill_transfer_feasible
    (p c : State → ℝ) (s₀ : State) (σ lam : ℝ)
    (hp : ∀ s, 0 ≤ p s) (hpSum : ∑ s, p s = 1)
    (hthreshold : 0 < lam) (hcAnchor : c s₀ = 0)
    (hbelow : StatisticalRL.RobustRL.TVProof.TieFill.aboveMass
      p c lam ≤ σ)
    (habove : σ ≤ StatisticalRL.RobustRL.TVProof.TieFill.aboveMass
      p c lam + StatisticalRL.RobustRL.TVProof.TieFill.tieMass p c lam)
    (htie : 0 < StatisticalRL.RobustRL.TVProof.TieFill.tieMass p c lam) :
    let d := StatisticalRL.RobustRL.TVProof.TieFill.thresholdFill p c σ lam
    (∀ s, 0 ≤ d s ∧ d s ≤ p s) ∧
    d s₀ = 0 ∧
    (∑ s, d s) = σ ∧
    (∀ s, 0 ≤ StatisticalRL.RobustRL.TVProof.Transfer.transferToMinimum
      p d s₀ s) ∧
    StatisticalRL.QLearning.qFiniteTotalVariation p
      (StatisticalRL.RobustRL.TVProof.Transfer.transferToMinimum p d s₀) = σ ∧
    StatisticalRL.RobustRL.TVProof.Event.qFiniteEventTV p
      (StatisticalRL.RobustRL.TVProof.Transfer.transferToMinimum p d s₀) = σ ∧
    (∑ s, StatisticalRL.RobustRL.TVProof.Transfer.transferToMinimum
      p d s₀ s) = 1 := by
  classical
  dsimp
  let d := StatisticalRL.RobustRL.TVProof.TieFill.thresholdFill p c σ lam
  have hdbounds : ∀ s, 0 ≤ d s ∧ d s ≤ p s := by
    intro s
    simpa [d] using
      StatisticalRL.RobustRL.TVProof.TieFill.thresholdFill_bounds
        p c σ lam hp hbelow habove htie s
  have hdAnchor : d s₀ = 0 := by
    simp [d, StatisticalRL.RobustRL.TVProof.TieFill.thresholdFill,
      hcAnchor, not_lt_of_ge (le_of_lt hthreshold), ne_of_lt hthreshold]
  have hdsum : ∑ s, d s = σ := by
    simpa [d] using
      StatisticalRL.RobustRL.TVProof.TieFill.thresholdFill_sum_eq_capacity
        p c σ lam hbelow habove htie
  let q := StatisticalRL.RobustRL.TVProof.Transfer.transferToMinimum
    p d s₀
  have hqnonneg : ∀ s, 0 ≤ q s := by
    simpa [q] using
      StatisticalRL.RobustRL.TVProof.Transfer.transferToMinimum_nonneg
        p d s₀ hp (fun s ↦ (hdbounds s).1) (fun s ↦ (hdbounds s).2) hdAnchor
  have hqsum : ∑ s, q s = 1 := by
    simpa [q] using
      StatisticalRL.RobustRL.TVProof.Transfer.transferToMinimum_sum
        p d s₀ hpSum
  have hTV : StatisticalRL.QLearning.qFiniteTotalVariation p q = σ := by
    calc
      StatisticalRL.QLearning.qFiniteTotalVariation p q =
          StatisticalRL.RobustRL.TVProof.Transfer.removalMass d := by
        simpa [q] using
          StatisticalRL.RobustRL.TVProof.Transfer.transferToMinimum_totalVariation_eq_removalMass
              p d s₀ (fun s ↦ (hdbounds s).1) hdAnchor
      _ = σ := by simpa [StatisticalRL.RobustRL.TVProof.Transfer.removalMass] using hdsum
  have hEvent :
      StatisticalRL.RobustRL.TVProof.Event.qFiniteEventTV p q = σ := by
    rw [StatisticalRL.RobustRL.TVProof.Event.qFiniteEventTV_eq_halfL1
      p q hp hqnonneg hpSum hqsum]
    exact hTV
  refine ⟨hdbounds, hdAnchor, hdsum, ?_, ?_, ?_, hqsum⟩
  · simpa [q] using hqnonneg
  · simpa [q] using hTV
  · simpa [q] using hEvent

end StatisticalRL.RobustRL.TVProof.Crossing
