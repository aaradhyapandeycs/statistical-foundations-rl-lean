import Mathlib
import Formalization.RobustRL.TVClipThresholdIdentity
import Formalization.RobustRL.TVTransfer
import Formalization.RobustRL.TVDisaggregation
import Formalization.RobustRL.TVEventBridge
import Formalization.RobustRL.TVSortedThreshold

/-! TV proof payoff-to-certificate composition. It proves the
finite state threshold-fill objective identity, transports it to the clipped
source scalar, and records separate zero-radius/full-positive-mass endpoints.
No strong-duality theorem is claimed. -/

open scoped BigOperators

namespace StatisticalRL.RobustRL.TVProof.Payoff

variable {State : Type*} [Fintype State] [DecidableEq State]

/-- The state-carrier threshold-fill objective is exactly the usual
positive-part threshold certificate whenever the crossing fills mass `σ`.
The proof is pointwise and handles strict-above, tied, and strict-below
coordinates separately. -/
theorem thresholdFill_cost_eq_certificate
    (p c : State → ℝ) (σ lam : ℝ)
    (hbelow : StatisticalRL.RobustRL.TVProof.TieFill.aboveMass
      p c lam ≤ σ)
    (habove : σ ≤ StatisticalRL.RobustRL.TVProof.TieFill.aboveMass
      p c lam + StatisticalRL.RobustRL.TVProof.TieFill.tieMass p c lam)
    (htie : 0 < StatisticalRL.RobustRL.TVProof.TieFill.tieMass p c lam) :
    (∑ s, StatisticalRL.RobustRL.TVProof.TieFill.thresholdFill
      p c σ lam s * c s) =
      lam * σ + ∑ s, p s * max (c s - lam) 0 := by
  classical
  let d := StatisticalRL.RobustRL.TVProof.TieFill.thresholdFill p c σ lam
  have hmass : ∑ s, d s = σ := by
    simpa [d] using
      StatisticalRL.RobustRL.TVProof.TieFill.thresholdFill_sum_eq_capacity
        p c σ lam hbelow habove htie
  have hpoint (s : State) :
      d s * c s = lam * d s + p s * max (c s - lam) 0 := by
    by_cases hgt : lam < c s
    · simp [d, StatisticalRL.RobustRL.TVProof.TieFill.thresholdFill,
        hgt, max_eq_left (sub_nonneg.mpr (le_of_lt hgt))]
      ring
    · by_cases heq : c s = lam
      · have hzero : c s - lam ≤ 0 := by simp [heq]
        simp [d, StatisticalRL.RobustRL.TVProof.TieFill.thresholdFill,
          hgt, heq, max_eq_right hzero] <;> ring
      · have hcle : c s ≤ lam := le_of_not_gt hgt
        have hzero : c s - lam ≤ 0 := sub_nonpos.mpr hcle
        simp [d, StatisticalRL.RobustRL.TVProof.TieFill.thresholdFill,
          hgt, heq, max_eq_right hzero]
  calc
    (∑ s, StatisticalRL.RobustRL.TVProof.TieFill.thresholdFill
        p c σ lam s * c s) = ∑ s, (lam * d s + p s * max (c s - lam) 0) := by
      apply Finset.sum_congr rfl
      intro s hs
      exact hpoint s
    _ = lam * (∑ s, d s) + ∑ s, p s * max (c s - lam) 0 := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    _ = lam * σ + ∑ s, p s * max (c s - lam) 0 := by rw [hmass]

/-- A positive-threshold state fill yields a feasible primal witness whose
payoff equals the exact source TV scalar objective at `α = vmin + lam`. The
source's full nonnegativity, extrema, normalization and interval assumptions
remain explicit. -/
theorem thresholdFill_matches_source_scalar
    (p V : State → ℝ) (s₀ : State) (vmin vmax σ lam : ℝ)
    (hp : ∀ s, 0 ≤ p s) (hpSum : ∑ s, p s = 1)
    (hVnonneg : ∀ s, 0 ≤ V s)
    (hVmin : ∀ s, vmin ≤ V s) (hVminAttained : ∃ s, V s = vmin)
    (hVmax : ∀ s, V s ≤ vmax) (hAnchor : V s₀ = vmin)
    (hlampos : 0 < lam) (hlamupper : lam ≤ vmax - vmin)
    (hbelow : StatisticalRL.RobustRL.TVProof.TieFill.aboveMass
      p (fun s ↦ V s - vmin) lam ≤ σ)
    (habove : σ ≤ StatisticalRL.RobustRL.TVProof.TieFill.aboveMass
      p (fun s ↦ V s - vmin) lam +
        StatisticalRL.RobustRL.TVProof.TieFill.tieMass
          p (fun s ↦ V s - vmin) lam)
    (htie : 0 < StatisticalRL.RobustRL.TVProof.TieFill.tieMass
      p (fun s ↦ V s - vmin) lam) :
    (∀ s, 0 ≤ StatisticalRL.RobustRL.TVProof.Transfer.transferToMinimum
      p (StatisticalRL.RobustRL.TVProof.TieFill.thresholdFill
        p (fun s ↦ V s - vmin) σ lam) s₀ s) ∧
    (∑ s, StatisticalRL.RobustRL.TVProof.Transfer.transferToMinimum
      p (StatisticalRL.RobustRL.TVProof.TieFill.thresholdFill
        p (fun s ↦ V s - vmin) σ lam) s₀ s) = 1 ∧
    StatisticalRL.QLearning.qFiniteTotalVariation p
      (StatisticalRL.RobustRL.TVProof.Transfer.transferToMinimum
        p (StatisticalRL.RobustRL.TVProof.TieFill.thresholdFill
          p (fun s ↦ V s - vmin) σ lam) s₀) ≤ σ ∧
    StatisticalRL.RobustRL.TVProof.Event.qFiniteEventTV p
      (StatisticalRL.RobustRL.TVProof.Transfer.transferToMinimum
        p (StatisticalRL.RobustRL.TVProof.TieFill.thresholdFill
          p (fun s ↦ V s - vmin) σ lam) s₀) ≤ σ ∧
    (∑ s, StatisticalRL.RobustRL.TVProof.Transfer.transferToMinimum
      p (StatisticalRL.RobustRL.TVProof.TieFill.thresholdFill
        p (fun s ↦ V s - vmin) σ lam) s₀ s * V s) =
      @StatisticalRL.RobustRL.TVProof.ClipThreshold.sourceTVScalarObjective
        State inferInstance
          (StatisticalRL.RobustRL.TVProof.Transfer.nonempty_of_sum_eq_one
            p hpSum) p V σ (vmin + lam) := by
  classical
  letI : Nonempty State := StatisticalRL.RobustRL.TVProof.Transfer.nonempty_of_sum_eq_one p hpSum
  let c : State → ℝ := fun s ↦ V s - vmin
  let d : State → ℝ :=
    StatisticalRL.RobustRL.TVProof.TieFill.thresholdFill p c σ lam
  have hcAnchor : c s₀ = 0 := by simp [c, hAnchor]
  have hdbounds : ∀ s, 0 ≤ d s ∧ d s ≤ p s := by
    intro s
    simpa [d] using
      StatisticalRL.RobustRL.TVProof.TieFill.thresholdFill_bounds
        p c σ lam hp hbelow habove htie s
  have hdAnchor : d s₀ = 0 := by
    simp [d, c, StatisticalRL.RobustRL.TVProof.TieFill.thresholdFill,
      hAnchor, not_lt_of_ge (le_of_lt hlampos), ne_of_lt hlampos]
  have hdSum : ∑ s, d s = σ := by
    simpa [d] using
      StatisticalRL.RobustRL.TVProof.TieFill.thresholdFill_sum_eq_capacity
        p c σ lam hbelow habove htie
  have hcertificate :
      (∑ s, d s * (V s - vmin)) =
        StatisticalRL.RobustRL.TVProof.ClipThreshold.positivePartThresholdCertificate p V vmin σ lam := by
    simpa [c, d, StatisticalRL.RobustRL.TVProof.ClipThreshold.positivePartThresholdCertificate,
      StatisticalRL.RobustRL.TVProof.ClipThreshold.shiftedCost,
      mul_comm] using thresholdFill_cost_eq_certificate p c σ lam hbelow habove htie
  have hαlo : vmin ≤ vmin + lam := by linarith
  have hαhi : vmin + lam ≤ vmax := by linarith
  have hresult := StatisticalRL.RobustRL.TVProof.Transfer.transfer_witness_matches_source_scalar
      p d V s₀ vmin vmax σ (vmin + lam) hp hpSum hVnonneg hVmin
      hVminAttained hVmax hαlo hαhi (fun s ↦ (hdbounds s).1) (fun s ↦ (hdbounds s).2) hdAnchor hAnchor
      (by simpa [StatisticalRL.RobustRL.TVProof.Transfer.removalMass] using hdSum.le)
      (by simpa using hcertificate)
  simpa [d, c] using hresult

/-- Source-facing intermediate-radius payoff bridge. The sorted-level witness
is converted to actual state above/tie masses; those inequalities produce the
threshold vector, whose payoff equals the clipped dual scalar. -/
theorem sortedCrossing_matches_source_scalar
    (p V : State → ℝ) (s₀ : State) (vmin vmax σ : ℝ)
    (hp : ∀ s, 0 ≤ p s) (hpSum : ∑ s, p s = 1)
    (hVnonneg : ∀ s, 0 ≤ V s)
    (hVmin : ∀ s, vmin ≤ V s) (hVmax : ∀ s, V s ≤ vmax)
    (hAnchor : V s₀ = vmin)
    (hσ : 0 < σ)
    (hσW : σ < ∑ s, if 0 < V s - vmin then p s else 0) :
    ∃ lam : ℝ,
      0 < lam ∧
      lam ≤ vmax - vmin ∧
      (∀ s, 0 ≤ StatisticalRL.RobustRL.TVProof.Transfer.transferToMinimum
        p (StatisticalRL.RobustRL.TVProof.TieFill.thresholdFill
          p (fun s ↦ V s - vmin) σ lam) s₀ s) ∧
      (∑ s, StatisticalRL.RobustRL.TVProof.Transfer.transferToMinimum
        p (StatisticalRL.RobustRL.TVProof.TieFill.thresholdFill
          p (fun s ↦ V s - vmin) σ lam) s₀ s) = 1 ∧
      StatisticalRL.QLearning.qFiniteTotalVariation p
        (StatisticalRL.RobustRL.TVProof.Transfer.transferToMinimum
          p (StatisticalRL.RobustRL.TVProof.TieFill.thresholdFill
            p (fun s ↦ V s - vmin) σ lam) s₀) ≤ σ ∧
      StatisticalRL.RobustRL.TVProof.Event.qFiniteEventTV p
        (StatisticalRL.RobustRL.TVProof.Transfer.transferToMinimum
          p (StatisticalRL.RobustRL.TVProof.TieFill.thresholdFill
            p (fun s ↦ V s - vmin) σ lam) s₀) ≤ σ ∧
      (∑ s, StatisticalRL.RobustRL.TVProof.Transfer.transferToMinimum
        p (StatisticalRL.RobustRL.TVProof.TieFill.thresholdFill
          p (fun s ↦ V s - vmin) σ lam) s₀ s * V s) =
        @StatisticalRL.RobustRL.TVProof.ClipThreshold.sourceTVScalarObjective
          State inferInstance
            (StatisticalRL.RobustRL.TVProof.Transfer.nonempty_of_sum_eq_one
              p hpSum) p V σ (vmin + lam) := by
  classical
  letI : Nonempty State := StatisticalRL.RobustRL.TVProof.Transfer.nonempty_of_sum_eq_one p hpSum
  let c : State → ℝ := fun s ↦ V s - vmin
  have hc : ∀ s, 0 ≤ c s := by
    intro s
    dsimp [c]
    exact sub_nonneg.mpr (hVmin s)
  have hWle := StatisticalRL.RobustRL.TVProof.Crossing.statePositiveCostMass_le_one p c hp hc hpSum
  have hσtotal : σ ≤ ∑ s, p s := by linarith [hσW, hWle]
  obtain ⟨pre, lam, post, hdecomp, hprefix, hcross, hpre, hpost, hlampos⟩ :=
    StatisticalRL.RobustRL.TVProof.SortedState.crossing_threshold_positive
      p c σ hp hc hσ hσW hσtotal
  obtain ⟨habove, htie⟩ :=
    StatisticalRL.RobustRL.TVProof.SortedState.sortedPrefix_stateAbove_and_tie
      p c hp pre post lam hdecomp hpre hpost
  have hbelow :
      StatisticalRL.RobustRL.TVProof.TieFill.aboveMass p c lam ≤ σ := by
    rw [habove]
    exact le_of_lt hprefix
  have haboveBound :
      σ ≤ StatisticalRL.RobustRL.TVProof.TieFill.aboveMass p c lam +
        StatisticalRL.RobustRL.TVProof.TieFill.tieMass p c lam := by
    rw [habove, htie]
    exact hcross
  have hlamlevel : lam ∈
      StatisticalRL.RobustRL.TVProof.CostLevels.positiveCostLevels p c := by
    rw [← StatisticalRL.RobustRL.TVProof.SortedCrossing.sortedPositiveCostLevels_toFinset p c, hdecomp]
    simp
  have hlamupper : lam ≤ vmax - vmin := by
    obtain ⟨s, hs, hcs⟩ := Finset.mem_image.mp hlamlevel
    rw [← hcs]
    exact sub_le_sub_right (hVmax s) vmin
  have htiePos :
      0 < StatisticalRL.RobustRL.TVProof.TieFill.tieMass p c lam := by
    rw [htie]
    exact StatisticalRL.RobustRL.TVProof.CostLevels.costLevelMass_pos_of_mem p c hp hlamlevel
  have hresult := thresholdFill_matches_source_scalar
    p V s₀ vmin vmax σ lam hp hpSum hVnonneg hVmin ⟨s₀, hAnchor⟩
    hVmax hAnchor hlampos hlamupper hbelow haboveBound htiePos
  exact ⟨lam, hlampos, hlamupper, hresult.1, hresult.2.1, hresult.2.2.1,
    hresult.2.2.2.1, hresult.2.2.2.2⟩

/-- Zero-radius endpoint: the nominal row is the actual optimizer and matches
the source scalar at the upper endpoint `α = vmax`. No threshold tie mass or
positive-cost support is needed. -/
theorem zeroRadius_nominal_matches_upperScalar
    (p V : State → ℝ) (vmin vmax : ℝ)
    (hp : ∀ s, 0 ≤ p s) (hpSum : ∑ s, p s = 1)
    (hVnonneg : ∀ s, 0 ≤ V s)
    (hVmin : ∀ s, vmin ≤ V s) (hVminAttained : ∃ s, V s = vmin)
    (hVmax : ∀ s, V s ≤ vmax) :
    (∀ s, 0 ≤ p s) ∧ (∑ s, p s) = 1 ∧
    StatisticalRL.QLearning.qFiniteTotalVariation p p = 0 ∧
    (∑ s, p s * V s) =
      @StatisticalRL.RobustRL.TVProof.ClipThreshold.sourceTVScalarObjective
        State inferInstance
          (StatisticalRL.RobustRL.TVProof.Transfer.nonempty_of_sum_eq_one
            p hpSum) p V 0 vmax := by
  classical
  letI : Nonempty State := StatisticalRL.RobustRL.TVProof.Transfer.nonempty_of_sum_eq_one p hpSum
  have htv : StatisticalRL.QLearning.qFiniteTotalVariation p p = 0 := by
    unfold StatisticalRL.QLearning.qFiniteTotalVariation
    simp
  have hαlo : vmin ≤ vmax := by
    obtain ⟨s, hs⟩ := hVminAttained
    rw [← hs]
    exact hVmax s
  have hcertificate :
      StatisticalRL.RobustRL.TVProof.ClipThreshold.positivePartThresholdCertificate p V vmin 0 (vmax - vmin) = 0 := by
    unfold StatisticalRL.RobustRL.TVProof.ClipThreshold.positivePartThresholdCertificate
      StatisticalRL.RobustRL.TVProof.ClipThreshold.shiftedCost
    simp only [zero_mul, zero_add]
    apply Finset.sum_eq_zero
    intro s hs
    have hcost : V s - vmin ≤ vmax - vmin := by linarith [hVmax s]
    rw [max_eq_right (sub_nonpos.mpr hcost)]
    ring
  have halgebra := StatisticalRL.RobustRL.TVProof.ClipThreshold.sourceTVScalar_eq_nominal_sub_thresholdCertificate
      p V vmin vmax 0 vmax hp hpSum hVnonneg hVmin hVminAttained hVmax
      hαlo le_rfl
  exact ⟨hp, hpSum, htv, by
    rw [halgebra, hcertificate]
    simp [StatisticalRL.RobustRL.TVProof.ClipThreshold.nominalValue]⟩

/-- Full-removal endpoint: if the radius covers all positive shifted-cost
mass, disaggregation of the full-positive allocation gives a feasible row at
the minimum value. Its matching scalar is the lower endpoint `α=vmin`. The
source `vmax` interval and nonnegativity assumptions are still stated. -/
theorem fullPositiveMass_matches_lowerScalar
    (p V : State → ℝ) (s₀ : State) (vmin vmax σ : ℝ)
    (hp : ∀ s, 0 ≤ p s) (hpSum : ∑ s, p s = 1)
    (hVnonneg : ∀ s, 0 ≤ V s)
    (hVmin : ∀ s, vmin ≤ V s) (hVminAttained : ∃ s, V s = vmin)
    (hVmax : ∀ s, V s ≤ vmax) (hAnchor : V s₀ = vmin)
    (hbudget : (∑ s, if 0 < V s - vmin then p s else 0) ≤ σ) :
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
            p (fun s ↦ V s - vmin))) s₀) ≤ σ ∧
    (∑ s, StatisticalRL.RobustRL.TVProof.Transfer.transferToMinimum
      p (StatisticalRL.RobustRL.TVProof.Disaggregation.stateRemoval p
        (fun s ↦ V s - vmin)
        (StatisticalRL.RobustRL.TVProof.Disaggregation.fullPositiveCostAllocation
          p (fun s ↦ V s - vmin))) s₀ s * V s) =
      @StatisticalRL.RobustRL.TVProof.ClipThreshold.sourceTVScalarObjective
        State inferInstance
          (StatisticalRL.RobustRL.TVProof.Transfer.nonempty_of_sum_eq_one
            p hpSum) p V σ vmin := by
  classical
  letI : Nonempty State := StatisticalRL.RobustRL.TVProof.Transfer.nonempty_of_sum_eq_one p hpSum
  let c : State → ℝ := fun s ↦ V s - vmin
  let a : ℝ → ℝ :=
    StatisticalRL.RobustRL.TVProof.Disaggregation.fullPositiveCostAllocation p c
  let d : State → ℝ := StatisticalRL.RobustRL.TVProof.Disaggregation.stateRemoval p c a
  let q : State → ℝ :=
    StatisticalRL.RobustRL.TVProof.Transfer.transferToMinimum p d s₀
  have hc : ∀ s, 0 ≤ c s := by
    intro s
    dsimp [c]
    exact sub_nonneg.mpr (hVmin s)
  have ha : ∀ lam ∈ StatisticalRL.RobustRL.TVProof.CostLevels.positiveCostLevels p c,
      0 ≤ a lam ∧ a lam ≤ StatisticalRL.RobustRL.TVProof.CostLevels.costLevelMass p c lam := by
    intro lam hlam
    exact StatisticalRL.RobustRL.TVProof.Disaggregation.fullPositiveCostAllocation_bounds p c hp hc hlam
  have hbudgetLevels :
      (∑ lam ∈ StatisticalRL.RobustRL.TVProof.CostLevels.positiveCostLevels p c, a lam) ≤ σ := by
    simpa [a, c] using StatisticalRL.RobustRL.TVProof.Crossing.fullPositiveCostAllocation_budget p c σ hp hc hpSum hbudget
  have hzero : a 0 = 0 := by simp [a,
    StatisticalRL.RobustRL.TVProof.Disaggregation.fullPositiveCostAllocation]
  have hresult := StatisticalRL.RobustRL.TVProof.Disaggregation.disaggregated_transfer_source_feasible
      p V a s₀ vmin σ hp hpSum hVmin hAnchor ha hbudgetLevels hzero
  have hcostLevels :
      (∑ lam ∈ StatisticalRL.RobustRL.TVProof.CostLevels.positiveCostLevels p c, lam * a lam) =
        ∑ s, p s * c s := by
    calc
      (∑ lam ∈ StatisticalRL.RobustRL.TVProof.CostLevels.positiveCostLevels p c, lam * a lam) =
          ∑ lam ∈ StatisticalRL.RobustRL.TVProof.CostLevels.positiveCostLevels p c,
              lam * StatisticalRL.RobustRL.TVProof.CostLevels.costLevelMass p c lam := by
          apply Finset.sum_congr rfl
          intro lam hlam
          by_cases hpos : 0 < lam
          · simp [a, StatisticalRL.RobustRL.TVProof.Disaggregation.fullPositiveCostAllocation, hpos]
          · have hlamnonneg : 0 ≤ lam := by
              obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hlam
              exact hc s
            have hlamzero : lam = 0 := le_antisymm (le_of_not_gt hpos) hlamnonneg
            simp [hlamzero]
      _ = ∑ s, p s * c s :=
        StatisticalRL.RobustRL.TVProof.CostLevels.sum_cost_mul_levelMass_eq_sum p c hp
  have hnominalShift :
      (∑ s, p s * V s) - vmin = ∑ s, p s * c s := by
    have hmass : ∑ s, p s * vmin = vmin := by
      rw [← Finset.sum_mul, hpSum]
      ring
    calc
      (∑ s, p s * V s) - vmin =
          (∑ s, p s * V s) - ∑ s, p s * vmin := by rw [hmass]
      _ = ∑ s, p s * (V s - vmin) := by
        calc
          (∑ s, p s * V s) - ∑ s, p s * vmin =
              ∑ s, (p s * V s - p s * vmin) := by rw [Finset.sum_sub_distrib]
          _ = ∑ s, p s * (V s - vmin) := by
            apply Finset.sum_congr rfl
            intro s hs
            ring
      _ = ∑ s, p s * c s := by simp [c]
  have hremovedCost : (∑ s, d s * c s) = ∑ s, p s * c s := by
    calc
      (∑ s, d s * c s) = ∑ lam ∈ StatisticalRL.RobustRL.TVProof.CostLevels.positiveCostLevels p c, lam * a lam := by
        exact StatisticalRL.RobustRL.TVProof.Disaggregation.sum_stateRemoval_mul_cost_eq_levelObjective p c a hp ha
      _ = ∑ s, p s * c s := hcostLevels
  have hremoved : (∑ s, d s * (V s - vmin)) = ∑ s, p s * c s := by
    simpa [c] using hremovedCost
  have hqvalue : (∑ s, q s * V s) = vmin := by
    have hdAnchor : d s₀ = 0 := by
      exact StatisticalRL.RobustRL.TVProof.Disaggregation.stateRemoval_eq_zero_at_zero_cost p c a hp ha hzero (by simp [c, hAnchor])
    have hvalue := StatisticalRL.RobustRL.TVProof.Transfer.transferToMinimum_expectation_eq_nominal_sub_shiftedRemoval
        p d V s₀ vmin hdAnchor hAnchor
    dsimp [q]
    rw [hvalue, hremoved, ← hnominalShift]
    ring
  have hscalar :
      @StatisticalRL.RobustRL.TVProof.ClipThreshold.sourceTVScalarObjective
        State inferInstance
          (StatisticalRL.RobustRL.TVProof.Transfer.nonempty_of_sum_eq_one
            p hpSum) p V σ vmin = vmin := by
    have hVminMax : vmin ≤ vmax := by
      obtain ⟨s, hs⟩ := hVminAttained
      rw [← hs]
      exact hVmax s
    have hcertificate :
        StatisticalRL.RobustRL.TVProof.ClipThreshold.positivePartThresholdCertificate p V vmin σ 0 =
          (∑ s, p s * V s) - vmin := by
      have hshiftCertificate :
          StatisticalRL.RobustRL.TVProof.ClipThreshold.positivePartThresholdCertificate p V vmin σ 0 =
          ∑ s, p s * (V s - vmin) := by
        unfold StatisticalRL.RobustRL.TVProof.ClipThreshold.positivePartThresholdCertificate
          StatisticalRL.RobustRL.TVProof.ClipThreshold.shiftedCost
        simp only [mul_zero, zero_add, sub_zero]
        apply Finset.sum_congr rfl
        intro s hs
        rw [max_eq_left (sub_nonneg.mpr (hVmin s))]
      rw [hshiftCertificate]
      simpa [c] using hnominalShift.symm
    have halgebra := StatisticalRL.RobustRL.TVProof.ClipThreshold.sourceTVScalar_eq_nominal_sub_thresholdCertificate
        p V vmin vmax σ vmin hp hpSum hVnonneg hVmin hVminAttained hVmax
        le_rfl hVminMax
    rw [halgebra]
    simp only [sub_self]
    rw [hcertificate]
    unfold StatisticalRL.RobustRL.TVProof.ClipThreshold.nominalValue
    ring
  rcases hresult with ⟨hqnonneg, hqsum, _, _, hqTV, _⟩
  exact ⟨hqnonneg, hqsum, hqTV, by simpa [q] using hqvalue.trans hscalar.symm⟩

end StatisticalRL.RobustRL.TVProof.Payoff
