import Mathlib
import Formalization.RobustRL.TVPayoffCertificate
import Formalization.RobustRL.TVEventBridge

/-! TV proof case composition of the source-facing TV reverse
witness. It produces a feasible row and a scalar `α` with identical values
for zero radius, the strict intermediate regime, and full-positive-mass
removal. It does not assert primal/dual equality, a max/sup identification, or
strong duality before the dependency chain is compiled and independently
reviewed. -/

open scoped BigOperators

namespace StatisticalRL.RobustRL.TVProof.AllRadius

variable {State : Type*} [Fintype State] [DecidableEq State]

/-- Across all nonnegative radii, construct an actual probability row within
the source event-TV ball and an interval scalar whose exact clipped objective
equals the row's expected value. This is the reverse-witness composition,
not yet a theorem about `max` of the scalar objective or `inf` of the primal. -/
theorem all_radius_matching_witness
    (p V : State → ℝ) (vmin vmax σ : ℝ)
    (hp : ∀ s, 0 ≤ p s) (hpSum : ∑ s, p s = 1)
    (hVnonneg : ∀ s, 0 ≤ V s)
    (hVmin : ∀ s, vmin ≤ V s) (hVminAttained : ∃ s, V s = vmin)
    (hVmax : ∀ s, V s ≤ vmax) (hσ : 0 ≤ σ) :
    ∃ α : ℝ, ∃ q : State → ℝ,
      vmin ≤ α ∧ α ≤ vmax ∧
      (∀ s, 0 ≤ q s) ∧ (∑ s, q s = 1) ∧
      StatisticalRL.RobustRL.TVProof.Event.qFiniteEventTV p q ≤ σ ∧
      (∑ s, q s * V s) =
        @StatisticalRL.RobustRL.TVProof.ClipThreshold.sourceTVScalarObjective
          State inferInstance
            (StatisticalRL.RobustRL.TVProof.Transfer.nonempty_of_sum_eq_one
              p hpSum) p V σ α := by
  classical
  letI : Nonempty State := StatisticalRL.RobustRL.TVProof.Transfer.nonempty_of_sum_eq_one p hpSum
  by_cases hσzero : σ = 0
  · have hnominal := StatisticalRL.RobustRL.TVProof.Payoff.zeroRadius_nominal_matches_upperScalar
        p V vmin vmax hp hpSum hVnonneg hVmin hVminAttained hVmax
    have hminmax : vmin ≤ vmax := by
      obtain ⟨s, hs⟩ := hVminAttained
      rw [← hs]
      exact hVmax s
    have hEvent :
        StatisticalRL.RobustRL.TVProof.Event.qFiniteEventTV p p = 0 := by
      rw [StatisticalRL.RobustRL.TVProof.Event.qFiniteEventTV_eq_halfL1
        p p hp hp hpSum hpSum]
      exact hnominal.2.2.1
    exact ⟨vmax, p, hminmax, le_rfl, hp, hpSum,
      by simp [hEvent, hσzero],
      by simpa [hσzero] using hnominal.2.2.2⟩
  · have hσpos : 0 < σ := lt_of_le_of_ne hσ (Ne.symm hσzero)
    let c : State → ℝ := fun s ↦ V s - vmin
    let W : ℝ := ∑ s, if 0 < c s then p s else 0
    have hc : ∀ s, 0 ≤ c s := by
      intro s
      dsimp [c]
      exact sub_nonneg.mpr (hVmin s)
    by_cases hintermediate : σ < W
    · obtain ⟨lam, hlampos, hlamupper, hqNonneg, hqSum, hqTV, hqEvent, hqValue⟩ :=
        StatisticalRL.RobustRL.TVProof.Payoff.sortedCrossing_matches_source_scalar
            p V (Classical.choose hVminAttained) vmin vmax σ
            hp hpSum hVnonneg hVmin hVmax
            (Classical.choose_spec hVminAttained) hσpos (by simpa [W, c] using hintermediate)
      have hminAlpha : vmin ≤ vmin + lam := by linarith
      have hmaxAlpha : vmin + lam ≤ vmax := by linarith
      exact ⟨vmin + lam,
        StatisticalRL.RobustRL.TVProof.Transfer.transferToMinimum p
          (StatisticalRL.RobustRL.TVProof.TieFill.thresholdFill p c σ lam)
          (Classical.choose hVminAttained),
        hminAlpha, hmaxAlpha, hqNonneg, hqSum, hqEvent, hqValue⟩
    · have hWbudget : W ≤ σ := le_of_not_gt hintermediate
      let s₀ := Classical.choose hVminAttained
      have hAnchor : V s₀ = vmin := Classical.choose_spec hVminAttained
      have hfull := StatisticalRL.RobustRL.TVProof.Payoff.fullPositiveMass_matches_lowerScalar
          p V s₀ vmin vmax σ hp hpSum hVnonneg hVmin hVminAttained
          hVmax hAnchor (by simpa [W, c] using hWbudget)
      let d : State → ℝ := StatisticalRL.RobustRL.TVProof.Disaggregation.stateRemoval
        p c (StatisticalRL.RobustRL.TVProof.Disaggregation.fullPositiveCostAllocation p c)
      let q : State → ℝ :=
        StatisticalRL.RobustRL.TVProof.Transfer.transferToMinimum p d s₀
      rcases hfull with ⟨hqNonneg, hqSum, hqTV, hqValue⟩
      have hEvent :
          StatisticalRL.RobustRL.TVProof.Event.qFiniteEventTV p q ≤ σ := by
        rw [StatisticalRL.RobustRL.TVProof.Event.qFiniteEventTV_eq_halfL1
          p q hp hqNonneg hpSum hqSum]
        simpa [q, d, c] using hqTV
      have hαrange : vmin ≤ vmax := by
        obtain ⟨s, hs⟩ := hVminAttained
        rw [← hs]
        exact hVmax s
      exact ⟨vmin, q, le_rfl, hαrange, hqNonneg, hqSum, hEvent,
        by simpa [q, d, c] using hqValue⟩

end StatisticalRL.RobustRL.TVProof.AllRadius
