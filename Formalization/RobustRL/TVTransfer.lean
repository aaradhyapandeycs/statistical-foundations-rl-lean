import Mathlib
import Formalization.ModelFree.QLearningFinitePinskerCoarsening
import Formalization.RobustRL.TVClipThresholdIdentity
import Formalization.RobustRL.TVEventBridge

/-!
# Feasible mass transfers between probability rows

Transfers an admissible removal vector to an attained minimum-value state and
proves normalization, TV-budget, and value identities. The allocation premises
are supplied by the cost-level disaggregation and crossing modules.
-/

open scoped BigOperators

namespace StatisticalRL.RobustRL.TVProof.Transfer

variable {State : Type*} [Fintype State] [DecidableEq State]

/-- A normalized finite mass function forces the finite carrier to be
nonempty. This supplies the minimum instance needed by the clipped scalar
without strengthening the source theorem's assumptions. -/
theorem nonempty_of_sum_eq_one (p : State → ℝ)
    (hpSum : ∑ s, p s = 1) : Nonempty State := by
  classical
  by_contra hne
  have hempty : IsEmpty State := not_nonempty_iff.mp hne
  letI : IsEmpty State := hempty
  have hzero : (∑ s, p s) = 0 := by simp
  rw [hpSum] at hzero
  norm_num at hzero

/-- Total amount removed from the nominal row. -/
def removalMass (d : State → ℝ) : ℝ := ∑ s, d s

/-- Mass deposited at the chosen minimum-value anchor. -/
def anchorDeposit (s₀ : State) (m : ℝ) (s : State) : ℝ :=
  if s = s₀ then m else 0

/-- Candidate robust row obtained by removing `d` and moving the removed mass
to the minimum-value anchor. -/
def transferToMinimum (p d : State → ℝ) (s₀ : State) : State → ℝ :=
  fun s ↦ p s - d s + anchorDeposit s₀ (removalMass d) s

theorem sum_anchorDeposit_eq (s₀ : State) (m : ℝ) :
    (∑ s, anchorDeposit s₀ m s) = m := by
  classical
  simp [anchorDeposit]

/-- The transfer preserves total probability whenever the removed mass is
deposited in full. -/
theorem transferToMinimum_sum
    (p d : State → ℝ) (s₀ : State)
    (hpSum : ∑ s, p s = 1) :
    (∑ s, transferToMinimum p d s₀ s) = 1 := by
  classical
  unfold transferToMinimum removalMass
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
    sum_anchorDeposit_eq, hpSum]
  ring

/-- The transferred row is nonnegative if removals are coordinatewise
feasible and do not remove the anchor's mass. -/
theorem transferToMinimum_nonneg
    (p d : State → ℝ) (s₀ : State)
    (hp : ∀ s, 0 ≤ p s) (hdNonneg : ∀ s, 0 ≤ d s)
    (hdLe : ∀ s, d s ≤ p s) (hdAnchor : d s₀ = 0) :
    ∀ s, 0 ≤ transferToMinimum p d s₀ s := by
  classical
  intro s
  by_cases hs : s = s₀
  · subst s
    have hm : 0 ≤ removalMass d := Finset.sum_nonneg fun i _ ↦ hdNonneg i
    simpa [transferToMinimum, anchorDeposit, hdAnchor] using
      add_nonneg (hp s₀) hm
  · have hbase : 0 ≤ p s - d s := sub_nonneg.mpr (hdLe s)
    simpa [transferToMinimum, anchorDeposit, hs] using hbase

/-- For a feasible removal vector that leaves the anchor unchanged, half-L¹
total variation from the nominal row is exactly the removed mass. -/
theorem transferToMinimum_totalVariation_eq_removalMass
    (p d : State → ℝ) (s₀ : State)
    (hdNonneg : ∀ s, 0 ≤ d s) (hdAnchor : d s₀ = 0) :
    StatisticalRL.QLearning.qFiniteTotalVariation p
      (transferToMinimum p d s₀) = removalMass d := by
  classical
  have hpoint (s : State) :
      |p s - transferToMinimum p d s₀ s| =
        d s + anchorDeposit s₀ (removalMass d) s := by
    by_cases hs : s = s₀
    · subst s
      have hm : 0 ≤ removalMass d := Finset.sum_nonneg fun i _ ↦ hdNonneg i
      simp only [transferToMinimum, anchorDeposit, hdAnchor, sub_zero, if_true, zero_add]
      have hdiff : p s₀ - (p s₀ + removalMass d) = -removalMass d := by ring
      rw [hdiff, abs_of_nonpos (neg_nonpos.mpr hm)]
      simp [removalMass, hdAnchor]
    · simp only [transferToMinimum, anchorDeposit, if_neg hs, add_zero]
      have hdiff : p s - (p s - d s) = d s := by ring
      rw [hdiff, abs_of_nonneg (hdNonneg s)]
  have hnorm :
      (∑ s, |p s - transferToMinimum p d s₀ s|) =
        removalMass d + removalMass d := by
    calc
      (∑ s, |p s - transferToMinimum p d s₀ s|) =
          ∑ s, (d s + anchorDeposit s₀ (removalMass d) s) := by
        apply Finset.sum_congr rfl
        intro s hs
        exact hpoint s
      _ = removalMass d + removalMass d := by
        rw [Finset.sum_add_distrib, sum_anchorDeposit_eq]
        rfl
  unfold StatisticalRL.QLearning.qFiniteTotalVariation
  rw [hnorm]
  ring

/-- The transfer respects the source uncertainty ball whenever the removed
mass is within its TV radius. The equality uses the source half-L¹
normalization. -/
theorem transferToMinimum_TV_feasible
    (p d : State → ℝ) (s₀ : State) (σ : ℝ)
    (hdNonneg : ∀ s, 0 ≤ d s) (hdAnchor : d s₀ = 0)
    (hdBudget : removalMass d ≤ σ) :
    StatisticalRL.QLearning.qFiniteTotalVariation p
      (transferToMinimum p d s₀) ≤ σ := by
  rw [transferToMinimum_totalVariation_eq_removalMass p d s₀ hdNonneg hdAnchor]
  exact hdBudget

/-- Exact value accounting for the transfer: the new row's value is the
nominal value minus the removed shifted-value objective. -/
theorem transferToMinimum_expectation_eq_nominal_sub_shiftedRemoval
    (p d V : State → ℝ) (s₀ : State) (vmin : ℝ)
    (hdAnchor : d s₀ = 0) (hVanchor : V s₀ = vmin) :
    (∑ s, transferToMinimum p d s₀ s * V s) =
      (∑ s, p s * V s) -
        (∑ s, d s * (V s - vmin)) := by
  classical
  unfold transferToMinimum anchorDeposit
  have hdeposit :
      (∑ s, (if s = s₀ then removalMass d else 0) * V s) =
        removalMass d * vmin := by
    simp [hVanchor]
  calc
    (∑ s, (p s - d s + (if s = s₀ then removalMass d else 0)) * V s) =
        ∑ s, (p s * V s - d s * V s +
          (if s = s₀ then removalMass d else 0) * V s) := by
      apply Finset.sum_congr rfl
      intro s hs
      ring
    _ = (∑ s, p s * V s) - (∑ s, d s * V s) +
          ∑ s, (if s = s₀ then removalMass d else 0) * V s := by
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    _ = (∑ s, p s * V s) - (∑ s, d s * V s) +
          removalMass d * vmin := by rw [hdeposit]
    _ = (∑ s, p s * V s) -
          (∑ s, d s * (V s - vmin)) := by
      have hshift :
          (∑ s, d s * (V s - vmin)) =
            (∑ s, d s * V s) - removalMass d * vmin := by
        calc
          (∑ s, d s * (V s - vmin)) =
              ∑ s, (d s * V s - d s * vmin) := by
            apply Finset.sum_congr rfl
            intro s hs
            ring
          _ = (∑ s, d s * V s) - ∑ s, d s * vmin := by
            rw [Finset.sum_sub_distrib]
          _ = (∑ s, d s * V s) - removalMass d * vmin := by
            simp only [removalMass, Finset.sum_mul]
      rw [hshift]
      ring

/-- Conditional source-facing reverse witness. If a removal vector has the
threshold-certificate objective and leaves an attained minimum state alone,
the transferred row is a feasible primal row whose expectation equals the
source scalar dual value. The construction supplies the optimizer side of the
argument, but deriving `hcertificate` from the sorted level fill remains a
separate obligation supplied by the threshold-fill construction. -/
theorem transfer_witness_matches_source_scalar
    (p d V : State → ℝ) (s₀ : State) (vmin vmax σ α : ℝ)
    (hp : ∀ s, 0 ≤ p s) (hpSum : ∑ s, p s = 1)
    (hVnonneg : ∀ s, 0 ≤ V s)
    (hVmin : ∀ s, vmin ≤ V s) (hVminAttained : ∃ s, V s = vmin)
    (hVmax : ∀ s, V s ≤ vmax)
    (hαlo : vmin ≤ α) (hαhi : α ≤ vmax)
    (hdNonneg : ∀ s, 0 ≤ d s) (hdLe : ∀ s, d s ≤ p s)
    (hdAnchor : d s₀ = 0) (hAnchor : V s₀ = vmin)
    (hdBudget : removalMass d ≤ σ)
    (hcertificate :
      (∑ s, d s * (V s - vmin)) =
        StatisticalRL.RobustRL.TVProof.ClipThreshold.positivePartThresholdCertificate
          p V vmin σ (α - vmin)) :
    (∀ s, 0 ≤ transferToMinimum p d s₀ s) ∧
      (∑ s, transferToMinimum p d s₀ s) = 1 ∧
      StatisticalRL.QLearning.qFiniteTotalVariation p
        (transferToMinimum p d s₀) ≤ σ ∧
      StatisticalRL.RobustRL.TVProof.Event.qFiniteEventTV p
        (transferToMinimum p d s₀) ≤ σ ∧
      (∑ s, transferToMinimum p d s₀ s * V s) =
        @StatisticalRL.RobustRL.TVProof.ClipThreshold.sourceTVScalarObjective
          State inferInstance (nonempty_of_sum_eq_one p hpSum) p V σ α := by
  letI : Nonempty State := nonempty_of_sum_eq_one p hpSum
  have hqnonneg := transferToMinimum_nonneg p d s₀ hp hdNonneg hdLe hdAnchor
  have hqsum := transferToMinimum_sum p d s₀ hpSum
  have htv := transferToMinimum_TV_feasible p d s₀ σ hdNonneg hdAnchor hdBudget
  have hEventTV :
      StatisticalRL.RobustRL.TVProof.Event.qFiniteEventTV p
          (transferToMinimum p d s₀) ≤ σ := by
    rw [StatisticalRL.RobustRL.TVProof.Event.qFiniteEventTV_eq_halfL1
      p (transferToMinimum p d s₀) hp hqnonneg hpSum hqsum]
    exact htv
  have hvalue := transferToMinimum_expectation_eq_nominal_sub_shiftedRemoval
    p d V s₀ vmin hdAnchor hAnchor
  have halgebra := StatisticalRL.RobustRL.TVProof.ClipThreshold.sourceTVScalar_eq_nominal_sub_thresholdCertificate
    p V vmin vmax σ α
      hp hpSum hVnonneg hVmin hVminAttained hVmax hαlo hαhi
  refine ⟨hqnonneg, hqsum, htv, hEventTV, ?_⟩
  rw [hvalue, hcertificate]
  simpa [StatisticalRL.RobustRL.TVProof.ClipThreshold.nominalValue] using
    halgebra.symm

end StatisticalRL.RobustRL.TVProof.Transfer
