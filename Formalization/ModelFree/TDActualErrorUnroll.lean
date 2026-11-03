import Formalization.ModelFree.TDActualErrorDecomposition
import Mathlib.Algebra.BigOperators.Intervals

/-! Exact finite unrolling of actual TD errors with chronological propagators.
No stochastic centering or concentration result is assumed. -/
open scoped BigOperators
namespace StatisticalRL.TemporalDifference
variable {State Action : Type*} [Fintype State] [Fintype Action]

theorem tdErrorTransition_zero (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (η : ℕ → ℝ) (i : ℕ) :
    tdErrorTransition M π η i 0 = 0 := by
  funext s
  change (1 - η i) * 0 + η i * M.discount * (M.policyTransition π s).expectation (fun _ ↦ 0) = 0
  simp

theorem tdErrorTransition_sum (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (η : ℕ → ℝ) (i : ℕ)
    (S : Finset ℕ) (U : ℕ → State → ℝ) :
    tdErrorTransition M π η i (∑ k ∈ S, U k) = ∑ k ∈ S, tdErrorTransition M π η i (U k) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using tdErrorTransition_zero M π η i
  | @insert k S hk ih =>
    rw [Finset.sum_insert hk, tdErrorTransition_add, ih, Finset.sum_insert hk]

theorem tdErrorPropagate_diagonal (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (η : ℕ → ℝ) (k : ℕ) (U : State → ℝ) :
    tdErrorPropagate M π η k k U = U := by
  cases k with
  | zero => rfl
  | succ k => simp only [tdErrorPropagate, Nat.not_succ_le_self, if_false]

theorem tdErrorPropagate_succ (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (η : ℕ → ℝ) (start n : ℕ) (h : start ≤ n) (U : State → ℝ) :
    tdErrorPropagate M π η start (n + 1) U =
      tdErrorTransition M π η (n + 1) (tdErrorPropagate M π η start n U) := by
  simp only [tdErrorPropagate, if_pos h]

theorem tdErrorPropagate_mul (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (η : ℕ → ℝ) (start n : ℕ) (c : ℝ) (U : State → ℝ) :
    tdErrorPropagate M π η start n (fun s ↦ c * U s) =
      fun s ↦ c * tdErrorPropagate M π η start n U s := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [tdErrorPropagate]
    split_ifs with h
    · rw [ih, tdErrorTransition_mul]
    · rfl

theorem tdWeightedErrorIncrement_source_form (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (η : ℕ → ℝ) (samples : ℕ → State → State)
    (V₀ : State → ℝ) (t k : ℕ) (hk : 1 ≤ k) (hkt : k ≤ t) :
    tdWeightedErrorIncrement M π η samples V₀ t k = fun s ↦
      M.discount * η k * tdErrorPropagate M π η k t (tdCenteredRowNoise M π η samples V₀ k) s := by
  rw [tdWeightedErrorIncrement, if_pos ⟨hk,hkt⟩]
  exact tdErrorPropagate_mul M π η k t (M.discount * η k) _

theorem tdWeightedErrorIncrement_succ (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (η : ℕ → ℝ) (samples : ℕ → State → State)
    (V₀ : State → ℝ) (t k : ℕ) (hk : 1 ≤ k) (hkt : k ≤ t) :
    tdWeightedErrorIncrement M π η samples V₀ (t + 1) k =
      tdErrorTransition M π η (t + 1) (tdWeightedErrorIncrement M π η samples V₀ t k) := by
  rw [tdWeightedErrorIncrement, if_pos ⟨hk, by omega⟩,
    tdErrorPropagate_succ M π η k t hkt, tdWeightedErrorIncrement, if_pos ⟨hk,hkt⟩]

theorem tdWeightedErrorIncrement_diagonal (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (η : ℕ → ℝ) (samples : ℕ → State → State)
    (V₀ : State → ℝ) (t : ℕ) :
    tdWeightedErrorIncrement M π η samples V₀ (t + 1) (t + 1) =
      fun s ↦ M.discount * η (t + 1) * tdCenteredRowNoise M π η samples V₀ (t + 1) s := by
  rw [tdWeightedErrorIncrement, if_pos ⟨by omega, le_rfl⟩, tdErrorPropagate_diagonal]

/-- Source exact error telescope, with actual trajectory target and actual old
iterate noise. The propagator applies updates in chronological order. -/
theorem tdErrorValue_eq_initial_add_increments (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (η : ℕ → ℝ) (samples : ℕ → State → State)
    (V₀ : State → ℝ) (t : ℕ) :
    tdErrorValue M π η samples V₀ t =
      tdErrorPropagate M π η 0 t (V₀ - M.trajectoryExpectedValue π) +
        ∑ k ∈ Finset.Icc 1 t, tdWeightedErrorIncrement M π η samples V₀ t k := by
  induction t with
  | zero => simp [tdErrorValue, tdIterate, tdErrorPropagate]
  | succ t ih =>
    have hsum : tdErrorTransition M π η (t + 1)
        (∑ k ∈ Finset.Icc 1 t, tdWeightedErrorIncrement M π η samples V₀ t k) =
        ∑ k ∈ Finset.Icc 1 t, tdWeightedErrorIncrement M π η samples V₀ (t + 1) k := by
      rw [tdErrorTransition_sum]
      apply Finset.sum_congr rfl
      intro k hk
      have hh := Finset.mem_Icc.mp hk
      exact (tdWeightedErrorIncrement_succ M π η samples V₀ t k hh.1 hh.2).symm
    rw [tdErrorValue_succ, ih, tdErrorTransition_add, hsum,
      tdErrorPropagate_succ M π η 0 t (Nat.zero_le t),
      Finset.sum_Icc_succ_top (by omega : 1 ≤ t + 1), tdWeightedErrorIncrement_diagonal]
    exact add_assoc _ _ _

end StatisticalRL.TemporalDifference
