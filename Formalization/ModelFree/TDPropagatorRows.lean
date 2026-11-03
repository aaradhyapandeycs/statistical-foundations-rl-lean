import Formalization.ModelFree.TDErrorCaps
import Formalization.ModelFree.TDLinearRowVariance

/-! Actual chronological TD propagator rows, their nonnegative entries and
exact mass. The terminal index remains explicit throughout. -/
open scoped BigOperators
namespace StatisticalRL.TemporalDifference
variable {State Action : Type*} [Fintype State] [Fintype Action]
noncomputable local instance tdPropagatorStateDecidable : DecidableEq State := Classical.decEq State

/-- An actual row coefficient: propagate the finite basis vector at r. -/
noncomputable def tdPropagatorRow (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (η : ℕ → ℝ) (start t : ℕ) (s r : State) : ℝ :=
  tdErrorPropagate M π η start t (fun x ↦ if x = r then 1 else 0) s

theorem tdErrorPropagate_zero (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (η : ℕ → ℝ) (start t : ℕ) : tdErrorPropagate M π η start t 0 = 0 := by
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [tdErrorPropagate]
    split_ifs with h
    · rw [ih, tdErrorTransition_zero]
    · rfl

theorem tdErrorPropagate_add (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (η : ℕ → ℝ) (start t : ℕ) (U V : State → ℝ) :
    tdErrorPropagate M π η start t (U + V) =
      tdErrorPropagate M π η start t U + tdErrorPropagate M π η start t V := by
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [tdErrorPropagate]
    split_ifs with h
    · rw [ih, tdErrorTransition_add]
    · rfl

theorem tdErrorPropagate_sum {ι : Type*} (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (η : ℕ → ℝ) (start t : ℕ) (S : Finset ι) (U : ι → State → ℝ) :
    tdErrorPropagate M π η start t (∑ r ∈ S, U r) =
      ∑ r ∈ S, tdErrorPropagate M π η start t (U r) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using tdErrorPropagate_zero M π η start t
  | @insert r S hr ih =>
    rw [Finset.sum_insert hr, tdErrorPropagate_add, ih, Finset.sum_insert hr]

/-- Every actual propagated vector is represented by these exact row entries. -/
theorem tdErrorPropagate_eq_row_sum (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (η : ℕ → ℝ) (start t : ℕ) (U : State → ℝ) (s : State) :
    tdErrorPropagate M π η start t U s = ∑ r, tdPropagatorRow M π η start t s r * U r := by
  classical
  have he : U = ∑ r : State, fun x ↦ U r * (if x = r then 1 else 0) := by
    funext x
    simp
  have hp := congrArg (fun W : State → ℝ ↦ tdErrorPropagate M π η start t W s) he
  dsimp only at hp
  rw [tdErrorPropagate_sum] at hp
  simp only [Finset.sum_apply, tdErrorPropagate_mul] at hp
  calc
    _ = ∑ r : State, U r * tdErrorPropagate M π η start t (fun x ↦ if x = r then 1 else 0) s := hp
    _ = _ := by apply Finset.sum_congr rfl; intro r hr; unfold tdPropagatorRow; ring

/-- Positivity is derived from actual stochastic rows and positive-prefix rates. -/
theorem tdErrorPropagate_nonneg (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (η : ℕ → ℝ) (start t : ℕ)
    (hη : ∀ i, 1 ≤ i → i ≤ t → 0 ≤ η i ∧ η i ≤ 1)
    (U : State → ℝ) (hU : ∀ r, 0 ≤ U r) (s : State) :
    0 ≤ tdErrorPropagate M π η start t U s := by
  induction t generalizing s with
  | zero => exact hU s
  | succ t ih =>
    by_cases hst : start ≤ t
    · rw [tdErrorPropagate_succ M π η start t hst]
      have hi := hη (t + 1) (by omega) le_rfl
      have hp (r : State) := ih (fun i hi hit ↦ hη i hi (by omega)) r
      exact add_nonneg (mul_nonneg (sub_nonneg.mpr hi.2) (hp s))
        (mul_nonneg (mul_nonneg hi.1 M.discount_nonneg) ((M.policyTransition π s).expectation_nonneg hp))
    · simpa only [tdErrorPropagate, if_neg hst] using hU s

theorem tdPropagatorRow_nonneg (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (η : ℕ → ℝ) (start t : ℕ)
    (hη : ∀ i, 1 ≤ i → i ≤ t → 0 ≤ η i ∧ η i ≤ 1) (s r : State) :
    0 ≤ tdPropagatorRow M π η start t s r := by
  apply tdErrorPropagate_nonneg M π η start t hη
  intro x
  split_ifs <;> norm_num

/-- Constant vectors are propagated by the exact scalar contraction product. -/
theorem tdErrorPropagate_const (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (η : ℕ → ℝ) (start t : ℕ) (hst : start ≤ t) (c : ℝ) :
    tdErrorPropagate M π η start t (fun _ ↦ c) =
      fun _ ↦ (∏ i ∈ Finset.Icc (start + 1) t, tdRateContraction M.discount η i) * c := by
  induction t with
  | zero =>
    have hs : start = 0 := by omega
    subst start
    simp [tdErrorPropagate]
  | succ t ih =>
    by_cases hs : start ≤ t
    · rw [tdErrorPropagate_succ M π η start t hs, ih hs]
      funext s
      simp only [tdErrorTransition, FiniteDistribution.expectation_const]
      rw [Finset.prod_Icc_succ_top (by omega : start + 1 ≤ t + 1)]
      unfold tdRateContraction
      ring
    · have he : start = t + 1 := by omega
      subst start
      rw [tdErrorPropagate_diagonal]
      simp

/-- Exact row mass, with no matrix operator-norm convention or inequality. -/
theorem tdPropagatorRow_sum (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (η : ℕ → ℝ) (start t : ℕ) (hst : start ≤ t) (s : State) :
    (∑ r, tdPropagatorRow M π η start t s r) =
      ∏ i ∈ Finset.Icc (start + 1) t, tdRateContraction M.discount η i := by
  have hr := tdErrorPropagate_eq_row_sum M π η start t (fun _ ↦ 1) s
  rw [tdErrorPropagate_const M π η start t hst 1] at hr
  simpa only [mul_one] using hr.symm

/-- The exact deterministic row in source Z_k^t includes γη_k ONCE. -/
noncomputable def tdWeightedPropagatorRow (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (η : ℕ → ℝ) (t k : ℕ) (s r : State) : ℝ :=
  M.discount * η k * tdPropagatorRow M π η k t s r

theorem tdWeightedPropagatorRow_nonneg (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (η : ℕ → ℝ) (t k : ℕ) (hk : 1 ≤ k) (hkt : k ≤ t)
    (hη : ∀ i, 1 ≤ i → i ≤ t → 0 ≤ η i ∧ η i ≤ 1) (s r : State) :
    0 ≤ tdWeightedPropagatorRow M π η t k s r := by
  exact mul_nonneg (mul_nonneg M.discount_nonneg (hη k hk hkt).1)
    (tdPropagatorRow_nonneg M π η k t hη s r)

theorem tdWeightedPropagatorRow_sum (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (η : ℕ → ℝ) (t k : ℕ) (hk : 1 ≤ k) (hkt : k ≤ t) (s : State) :
    (∑ r, tdWeightedPropagatorRow M π η t k s r) = M.discount * tdRateWeight M.discount η t k := by
  unfold tdWeightedPropagatorRow
  rw [← Finset.mul_sum, tdPropagatorRow_sum M π η k t hkt s,
    tdRateWeight, if_pos hkt, if_neg (by omega : k ≠ 0)]
  ring

theorem tdWeightedPropagatorRow_apply (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (η : ℕ → ℝ) (t k : ℕ) (s : State) (U : State → ℝ) :
    (∑ r, tdWeightedPropagatorRow M π η t k s r * U r) =
      M.discount * η k * tdErrorPropagate M π η k t U s := by
  rw [tdErrorPropagate_eq_row_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  unfold tdWeightedPropagatorRow
  ring

/-- Fixed terminal t and source update k: actual Z, not a surrogate row. -/
theorem tdWeightedErrorIncrement_eq_row_sum (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (η : ℕ → ℝ) (samples : ℕ → State → State) (V₀ : State → ℝ)
    (t k : ℕ) (hk : 1 ≤ k) (hkt : k ≤ t) (s : State) :
    tdWeightedErrorIncrement M π η samples V₀ t k s =
      ∑ r, tdWeightedPropagatorRow M π η t k s r * tdCenteredRowNoise M π η samples V₀ k r := by
  rw [tdWeightedErrorIncrement_source_form M π η samples V₀ t k hk hkt]
  dsimp only
  rw [tdErrorPropagate_eq_row_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  unfold tdWeightedPropagatorRow
  ring

end StatisticalRL.TemporalDifference
