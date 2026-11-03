import Formalization.ModelFree.TDLearningWeights

/-! Exact scalar mass telescope for actual TD learning-rate weights.
It supplies deterministic variance-cap arithmetic without assuming a target cap. -/
open scoped BigOperators
namespace StatisticalRL.TemporalDifference

theorem tdRateWeight_succ (γ : ℝ) (η : ℕ → ℝ) (t k : ℕ) (hk : k ≤ t) :
    tdRateWeight γ η (t + 1) k = tdRateWeight γ η t k * tdRateContraction γ η (t + 1) := by
  unfold tdRateWeight
  rw [if_pos (by omega : k ≤ t + 1), if_pos hk,
    Finset.prod_Icc_succ_top (by omega : k + 1 ≤ t + 1)]
  ring

theorem tdRateWeight_sum_succ (γ : ℝ) (η : ℕ → ℝ) (t : ℕ) :
    (∑ k ∈ Finset.Icc 1 (t + 1), tdRateWeight γ η (t + 1) k) =
      (∑ k ∈ Finset.Icc 1 t, tdRateWeight γ η t k) * tdRateContraction γ η (t + 1) + η (t + 1) := by
  rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ t + 1), tdRateWeight_diagonal γ η (t + 1) (by omega)]
  have he : (∑ k ∈ Finset.Icc 1 t, tdRateWeight γ η (t + 1) k) =
      ∑ k ∈ Finset.Icc 1 t, tdRateWeight γ η t k * tdRateContraction γ η (t + 1) := by
    apply Finset.sum_congr rfl
    intro k hk
    exact tdRateWeight_succ γ η t k (Finset.mem_Icc.mp hk).2
  rw [he, ← Finset.sum_mul]

/-- Exact initialization-plus-reward mass identity, including t=0 and γ=1. -/
theorem tdRateWeight_mass_identity (γ : ℝ) (η : ℕ → ℝ) (t : ℕ) :
    tdRateWeight γ η t 0 + (1 - γ) * (∑ k ∈ Finset.Icc 1 t, tdRateWeight γ η t k) = 1 := by
  induction t with
  | zero => simp [tdRateWeight]
  | succ t ih =>
    rw [tdRateWeight_succ γ η t 0 (Nat.zero_le t), tdRateWeight_sum_succ]
    have hh := congrArg (fun x : ℝ ↦ x * tdRateContraction γ η (t + 1)) ih
    unfold tdRateContraction at hh ⊢
    nlinarith

/-- Finite mass bound with no η0 condition and no infinite schedule premise. -/
theorem tdRateWeight_sum_le_horizon (γ : ℝ) (η : ℕ → ℝ) (t : ℕ)
    (hγ : 0 ≤ γ) (hγ1 : γ < 1)
    (hη : ∀ i, 1 ≤ i → i ≤ t → 0 ≤ η i ∧ η i ≤ 1) :
    (∑ k ∈ Finset.Icc 1 t, tdRateWeight γ η t k) ≤ 1 / (1 - γ) := by
  have hh := tdRateWeight_mass_identity γ η t
  have hzero := tdRateWeight_nonneg γ η t 0 hγ hγ1.le hη
  apply (le_div_iff₀ (sub_pos.mpr hγ1)).2
  nlinarith

/-- The actual squared-weight sum is controlled by its uniform envelope and
proved total mass; no desired variance estimate is assumed. -/
theorem tdRateWeight_sq_sum_le (γ : ℝ) (η : ℕ → ℝ) (t : ℕ) (A : ℝ)
    (hγ : 0 ≤ γ) (hγ1 : γ < 1) (hA : 0 ≤ A)
    (hη : ∀ i, 1 ≤ i → i ≤ t → 0 ≤ η i ∧ η i ≤ 1)
    (hcap : ∀ k, 1 ≤ k → k ≤ t → tdRateWeight γ η t k ≤ A) :
    (∑ k ∈ Finset.Icc 1 t, tdRateWeight γ η t k ^ 2) ≤ A / (1 - γ) := by
  calc
    _ ≤ ∑ k ∈ Finset.Icc 1 t, A * tdRateWeight γ η t k := by
      apply Finset.sum_le_sum
      intro k hk
      have hi := Finset.mem_Icc.mp hk
      have hn := tdRateWeight_nonneg γ η t k hγ hγ1.le hη
      have hu := hcap k hi.1 hi.2
      nlinarith
    _ = A * (∑ k ∈ Finset.Icc 1 t, tdRateWeight γ η t k) := by rw [Finset.mul_sum]
    _ ≤ A * (1 / (1 - γ)) := mul_le_mul_of_nonneg_left (tdRateWeight_sum_le_horizon γ η t hγ hγ1 hη) hA
    _ = A / (1 - γ) := by ring

end StatisticalRL.TemporalDifference
