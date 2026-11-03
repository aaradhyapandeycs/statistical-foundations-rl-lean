import Formalization.ModelFree.TDIterateBounds
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.SpecialFunctions.Exp

/-! Exact TD learning-rate weights from def:eta-k-t. The initial weight at
(t,k)=(0,0) is one; out-of-range indices are zero. No rate theorem is assumed. -/
open scoped BigOperators
namespace StatisticalRL.TemporalDifference

/-- The TD contraction multiplier, with the source's effective discount gap. -/
def tdRateContraction (γ : ℝ) (η : ℕ → ℝ) (i : ℕ) : ℝ := 1 - η i * (1 - γ)

/-- Source η_k^(t), with the k=0 branch taking precedence at t=0.
Positive k=t has an empty suffix product and therefore equals η_t. -/
noncomputable def tdRateWeight (γ : ℝ) (η : ℕ → ℝ) (t k : ℕ) : ℝ :=
  if k ≤ t then (if k = 0 then 1 else η k) *
    ∏ i ∈ Finset.Icc (k + 1) t, tdRateContraction γ η i else 0

theorem tdRateWeight_initial (γ : ℝ) (η : ℕ → ℝ) (t : ℕ) :
    tdRateWeight γ η t 0 = ∏ i ∈ Finset.Icc 1 t, tdRateContraction γ η i := by
  simp [tdRateWeight]

theorem tdRateWeight_diagonal (γ : ℝ) (η : ℕ → ℝ) (t : ℕ) (ht : 0 < t) :
    tdRateWeight γ η t t = η t := by
  simp [tdRateWeight, ht.ne']

theorem tdRateWeight_out_of_range (γ : ℝ) (η : ℕ → ℝ) (t k : ℕ) (hk : t < k) :
    tdRateWeight γ η t k = 0 := by simp [tdRateWeight, Nat.not_le.mpr hk]

theorem tdRateContraction_bounds (γ : ℝ) (η : ℕ → ℝ) (i : ℕ)
    (hγ : 0 ≤ γ) (hγ1 : γ ≤ 1) (hη : 0 ≤ η i ∧ η i ≤ 1) :
    0 ≤ tdRateContraction γ η i ∧ tdRateContraction γ η i ≤ 1 := by
  unfold tdRateContraction
  have hh : 0 ≤ 1 - γ := sub_nonneg.mpr hγ1
  constructor
  · nlinarith [mul_nonneg (sub_nonneg.mpr hη.2) hh]
  · nlinarith [mul_nonneg hη.1 hh]

theorem tdRateWeight_nonneg (γ : ℝ) (η : ℕ → ℝ) (t k : ℕ)
    (hγ : 0 ≤ γ) (hγ1 : γ ≤ 1) (hη : ∀ i, 1 ≤ i → i ≤ t → 0 ≤ η i ∧ η i ≤ 1) :
    0 ≤ tdRateWeight γ η t k := by
  by_cases hk : k ≤ t
  · rw [tdRateWeight, if_pos hk]
    apply mul_nonneg
    · split_ifs with hzero
      · norm_num
      · exact (hη k (by omega) hk).1
    · apply Finset.prod_nonneg
      intro i hi
      have hi' := Finset.mem_Icc.mp hi
      exact (tdRateContraction_bounds γ η i hγ hγ1 (hη i (by omega) hi'.2)).1
  · simp [tdRateWeight, hk]

theorem tdRateWeight_le_rate (γ : ℝ) (η : ℕ → ℝ) (t k : ℕ)
    (hγ : 0 ≤ γ) (hγ1 : γ ≤ 1) (hk : 0 < k) (hkt : k ≤ t)
    (hη : ∀ i, 1 ≤ i → i ≤ t → 0 ≤ η i ∧ η i ≤ 1) :
    tdRateWeight γ η t k ≤ η k := by
  rw [tdRateWeight, if_pos hkt, if_neg hk.ne']
  have hp : (∏ i ∈ Finset.Icc (k + 1) t, tdRateContraction γ η i) ≤ 1 := by
    apply Finset.prod_le_one
    · intro i hi
      have hi' := Finset.mem_Icc.mp hi
      exact (tdRateContraction_bounds γ η i hγ hγ1 (hη i (by omega) hi'.2)).1
    · intro i hi
      have hi' := Finset.mem_Icc.mp hi
      exact (tdRateContraction_bounds γ η i hγ hγ1 (hη i (by omega) hi'.2)).2
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hp (hη k hk hkt).1

/-- A non-constant-rate product estimate; its genuine contraction lower bound
must be derived from the actual finite schedule before any source T^-2 claim. -/
theorem tdRateWeight_le_exp (γ : ℝ) (η : ℕ → ℝ) (t k : ℕ) (α : ℝ)
    (hγ : 0 ≤ γ) (hγ1 : γ ≤ 1) (hkt : k ≤ t)
    (hη : ∀ i, 1 ≤ i → i ≤ t → 0 ≤ η i ∧ η i ≤ 1)
    (hα : ∀ i, k < i → i ≤ t → α ≤ η i * (1 - γ)) :
    tdRateWeight γ η t k ≤ Real.exp (-α * (t - k : ℕ)) := by
  have hprod : (∏ i ∈ Finset.Icc (k + 1) t, tdRateContraction γ η i) ≤
      ∏ _i ∈ Finset.Icc (k + 1) t, Real.exp (-α) := by
    apply Finset.prod_le_prod
    · intro i hi
      have hi' := Finset.mem_Icc.mp hi
      exact (tdRateContraction_bounds γ η i hγ hγ1 (hη i (by omega) hi'.2)).1
    · intro i hi
      have hi' := Finset.mem_Icc.mp hi
      have hh := hα i (by omega) hi'.2
      have he := Real.add_one_le_exp (-α)
      unfold tdRateContraction
      linarith
  have hcard : (Finset.Icc (k + 1) t).card = t - k := by rw [Nat.card_Icc]; omega
  have he : (∏ _i ∈ Finset.Icc (k + 1) t, Real.exp (-α)) = Real.exp (-α * (t - k : ℕ)) := by
    rw [Finset.prod_const, hcard, ← Real.exp_nat_mul]
    congr 1
    ring
  rw [he] at hprod
  have hinit : (if k = 0 then (1 : ℝ) else η k) ≤ 1 := by
    split_ifs with hzero
    · exact le_rfl
    · exact (hη k (by omega) hkt).2
  have hp0 : 0 ≤ ∏ i ∈ Finset.Icc (k + 1) t, tdRateContraction γ η i := by
    apply Finset.prod_nonneg
    intro i hi
    have hi' := Finset.mem_Icc.mp hi
    exact (tdRateContraction_bounds γ η i hγ hγ1 (hη i (by omega) hi'.2)).1
  rw [tdRateWeight, if_pos hkt]
  calc
    _ ≤ 1 * (∏ i ∈ Finset.Icc (k + 1) t, tdRateContraction γ η i) :=
      mul_le_mul_of_nonneg_right hinit hp0
    _ ≤ _ := by simpa only [one_mul] using hprod

end StatisticalRL.TemporalDifference
