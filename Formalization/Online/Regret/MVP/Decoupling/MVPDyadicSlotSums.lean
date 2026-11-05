import Formalization.Online.Regret.MVP.OnlineMVPDyadicTrigger
import Mathlib.Tactic

/-! exact dyadic-slot sums. Slots cover all zero-based visit ranks
starting at 2; the source's first two ranks remain separate terms. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators

/-- Source batch level j uses N=2^j samples and stays active for 2N visits. -/
theorem mvp_sum_dyadicSlots (J : ℕ) (f : ℕ → ℝ) :
    (∑ u ∈ Finset.range (2^(J+1)), f u) =
      f 0 + f 1 + ∑ j ∈ Finset.range J,
        ∑ i ∈ Finset.range (2*2^j), f (2*2^j+i) := by
  induction J with
  | zero => norm_num [Finset.sum_range_succ]
  | succ J ih =>
      have hp : 2^(J+1+1) = 2^(J+1)+2^(J+1) := by
        rw [pow_succ]
        omega
      rw [hp, Finset.sum_range_add, ih, Finset.sum_range_succ]
      have hb : 2^(J+1) = 2*2^J := by simp [pow_succ, Nat.mul_comm]
      rw [hb]
      ring

/-- Exact extension by zero followed by the dyadic partition. There is no
unjustified extra visit when K is not a power of two. -/
theorem mvp_sum_dyadicSlots_zeroExtended (K J : ℕ) (hK : K ≤ 2^(J+1))
    (f : ℕ → ℝ) (hzero : ∀ u, K ≤ u → f u = 0) :
    (∑ u ∈ Finset.range K, f u) =
      f 0 + f 1 + ∑ j ∈ Finset.range J,
        ∑ i ∈ Finset.range (2*2^j), f (2*2^j+i) := by
  rw [← mvp_sum_dyadicSlots]
  apply Finset.sum_subset (Finset.range_mono hK)
  intro u _ hu
  exact hzero u (by simpa only [Finset.mem_range, not_lt] using hu)

theorem mvp_dyadicSlot_log2 (j i : ℕ) (hi : i < 2*2^j) :
    Nat.log2 (2*2^j+i) = j+1 := by
  apply onlineMVP_log2_eq_of_dyadic_bounds
  · simp only [pow_succ]
    omega
  · have hp : 2^(j+1+1) = 2*(2*2^j) := by simp [pow_succ]; ring
    rw [hp]
    omega

/-- The sum of all 2N slot coefficients 1/(16Nx) is J/(8x). -/
theorem mvp_dyadicSlot_weight_sum (J : ℕ) (x : ℝ) (hx : 0 < x) :
    (∑ j ∈ Finset.range J, ∑ _i ∈ Finset.range (2*2^j),
      (1 : ℝ)/(16*(2:ℝ)^j*x)) = (J : ℝ)/(8*x) := by
  have hinner (j : ℕ) :
      (∑ _i ∈ Finset.range (2*2^j), (1 : ℝ)/(16*(2:ℝ)^j*x)) = 1/(8*x) := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    push_cast
    field_simp
    ring
  simp_rw [hinner]
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  ring

theorem mvp_dyadicSlot_weight_budget (J : ℕ) (x : ℝ) (hx : 0 < x)
    (hJ : (J : ℝ) ≤ x) :
    (∑ j ∈ Finset.range J, ∑ _i ∈ Finset.range (2*2^j),
      (1 : ℝ)/(16*(2:ℝ)^j*x)) ≤ 1/8 := by
  rw [mvp_dyadicSlot_weight_sum J x hx]
  apply (div_le_iff₀ (by positivity : 0 < 8*x)).2
  linarith

/-- The two deterministic initial-rank charges fit in the source additive
budget with the slack left by the strengthened concentration bound. -/
theorem mvp_initialRanks_absorb (A I : ℝ) (hA : 0 ≤ A) (hI : 4 ≤ I) :
    A*I/8+2*A ≤ A*I := by
  have h := mul_nonneg hA (sub_nonneg.mpr hI)
  nlinarith only [h,hA]

end StatisticalRL.OnlineRL
