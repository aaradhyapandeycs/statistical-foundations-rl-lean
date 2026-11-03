import Formalization.Generative.PolicyEvaluationVarianceResolvent

/-!
# Unrolling the auxiliary policy-evaluation error recursion

Algebraic bridge for `eqn:Chopin` in the generative-model chapter. The input
inequalities are the separately established recursive error and value bounds;
this file does not assert the concentration event or the sharp theorem.
-/

open scoped BigOperators

namespace StatisticalRL.ModelBasedPolicyEvaluation

/-- Unroll the source's finite error recursion, retaining its terminal error
and its exact finite geometric sum. -/
theorem auxiliary_error_recursion_unroll
    (E V : ℕ → ℝ) (b₁ b₂ b₃ : ℝ) (m : ℕ)
    (hb₁ : 0 ≤ b₁) (hb₂ : 0 ≤ b₂)
    (hstep : ∀ l < m, E l ≤ b₁ * E (l + 1) + b₂ * V l)
    (hvalue : ∀ l < m, V l ≤ b₃ ^ l * V 0) :
    E 0 ≤ b₁ ^ m * E m + b₂ * (∑ l ∈ Finset.range m, (b₁ * b₃) ^ l) * V 0 := by
  have haux : ∀ n ≤ m,
      E 0 ≤ b₁ ^ n * E n + b₂ * (∑ l ∈ Finset.range n, (b₁ * b₃) ^ l) * V 0 := by
    intro n hn
    induction n with
    | zero => simp
    | succ n ih =>
      have hn' : n < m := Nat.lt_of_succ_le hn
      have hi := ih (Nat.le_of_lt hn')
      have hs := hstep n hn'
      have hv := hvalue n hn'
      have hb : 0 ≤ b₁ ^ n := pow_nonneg hb₁ _
      have hlocal : E n ≤ b₁ * E (n + 1) + b₂ * (b₃ ^ n * V 0) := by
        have := mul_le_mul_of_nonneg_left hv hb₂
        linarith
      calc
        E 0 ≤ b₁ ^ n * E n + b₂ * (∑ l ∈ Finset.range n, (b₁ * b₃) ^ l) * V 0 := hi
        _ ≤ b₁ ^ n * (b₁ * E (n + 1) + b₂ * (b₃ ^ n * V 0)) +
            b₂ * (∑ l ∈ Finset.range n, (b₁ * b₃) ^ l) * V 0 :=
          add_le_add_left (mul_le_mul_of_nonneg_left hlocal hb) _
        _ = b₁ ^ (n + 1) * E (n + 1) +
            b₂ * (∑ l ∈ Finset.range (n + 1), (b₁ * b₃) ^ l) * V 0 := by
          rw [Finset.sum_range_succ, mul_pow, pow_succ]
          ring
  exact haux m le_rfl

/-- The finite geometric factor used in the source's Step 5 is at most two
when its ratio lies in `[0, 1/2]`. -/
theorem auxiliary_geometric_sum_le_two (q : ℝ) (m : ℕ)
    (hq : 0 ≤ q) (hqhalf : q ≤ 1 / 2) :
    (∑ l ∈ Finset.range m, q ^ l) ≤ 2 := by
  have hsum : 0 ≤ ∑ l ∈ Finset.range m, q ^ l :=
    Finset.sum_nonneg (fun l _ ↦ pow_nonneg hq l)
  have hpow : 0 ≤ q ^ m := pow_nonneg hq m
  have hgeom := geom_sum_mul_neg q m
  nlinarith

/-- The preceding finite recursion with the source's geometric factor controlled. -/
theorem auxiliary_error_recursion_unroll_half
    (E V : ℕ → ℝ) (b₁ b₂ b₃ : ℝ) (m : ℕ)
    (hb₁ : 0 ≤ b₁) (hb₂ : 0 ≤ b₂) (hV0 : 0 ≤ V 0)
    (hq : 0 ≤ b₁ * b₃) (hqhalf : b₁ * b₃ ≤ 1 / 2)
    (hstep : ∀ l < m, E l ≤ b₁ * E (l + 1) + b₂ * V l)
    (hvalue : ∀ l < m, V l ≤ b₃ ^ l * V 0) :
    E 0 ≤ b₁ ^ m * E m + 2 * b₂ * V 0 := by
  have h := auxiliary_error_recursion_unroll E V b₁ b₂ b₃ m hb₁ hb₂ hstep hvalue
  have hg := auxiliary_geometric_sum_le_two (b₁ * b₃) m hq hqhalf
  have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hg hb₂) hV0
  nlinarith

/-- True and empirical trajectory values both lie in the same horizon interval. -/
theorem trajectoryValue_difference_le_horizon
    {State Action : Type*} [Fintype State] [Fintype Action]
    (M Mhat : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (hγ : Mhat.discount = M.discount) :
    ‖Mhat.trajectoryExpectedValue π - M.trajectoryExpectedValue π‖ ≤
      1 / (1 - M.discount) := by
  have hd : 0 < 1 - M.discount := sub_pos.mpr M.discount_lt_one
  have hB : 0 ≤ 1 / (1 - M.discount) := by positivity
  apply (pi_norm_le_iff_of_nonneg hB).2
  intro s
  have htrue := M.trajectoryExpectedValue_bounds π s
  have hhat := Mhat.trajectoryExpectedValue_bounds π s
  rw [hγ] at hhat
  simp only [Pi.sub_apply, Real.norm_eq_abs]
  apply abs_le.mpr
  constructor <;> linarith

/-- A deterministic small-sample bound that can fill the gap between the
source's displayed large-sample requirement and its final stated threshold.
This is a numerical estimate and makes no probabilistic claim. -/
theorem trajectoryValue_small_sample_bound
    {State Action : Type*} [Fintype State] [Fintype Action]
    (M Mhat : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (hγ : Mhat.discount = M.discount) (β N : ℝ) (hβ : 0 ≤ β) (hN : 0 < N)
    (hsmall : N ≤ 72 * β / (1 - M.discount)) :
    ‖Mhat.trajectoryExpectedValue π - M.trajectoryExpectedValue π‖ ≤
      3 * Real.sqrt (8 * β / ((1 - M.discount) ^ 3 * N)) := by
  let h : ℝ := 1 - M.discount
  have hh : 0 < h := sub_pos.mpr M.discount_lt_one
  have hsize : N * h ≤ 72 * β := (le_div_iff₀ hh).mp hsmall
  have harg : 0 ≤ 8 * β / (h ^ 3 * N) := by positivity
  have hsquare : (1 / h) ^ 2 ≤ 9 * (8 * β / (h ^ 3 * N)) := by
    have hden : 0 < h ^ 3 * N := by positivity
    rw [← mul_div_assoc]
    apply (le_div_iff₀ hden).2
    field_simp
    nlinarith
  have hsqrt := Real.sq_sqrt harg
  have hroot : 1 / h ≤ 3 * Real.sqrt (8 * β / (h ^ 3 * N)) := by
    have hr := Real.sqrt_nonneg (8 * β / (h ^ 3 * N))
    nlinarith
  exact (trajectoryValue_difference_le_horizon M Mhat π hγ).trans hroot

end StatisticalRL.ModelBasedPolicyEvaluation
