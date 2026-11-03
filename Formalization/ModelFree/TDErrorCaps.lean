import Formalization.ModelFree.TDActualErrorUnroll
import Formalization.ModelFree.TDLearningWeights

/-! Deterministic actual TD propagator and fixed-terminal increment caps.
No conditional variance or concentration conclusion is assumed. -/
open scoped BigOperators
namespace StatisticalRL.TemporalDifference
variable {State Action : Type*} [Fintype State] [Fintype Action]

theorem tdIterate_eq_of_rates_agree (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (η ζ : ℕ → ℝ) (samples : ℕ → State → State)
    (V₀ : State → ℝ) (t : ℕ) (he : ∀ k, 1 ≤ k → k ≤ t → η k = ζ k) :
    tdIterate M π η samples V₀ t = tdIterate M π ζ samples V₀ t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have hh := ih (fun k hk hkt ↦ he k hk (by omega))
    funext s
    simp only [tdIterate, hh, he (t + 1) (by omega) (by omega)]

/-- Source iterate bounds without an artificial condition on the unused η0. -/
theorem tdIterate_bounds_positive_rates (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (η : ℕ → ℝ) (samples : ℕ → State → State)
    (V₀ : State → ℝ) (h₀ : ∀ s, 0 ≤ V₀ s ∧ V₀ s ≤ M.effectiveHorizon)
    (t : ℕ) (hη : ∀ i, 1 ≤ i → i ≤ t → 0 ≤ η i ∧ η i ≤ 1) (s : State) :
    0 ≤ tdIterate M π η samples V₀ t s ∧ tdIterate M π η samples V₀ t s ≤ M.effectiveHorizon := by
  let ζ : ℕ → ℝ := fun i ↦ if i = 0 then 0 else η i
  have hz : ∀ i, i ≤ t → 0 ≤ ζ i ∧ ζ i ≤ 1 := by
    intro i hit
    by_cases hi : i = 0
    · simp [ζ, hi]
    · simpa only [ζ, if_neg hi] using hη i (by omega) hit
  have hh := tdIterate_bounds M π ζ samples V₀ h₀ t hz s
  have he := tdIterate_eq_of_rates_agree M π η ζ samples V₀ t (by
    intro i hi hit
    simp [ζ, show i ≠ 0 by omega])
  rw [← he] at hh
  exact hh

theorem tdIterate_norm_le_positive_rates (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (η : ℕ → ℝ) (samples : ℕ → State → State)
    (V₀ : State → ℝ) (h₀ : ∀ s, 0 ≤ V₀ s ∧ V₀ s ≤ M.effectiveHorizon)
    (t : ℕ) (hη : ∀ i, 1 ≤ i → i ≤ t → 0 ≤ η i ∧ η i ≤ 1) :
    ‖tdIterate M π η samples V₀ t‖ ≤ M.effectiveHorizon := by
  apply (pi_norm_le_iff_of_nonneg M.effectiveHorizon_nonneg).2
  intro s
  have hh := tdIterate_bounds_positive_rates M π η samples V₀ h₀ t hη s
  simpa only [Real.norm_eq_abs, abs_of_nonneg hh.1] using hh.2

/-- The actual true policy row contracts the full Pi norm with exactly the
source scalar multiplier; no matrix norm orientation convention is needed. -/
theorem tdErrorTransition_norm_le (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (η : ℕ → ℝ) (i : ℕ) (hi : 0 ≤ η i ∧ η i ≤ 1)
    (U : State → ℝ) : ‖tdErrorTransition M π η i U‖ ≤ tdRateContraction M.discount η i * ‖U‖ := by
  have hc := tdRateContraction_bounds M.discount η i M.discount_nonneg M.discount_lt_one.le hi
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg hc.1 (norm_nonneg U))).2
  intro s
  have hU : |U s| ≤ ‖U‖ := norm_le_pi_norm U s
  have hE : |(M.policyTransition π s).expectation U| ≤ ‖U‖ :=
    (M.policyTransition π s).abs_expectation_le (fun t ↦ norm_le_pi_norm U t)
  change |(1 - η i) * U s + η i * M.discount * (M.policyTransition π s).expectation U| ≤ _
  have htri := abs_add_le ((1 - η i) * U s) (η i * M.discount * (M.policyTransition π s).expectation U)
  rw [abs_mul, abs_mul, abs_of_nonneg (sub_nonneg.mpr hi.2),
    abs_of_nonneg (mul_nonneg hi.1 M.discount_nonneg)] at htri
  have h1 := mul_le_mul_of_nonneg_left hU (sub_nonneg.mpr hi.2)
  have h2 := mul_le_mul_of_nonneg_left hE (mul_nonneg hi.1 M.discount_nonneg)
  unfold tdRateContraction
  nlinarith

/-- Chronological products of the actual error transitions have the exact
scalar-product norm upper bound used in source (TD-L1-norm). -/
theorem tdErrorPropagate_norm_le (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (η : ℕ → ℝ) (start t : ℕ) (hstart : start ≤ t)
    (hη : ∀ i, 1 ≤ i → i ≤ t → 0 ≤ η i ∧ η i ≤ 1) (U : State → ℝ) :
    ‖tdErrorPropagate M π η start t U‖ ≤
      (∏ i ∈ Finset.Icc (start + 1) t, tdRateContraction M.discount η i) * ‖U‖ := by
  induction t with
  | zero =>
    have hs : start = 0 := by omega
    subst start
    simp [tdErrorPropagate]
  | succ t ih =>
    by_cases hs : start ≤ t
    · have hh := ih hs (fun i hi hit ↦ hη i hi (by omega))
      have hstep := tdErrorTransition_norm_le M π η (t + 1) (hη (t + 1) (by omega) le_rfl)
        (tdErrorPropagate M π η start t U)
      have hc := (tdRateContraction_bounds M.discount η (t + 1) M.discount_nonneg M.discount_lt_one.le
        (hη (t + 1) (by omega) le_rfl)).1
      rw [tdErrorPropagate_succ M π η start t hs]
      apply hstep.trans
      have hp := mul_le_mul_of_nonneg_left hh hc
      rw [Finset.prod_Icc_succ_top (by omega : start + 1 ≤ t + 1)]
      nlinarith
    · have he : start = t + 1 := by omega
      subst start
      rw [tdErrorPropagate_diagonal]
      simp

/-- Raw transition noise is bounded for every realized synchronous array. -/
theorem tdCenteredRowNoise_norm_le (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (η : ℕ → ℝ) (samples : ℕ → State → State)
    (V₀ : State → ℝ) (k : ℕ) :
    ‖tdCenteredRowNoise M π η samples V₀ (k + 1)‖ ≤ 2 * ‖tdIterate M π η samples V₀ k‖ := by
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg (by norm_num) (norm_nonneg _))).2
  intro s
  have hv : |tdIterate M π η samples V₀ k (samples (k + 1) s)| ≤ ‖tdIterate M π η samples V₀ k‖ :=
    by simpa only [Real.norm_eq_abs] using
      (norm_le_pi_norm (tdIterate M π η samples V₀ k) (samples (k + 1) s))
  have he := (M.policyTransition π s).abs_expectation_le
    (fun t ↦ show |tdIterate M π η samples V₀ k t| ≤ ‖tdIterate M π η samples V₀ k‖ from norm_le_pi_norm (tdIterate M π η samples V₀ k) t)
  change |tdIterate M π η samples V₀ k (samples (k + 1) s) -
    (M.policyTransition π s).expectation (tdIterate M π η samples V₀ k)| ≤ _
  have hh := abs_sub_le (tdIterate M π η samples V₀ k (samples (k + 1) s)) 0
    ((M.policyTransition π s).expectation (tdIterate M π η samples V₀ k))
  simp only [sub_zero, zero_sub, abs_neg] at hh
  linarith

/-- Source fixed-terminal innovation cap in terms of the exact proved weight.
The terminal t is retained; no single terminal-independent process is invented. -/
theorem tdWeightedErrorIncrement_norm_le (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (η : ℕ → ℝ) (samples : ℕ → State → State)
    (V₀ : State → ℝ) (t k : ℕ) (hk : 1 ≤ k) (hkt : k ≤ t)
    (hη : ∀ i, 1 ≤ i → i ≤ t → 0 ≤ η i ∧ η i ≤ 1) :
    ‖tdWeightedErrorIncrement M π η samples V₀ t k‖ ≤
      2 * M.discount * tdRateWeight M.discount η t k * ‖tdIterate M π η samples V₀ (k - 1)‖ := by
  cases k with
  | zero => omega
  | succ k =>
    have hc : 0 ≤ M.discount * η (k + 1) := mul_nonneg M.discount_nonneg (hη (k + 1) hk hkt).1
    rw [tdWeightedErrorIncrement_source_form M π η samples V₀ t (k + 1) hk hkt]
    change ‖(M.discount * η (k + 1)) • tdErrorPropagate M π η (k + 1) t
      (tdCenteredRowNoise M π η samples V₀ (k + 1))‖ ≤ _
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hc]
    have hp := tdErrorPropagate_norm_le M π η (k + 1) t hkt hη
      (tdCenteredRowNoise M π η samples V₀ (k + 1))
    have hn := tdCenteredRowNoise_norm_le M π η samples V₀ k
    have hprod : 0 ≤ ∏ i ∈ Finset.Icc (k + 1 + 1) t, tdRateContraction M.discount η i := by
      apply Finset.prod_nonneg
      intro i hi
      have hi' := Finset.mem_Icc.mp hi
      exact (tdRateContraction_bounds M.discount η i M.discount_nonneg M.discount_lt_one.le
        (hη i (by omega) hi'.2)).1
    have h1 := mul_le_mul_of_nonneg_left hp hc
    have h2 := mul_le_mul_of_nonneg_left hn (mul_nonneg hc hprod)
    rw [tdRateWeight, if_pos hkt, if_neg (by omega : k + 1 ≠ 0)]
    simp only [Nat.add_sub_cancel]
    nlinarith

/-- The source's deterministic martingale-increment envelope, without η0.
Conditional centering and variance are separate obligations. -/
theorem tdWeightedErrorIncrement_norm_le_horizon (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (η : ℕ → ℝ) (samples : ℕ → State → State)
    (V₀ : State → ℝ) (h₀ : ∀ s, 0 ≤ V₀ s ∧ V₀ s ≤ M.effectiveHorizon)
    (t k : ℕ) (hk : 1 ≤ k) (hkt : k ≤ t)
    (hη : ∀ i, 1 ≤ i → i ≤ t → 0 ≤ η i ∧ η i ≤ 1) :
    ‖tdWeightedErrorIncrement M π η samples V₀ t k‖ ≤
      2 * M.discount * tdRateWeight M.discount η t k * M.effectiveHorizon := by
  have hw := tdRateWeight_nonneg M.discount η t k M.discount_nonneg M.discount_lt_one.le hη
  have hv := tdIterate_norm_le_positive_rates M π η samples V₀ h₀ (k - 1)
    (fun i hi hit ↦ hη i hi (by omega))
  exact (tdWeightedErrorIncrement_norm_le M π η samples V₀ t k hk hkt hη).trans
    (mul_le_mul_of_nonneg_left hv (mul_nonneg (mul_nonneg (by norm_num) M.discount_nonneg) hw))

end StatisticalRL.TemporalDifference
