import Formalization.ModelFree.TDSquareEnergy
import Formalization.ModelFree.TDPropagatorRows
import Formalization.ModelFree.TDWeightMass

/-! Deterministic helpers for the sharp TD
square-energy telescope after source Lemma 4.4. This file contains no
conditional-expectation or stochastic-concentration conclusion. -/
set_option maxHeartbeats 1000000
open scoped BigOperators
namespace StatisticalRL.TemporalDifference

variable {State Action : Type*} [Fintype State] [Fintype Action]

/-- A single source error transition preserves pointwise order when the
source step size is in `[0,1]`. -/
theorem tdErrorTransition_mono (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (η : ℕ → ℝ) (i : ℕ)
    (hη : 0 ≤ η i ∧ η i ≤ 1) (U V : State → ℝ)
    (hUV : ∀ s, U s ≤ V s) :
    ∀ s, tdErrorTransition M π η i U s ≤ tdErrorTransition M π η i V s := by
  intro s
  unfold tdErrorTransition
  have hrow := (M.policyTransition π s).expectation_mono hUV
  have h1 := mul_le_mul_of_nonneg_left (hUV s) (sub_nonneg.mpr hη.2)
  have h2 := mul_le_mul_of_nonneg_left hrow
    (mul_nonneg hη.1 M.discount_nonneg)
  linarith

/-- Chronological TD propagation preserves pointwise order under the
positive-index source rate bounds. -/
theorem tdErrorPropagate_mono (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (η : ℕ → ℝ) (start t : ℕ)
    (hη : ∀ i, 1 ≤ i → i ≤ t → 0 ≤ η i ∧ η i ≤ 1)
    (U V : State → ℝ) (hUV : ∀ s, U s ≤ V s) :
    ∀ s, tdErrorPropagate M π η start t U s ≤
      tdErrorPropagate M π η start t V s := by
  induction t generalizing start with
  | zero => exact hUV
  | succ t ih =>
    by_cases hst : start ≤ t
    · rw [tdErrorPropagate_succ M π η start t hst]
      rw [tdErrorPropagate_succ M π η start t hst]
      exact tdErrorTransition_mono M π η (t + 1)
        (hη (t + 1) (by omega) le_rfl) _ _ (ih start
          (fun i hi1 hit ↦ hη i hi1 (by omega)))
    · simpa only [tdErrorPropagate, if_neg hst] using hUV

/-- Propagation splits exactly at an intermediate source time. The operator
applies transitions `start+1,...,mid` first, then `mid+1,...,terminal`; this
fixes chronological order without commuting matrices. -/
theorem tdErrorPropagate_comp (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (η : ℕ → ℝ)
    (start mid terminal : ℕ) (hsm : start ≤ mid) (hmt : mid ≤ terminal)
    (U : State → ℝ) :
    tdErrorPropagate M π η start terminal U =
      tdErrorPropagate M π η mid terminal
        (tdErrorPropagate M π η start mid U) := by
  induction terminal with
  | zero =>
    have hs : start = 0 := by omega
    subst start
    have hm : mid = 0 := by omega
    subst mid
    rfl
  | succ terminal ih =>
    by_cases hmid : mid ≤ terminal
    · have hstart : start ≤ terminal := hsm.trans hmid
      rw [tdErrorPropagate_succ M π η start terminal hstart,
        tdErrorPropagate_succ M π η mid terminal hmid,
        ih hmid]
    · have heq : mid = terminal + 1 := by omega
      subst mid
      rw [tdErrorPropagate_diagonal]

/-- Splitting off the first chronological update gives the product-composition
identity used by the square-energy telescope. -/
theorem tdErrorPropagate_succ_start (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (η : ℕ → ℝ) (start terminal : ℕ)
    (hst : start < terminal) (U : State → ℝ) :
    tdErrorPropagate M π η start terminal U =
      tdErrorPropagate M π η (start + 1) terminal
        (tdErrorTransition M π η (start + 1) U) := by
  have hcomp := tdErrorPropagate_comp M π η start (start + 1) terminal
    (by omega) (by omega) U
  rw [tdErrorPropagate_succ M π η start start (Nat.le_refl start),
    tdErrorPropagate_diagonal] at hcomp
  exact hcomp

/-- The weighted square-difference sum is an exact telescoping identity for
the actual chronological propagator. `X` is an arbitrary vector sequence;
no martingale or sampling fact is assumed. -/
theorem tdWeightedSquareEnergy_telescope (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (η : ℕ → ℝ) (m t : ℕ)
    (hmt : m ≤ t) (X : ℕ → State → ℝ) :
    (∑ k ∈ Finset.Icc (m + 1) t,
      tdErrorPropagate M π η k t
        (tdErrorTransition M π η k (X (k - 1)) - X k)) =
      tdErrorPropagate M π η m t (X m) - X t := by
  induction t, hmt using Nat.le_induction with
  | base =>
    simp [tdErrorPropagate_diagonal]
  | succ t hmt ih =>
    rw [Finset.sum_Icc_succ_top (by omega : m + 1 ≤ t + 1)]
    have hprev :
        (∑ k ∈ Finset.Icc (m + 1) t,
          tdErrorPropagate M π η k (t + 1)
            (tdErrorTransition M π η k (X (k - 1)) - X k)) =
          tdErrorTransition M π η (t + 1)
            (∑ k ∈ Finset.Icc (m + 1) t,
              tdErrorPropagate M π η k t
                (tdErrorTransition M π η k (X (k - 1)) - X k)) := by
      rw [tdErrorTransition_sum]
      apply Finset.sum_congr rfl
      intro k hk
      have hk' := Finset.mem_Icc.mp hk
      exact tdErrorPropagate_succ M π η k t hk'.2 _
    have hlast : tdErrorPropagate M π η (t + 1) (t + 1)
          (tdErrorTransition M π η (t + 1) (X t) - X (t + 1)) =
        tdErrorTransition M π η (t + 1) (X t) - X (t + 1) :=
      tdErrorPropagate_diagonal M π η (t + 1) _
    have hx : X (t + 1 - 1) = X t := by congr 1
    rw [hx, hprev, ih, tdErrorPropagate_succ M π η m t hmt, hlast]
    have hsub (U V : State → ℝ) :
        tdErrorTransition M π η (t + 1) (U - V) =
          tdErrorTransition M π η (t + 1) U - tdErrorTransition M π η (t + 1) V := by
      rw [show U - V = U + (fun s ↦ (-1 : ℝ) * V s) by
        ext s
        simp only [Pi.sub_apply, Pi.add_apply]
        ring]
      rw [tdErrorTransition_add, tdErrorTransition_mul]
      ext s
      simp only [Pi.add_apply, Pi.sub_apply]
      ring
    rw [hsub]
    ext s
    simp only [Pi.sub_apply, Pi.add_apply]
    ring

/-- The actual propagated square vector stays below `H^2` if the input does;
this is a deterministic interval statement, not a variance bound. -/
theorem tdErrorPropagate_le_const_of_interval
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (η : ℕ → ℝ) (start t : ℕ) (hst : start ≤ t)
    (hη : ∀ i, 1 ≤ i → i ≤ t → 0 ≤ η i ∧ η i ≤ 1)
    (U : State → ℝ) (H : ℝ) (hH : 0 ≤ H)
    (hU : ∀ s, 0 ≤ U s ∧ U s ≤ H) :
    ∀ s, 0 ≤ tdErrorPropagate M π η start t U s ∧
      tdErrorPropagate M π η start t U s ≤ H := by
  have hzero : ∀ s, 0 ≤ tdErrorPropagate M π η start t U s :=
    tdErrorPropagate_nonneg M π η start t hη U (fun s ↦ (hU s).1)
  have hupper : ∀ s, tdErrorPropagate M π η start t U s ≤ H := by
    intro s
    have hmono := tdErrorPropagate_mono M π η start t hη U (fun _ ↦ H)
      (fun x ↦ (hU x).2) s
    have hconst := congrFun (tdErrorPropagate_const M π η start t hst H) s
    have hprod : (∏ i ∈ Finset.Icc (start + 1) t,
        tdRateContraction M.discount η i) ≤ 1 := by
      apply Finset.prod_le_one
      · intro i hi
        have hi' := Finset.mem_Icc.mp hi
        exact (tdRateContraction_bounds M.discount η i M.discount_nonneg
          M.discount_lt_one.le (hη i (by omega) hi'.2)).1
      · intro i hi
        have hi' := Finset.mem_Icc.mp hi
        exact (tdRateContraction_bounds M.discount η i M.discount_nonneg
          M.discount_lt_one.le (hη i (by omega) hi'.2)).2
    calc
      tdErrorPropagate M π η start t U s ≤
          tdErrorPropagate M π η start t (fun _ ↦ H) s := hmono
      _ = (∏ i ∈ Finset.Icc (start + 1) t,
          tdRateContraction M.discount η i) * H := hconst
      _ ≤ 1 * H := mul_le_mul_of_nonneg_right hprod hH
      _ = H := by ring
  exact fun s ↦ ⟨hzero s, hupper s⟩

/-- Deterministic upper bound on the telescoping endpoint term from source
`eq:TD-variance-energy-bound`. -/
theorem tdWeightedSquareEnergy_endpoint_le
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (η : ℕ → ℝ) (m t : ℕ) (hmt : m ≤ t)
    (hη : ∀ i, 1 ≤ i → i ≤ t → 0 ≤ η i ∧ η i ≤ 1)
    (H : ℝ) (_hH : 0 ≤ H) (X : ℕ → State → ℝ)
    (hF : ∀ n s, 0 ≤ X n s ∧ X n s ≤ H ^ 2) :
    ∀ s, tdErrorPropagate M π η m t (X m) s - X t s ≤ H ^ 2 := by
  have hprop := tdErrorPropagate_le_const_of_interval M π η m t hmt hη
    (X m) (H ^ 2) (sq_nonneg H) (fun s ↦ hF m s)
  intro s
  have htail := (hF t s).1
  linarith [hprop s]

end StatisticalRL.TemporalDifference
