import Formalization.Probability.FiniteMarkov.Definitions
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/-! # Finite Markov chains: matrix powers, stationarity and mixing distances

Ingredients (M1)–(M3) of the plan for Theorem 4.12: `μ K^t = μ`, the monotonicity of
`d(t) = max_x TV(K^t(x,·), μ)`, the bound `d(s+t) ≤ 2 d(s) d(t)` and the summability
`∑_{m<N} d(m) ≤ 2 t̄` when `d(t̄) ≤ 1/4`. Everything is an explicit finite sum. -/

open scoped BigOperators
open Finset

set_option linter.unusedSectionVars false

namespace StatisticalRL.FiniteMarkov

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- Row-stochastic matrix. -/
structure IsStochastic (K : X → X → ℝ) : Prop where
  nonneg : ∀ x y, 0 ≤ K x y
  row_sum : ∀ x, ∑ y, K x y = 1

/-- Probability vector. -/
structure IsProb (p : X → ℝ) : Prop where
  nonneg : ∀ x, 0 ≤ p x
  sum_eq : ∑ x, p x = 1

variable {K : X → X → ℝ}

theorem kpow_zero_apply (x y : X) : kpow K 0 x y = if x = y then 1 else 0 := rfl

theorem kpow_succ_apply (t : ℕ) (x y : X) : kpow K (t + 1) x y = ∑ w, K x w * kpow K t w y := rfl

theorem kpow_nonneg (hK : IsStochastic K) (t : ℕ) (x y : X) : 0 ≤ kpow K t x y := by
  induction t generalizing x with
  | zero => simp only [kpow_zero_apply]; split_ifs <;> norm_num
  | succ t ih => exact sum_nonneg fun w _ ↦ mul_nonneg (hK.nonneg x w) (ih w)

theorem kpow_row_sum (hK : IsStochastic K) (t : ℕ) (x : X) : ∑ y, kpow K t x y = 1 := by
  induction t generalizing x with
  | zero => simp [kpow_zero_apply]
  | succ t ih =>
    simp only [kpow_succ_apply]
    rw [sum_comm]
    simp_rw [← mul_sum, ih, mul_one]
    exact hK.row_sum x

theorem kpow_isProb (hK : IsStochastic K) (t : ℕ) (x : X) : IsProb (kpow K t x) :=
  ⟨kpow_nonneg hK t x, kpow_row_sum hK t x⟩

theorem kpow_add (s t : ℕ) (x y : X) :
    kpow K (s + t) x y = ∑ w, kpow K s x w * kpow K t w y := by
  induction s generalizing x with
  | zero => simp [kpow_zero_apply]
  | succ s ih =>
    rw [Nat.succ_add, kpow_succ_apply]
    simp_rw [ih, kpow_succ_apply, mul_sum, sum_mul]
    rw [sum_comm]
    refine sum_congr rfl fun w _ ↦ sum_congr rfl fun v _ ↦ by ring

/-- Stationarity propagates to all powers: `μ K^t = μ`. -/
theorem stationary_kpow {μ : X → ℝ} (hμ : ∀ y, ∑ x, μ x * K x y = μ y) (t : ℕ) (y : X) :
    ∑ x, μ x * kpow K t x y = μ y := by
  induction t generalizing y with
  | zero => simp [kpow_zero_apply]
  | succ t ih =>
    simp_rw [kpow_succ_apply, mul_sum]
    rw [sum_comm]
    simp_rw [← mul_assoc, ← sum_mul, hμ, ih]

/-! ## Total variation -/

theorem tvDist_nonneg (p q : X → ℝ) : 0 ≤ tvDist p q := by
  unfold tvDist; positivity

theorem tvDist_le_one {p q : X → ℝ} (hp : IsProb p) (hq : IsProb q) : tvDist p q ≤ 1 := by
  unfold tvDist
  have : ∑ y, |p y - q y| ≤ ∑ y, (p y + q y) :=
    sum_le_sum fun y _ ↦ by
      rw [abs_le]; constructor <;> linarith [hp.nonneg y, hq.nonneg y]
  rw [sum_add_distrib, hp.sum_eq, hq.sum_eq] at this
  linarith

/-- A single coordinate of a zero-sum difference is bounded by the total variation. -/
theorem abs_sub_le_tvDist {p q : X → ℝ} (hpq : ∑ y, p y = ∑ y, q y) (z : X) :
    |p z - q z| ≤ tvDist p q := by
  unfold tvDist
  have h0 : ∑ y, (p y - q y) = 0 := by rw [sum_sub_distrib, hpq, sub_self]
  have h1 := add_sum_erase univ (fun y ↦ p y - q y) (mem_univ z)
  have h2 := add_sum_erase univ (fun y ↦ |p y - q y|) (mem_univ z)
  have h3 := abs_sum_le_sum_abs (fun y ↦ p y - q y) (univ.erase z)
  have h4 : |p z - q z| = |∑ y ∈ univ.erase z, (p y - q y)| := by
    rw [show ∑ y ∈ univ.erase z, (p y - q y) = -(p z - q z) by linarith, abs_neg]
  linarith

/-- The `L¹` norm of `D K^t` for a zero-sum `D`. -/
theorem sum_abs_mul_kpow_le {D : X → ℝ} (hD : ∑ w, D w = 0) (μ : X → ℝ) (t : ℕ) (c : ℝ)
    (hc : ∀ w, tvDist (kpow K t w) μ ≤ c) :
    ∑ y, |∑ w, D w * kpow K t w y| ≤ (∑ w, |D w|) * (2 * c) := by
  set g : X → ℝ := fun y ↦ ∑ w, D w * kpow K t w y
  let sgn : X → ℝ := fun y ↦ if 0 ≤ g y then 1 else -1
  have hsg : ∀ y, |g y| = sgn y * g y := fun y ↦ by
    by_cases h : 0 ≤ g y
    · simp [sgn, h, abs_of_nonneg h]
    · simp [sgn, h, abs_of_neg (lt_of_not_ge h)]
  have hsabs : ∀ y, |sgn y| = 1 := fun y ↦ by by_cases h : 0 ≤ g y <;> simp [sgn, h]
  calc ∑ y, |g y| = ∑ y, sgn y * g y := sum_congr rfl fun y _ ↦ hsg y
    _ = ∑ w, D w * ∑ y, sgn y * kpow K t w y := by
        simp only [g, mul_sum]; rw [sum_comm]
        exact sum_congr rfl fun w _ ↦ sum_congr rfl fun y _ ↦ by ring
    _ = ∑ w, D w * ∑ y, sgn y * (kpow K t w y - μ y) := by
        have : ∑ w, D w * ∑ y, sgn y * μ y = 0 := by rw [← sum_mul, hD, zero_mul]
        simp_rw [mul_sub, sum_sub_distrib, mul_sub, sum_sub_distrib, this, sub_zero]
    _ ≤ ∑ w, |D w| * (2 * c) := by
        refine sum_le_sum fun w _ ↦ ?_
        refine (le_abs_self _).trans ?_
        rw [abs_mul]
        refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
        refine (abs_sum_le_sum_abs _ _).trans ?_
        have := hc w
        unfold tvDist at this
        calc ∑ y, |sgn y * (kpow K t w y - μ y)| = ∑ y, |kpow K t w y - μ y| :=
              sum_congr rfl fun y _ ↦ by rw [abs_mul, hsabs, one_mul]
          _ ≤ 2 * c := by linarith
    _ = (∑ w, |D w|) * (2 * c) := by rw [sum_mul]

/-! ## The mixing distance `d(t) = max_x TV(K^t(x,·), μ)` -/

variable [Nonempty X]

/-- `d(t) = max_x TV(K^t(x,·), μ)`. -/
noncomputable def mixDist (K : X → X → ℝ) (μ : X → ℝ) (t : ℕ) : ℝ :=
  univ.sup' univ_nonempty fun x ↦ tvDist (kpow K t x) μ

theorem tvDist_le_mixDist (μ : X → ℝ) (t : ℕ) (x : X) : tvDist (kpow K t x) μ ≤ mixDist K μ t :=
  le_sup' (fun x ↦ tvDist (kpow K t x) μ) (mem_univ x)

theorem mixDist_le_iff (μ : X → ℝ) (t : ℕ) (c : ℝ) :
    mixDist K μ t ≤ c ↔ ∀ x, tvDist (kpow K t x) μ ≤ c := by
  unfold mixDist; simp [sup'_le_iff]

theorem mixDist_nonneg (μ : X → ℝ) (t : ℕ) : 0 ≤ mixDist K μ t :=
  (tvDist_nonneg _ _).trans (tvDist_le_mixDist μ t (Classical.arbitrary X))

theorem mixDist_le_one (hK : IsStochastic K) {μ : X → ℝ} (hμ : IsProb μ) (t : ℕ) :
    mixDist K μ t ≤ 1 :=
  (mixDist_le_iff μ t 1).2 fun x ↦ tvDist_le_one (kpow_isProb hK t x) hμ

theorem mixDist_succ_le (hK : IsStochastic K) (μ : X → ℝ) (t : ℕ) :
    mixDist K μ (t + 1) ≤ mixDist K μ t := by
  refine (mixDist_le_iff μ (t + 1) _).2 fun x ↦ ?_
  unfold tvDist
  have key : ∀ y, |kpow K (t + 1) x y - μ y| ≤ ∑ w, K x w * |kpow K t w y - μ y| := fun y ↦ by
    have : kpow K (t + 1) x y - μ y = ∑ w, K x w * (kpow K t w y - μ y) := by
      simp_rw [kpow_succ_apply, mul_sub, sum_sub_distrib, ← sum_mul, hK.row_sum, one_mul]
    rw [this]
    refine (abs_sum_le_sum_abs _ _).trans (le_of_eq (sum_congr rfl fun w _ ↦ ?_))
    rw [abs_mul, abs_of_nonneg (hK.nonneg x w)]
  have hsum : ∑ y, |kpow K (t + 1) x y - μ y| ≤ ∑ w, K x w * (2 * mixDist K μ t) := by
    refine (sum_le_sum fun y _ ↦ key y).trans ?_
    rw [sum_comm]
    refine sum_le_sum fun w _ ↦ ?_
    rw [← mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ (hK.nonneg x w)
    have := tvDist_le_mixDist (K := K) μ t w
    unfold tvDist at this
    linarith
  rw [← sum_mul, hK.row_sum, one_mul] at hsum
  linarith

theorem mixDist_antitone (hK : IsStochastic K) (μ : X → ℝ) {s t : ℕ} (h : s ≤ t) :
    mixDist K μ t ≤ mixDist K μ s := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact (mixDist_succ_le hK μ _).trans ih

/-- Submultiplicativity in the form `d(s+t) ≤ 2 d(s) d(t)` (stationary `μ`). -/
theorem mixDist_add_le (hK : IsStochastic K) {μ : X → ℝ} (hμ : IsProb μ)
    (hst : ∀ y, ∑ x, μ x * K x y = μ y) (s t : ℕ) :
    mixDist K μ (s + t) ≤ 2 * mixDist K μ s * mixDist K μ t := by
  refine (mixDist_le_iff μ (s + t) _).2 fun x ↦ ?_
  set D : X → ℝ := fun w ↦ kpow K s x w - μ w
  have hD : ∑ w, D w = 0 := by simp [D, sum_sub_distrib, kpow_row_sum hK, hμ.sum_eq]
  have hrow : ∀ y, kpow K (s + t) x y - μ y = ∑ w, D w * kpow K t w y := fun y ↦ by
    simp only [D, sub_mul, sum_sub_distrib, stationary_kpow hst t y, kpow_add]
  have h := sum_abs_mul_kpow_le (K := K) hD μ t (mixDist K μ t) (tvDist_le_mixDist μ t)
  have hDx : (∑ w, |D w|) = 2 * tvDist (kpow K s x) μ := by unfold tvDist; simp [D]
  have hx := tvDist_le_mixDist (K := K) μ s x
  have hdt := mixDist_nonneg (K := K) μ t
  unfold tvDist
  simp_rw [hrow]
  rw [hDx] at h
  nlinarith

/-- Halving after one mixing time. -/
theorem mixDist_add_tbar_le (hK : IsStochastic K) {μ : X → ℝ} (hμ : IsProb μ)
    (hst : ∀ y, ∑ x, μ x * K x y = μ y) {tb : ℕ} (htb : mixDist K μ tb ≤ 1 / 4) (s : ℕ) :
    mixDist K μ (s + tb) ≤ mixDist K μ s / 2 := by
  have h := mixDist_add_le hK hμ hst s tb
  have := mixDist_nonneg (K := K) μ s
  nlinarith

/-- `∑_{m<N} d(m) ≤ 2 t̄` whenever `t̄ ≥ 1` and `d(t̄) ≤ 1/4`. -/
theorem sum_mixDist_le (hK : IsStochastic K) {μ : X → ℝ} (hμ : IsProb μ)
    (hst : ∀ y, ∑ x, μ x * K x y = μ y) {tb : ℕ} (htb1 : 1 ≤ tb)
    (htb : mixDist K μ tb ≤ 1 / 4) (N : ℕ) :
    ∑ m ∈ range N, mixDist K μ m ≤ 2 * tb := by
  have hstep : ∀ k : ℕ, ∑ m ∈ range (k * tb), mixDist K μ m ≤ 2 * tb := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Nat.succ_mul, add_comm (k * tb) tb, sum_range_add]
      have h1 : ∑ m ∈ range tb, mixDist K μ m ≤ tb := by
        calc ∑ m ∈ range tb, mixDist K μ m ≤ ∑ m ∈ range tb, (1 : ℝ) :=
              sum_le_sum fun m _ ↦ mixDist_le_one hK hμ m
          _ = tb := by simp
      have h2 : ∑ m ∈ range (k * tb), mixDist K μ (tb + m) ≤
          (∑ m ∈ range (k * tb), mixDist K μ m) / 2 := by
        rw [sum_div]
        exact sum_le_sum fun m _ ↦ by rw [add_comm]; exact mixDist_add_tbar_le hK hμ hst htb m
      linarith
  have hmono : ∑ m ∈ range N, mixDist K μ m ≤ ∑ m ∈ range (N * tb), mixDist K μ m :=
    sum_le_sum_of_subset_of_nonneg (range_mono (Nat.le_mul_of_pos_right N htb1))
      fun m _ _ ↦ mixDist_nonneg μ m
  exact hmono.trans (hstep N)

/-- The `t`-step marginal of any initial law is within `d(t)` of `μ`, coordinatewise. -/
theorem abs_marginal_sub_le (hK : IsStochastic K) {μ : X → ℝ} (hμ : IsProb μ)
    {lam : X → ℝ} (hlam : IsProb lam) (t : ℕ) (z : X) :
    |∑ x, lam x * kpow K t x z - μ z| ≤ mixDist K μ t := by
  have : ∑ x, lam x * kpow K t x z - μ z = ∑ x, lam x * (kpow K t x z - μ z) := by
    simp_rw [mul_sub, sum_sub_distrib, ← sum_mul, hlam.sum_eq, one_mul]
  rw [this]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ x, |lam x * (kpow K t x z - μ z)| ≤ ∑ x, lam x * mixDist K μ t := by
        refine sum_le_sum fun x _ ↦ ?_
        rw [abs_mul, abs_of_nonneg (hlam.nonneg x)]
        refine mul_le_mul_of_nonneg_left ?_ (hlam.nonneg x)
        exact (abs_sub_le_tvDist (by rw [kpow_row_sum hK, hμ.sum_eq]) z).trans
          (tvDist_le_mixDist μ t x)
    _ = mixDist K μ t := by rw [← sum_mul, hlam.sum_eq, one_mul]

/-- At time `0`, `TV(δ_x, μ) ≥ 1 - μ(x)`. -/
theorem one_sub_le_tvDist_zero {μ : X → ℝ} (hμ : IsProb μ) (x : X) :
    1 - μ x ≤ tvDist (kpow K 0 x) μ := by
  have h := abs_sub_le_tvDist (p := kpow K 0 x) (q := μ) (by simp [kpow_zero_apply, hμ.sum_eq]) x
  simp only [kpow_zero_apply] at h
  exact (le_abs_self _).trans h

end StatisticalRL.FiniteMarkov
