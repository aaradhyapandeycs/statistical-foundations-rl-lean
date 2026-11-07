import Formalization.Online.Bandit.UCBDefinitions

/-!
# UCB: pathwise facts

Deterministic properties of the UCB recursion used in the proof of Theorem 5.1
(`chapters/bandits.tex:387–451`): count and sum recursions, the argmax membership of the pulled
arm, the count-below identity, the identification of the running noise sum with the sum of the
first `N` noises, past dependence, and the deterministic part of Step 1 (`:400–419`).
-/

open Finset

noncomputable section

namespace StatisticalRL.Bandit

variable {A : ℕ} (tie : ℕ → Finset (Fin A) → Fin A) (L : ℝ) (r : Fin A → ℝ)
  (ζ : ℕ → Fin A → ℝ)

/-- Count `N_t(c)` before round `t`. -/
abbrev ucbCount (t : ℕ) (c : Fin A) : ℕ := (ucbState tie L r ζ t).1 c

/-- Reward sum `r^sum_t(c)` before round `t`. -/
abbrev ucbSum (t : ℕ) (c : Fin A) : ℝ := (ucbState tie L r ζ t).2 c

/-- Sum of the noises of arm `c` over its pulls with pre-count below `k`, among rounds `< T`;
when `k ≤ N_T(c)` this is the sum of the first `k` noises of arm `c`. -/
def ucbNoiseSum (T k : ℕ) (c : Fin A) : ℝ :=
  ∑ s ∈ range T, if ucbArm tie L r ζ s = c ∧ ucbCount tie L r ζ s c < k then ζ s c else 0

theorem ucbCount_zero (c : Fin A) : ucbCount tie L r ζ 0 c = 0 := rfl

theorem ucbCount_succ (t : ℕ) (c : Fin A) :
    ucbCount tie L r ζ (t + 1) c
      = ucbCount tie L r ζ t c + if ucbArm tie L r ζ t = c then 1 else 0 := by
  classical
  simp only [ucbCount, ucbState, ucbArm]
  by_cases h : tie t (ucbArgmax L (ucbState tie L r ζ t).1 (ucbState tie L r ζ t).2) = c
  · subst h; simp
  · rw [if_neg h, Function.update_of_ne (Ne.symm h)]; simp

theorem ucbSum_succ (t : ℕ) (c : Fin A) :
    ucbSum tie L r ζ (t + 1) c
      = ucbSum tie L r ζ t c + if ucbArm tie L r ζ t = c then r c + ζ t c else 0 := by
  classical
  simp only [ucbSum, ucbState, ucbArm]
  by_cases h : tie t (ucbArgmax L (ucbState tie L r ζ t).1 (ucbState tie L r ζ t).2) = c
  · subst h; simp
  · rw [if_neg h, Function.update_of_ne (Ne.symm h)]; simp

theorem ucbCount_mono (c : Fin A) : Monotone fun t => ucbCount tie L r ζ t c := by
  apply monotone_nat_of_le_succ
  intro t
  rw [ucbCount_succ]; exact Nat.le_add_right _ _

theorem ucbCount_le (t : ℕ) (c : Fin A) : ucbCount tie L r ζ t c ≤ t := by
  induction t with
  | zero => simp [ucbCount_zero]
  | succ t ih => rw [ucbCount_succ]; split_ifs <;> omega

theorem sum_ucbCount (t : ℕ) : ∑ c, ucbCount tie L r ζ t c = t := by
  classical
  induction t with
  | zero => simp [ucbCount_zero]
  | succ t ih =>
    simp_rw [ucbCount_succ]
    rw [sum_add_distrib, ih]
    simp

theorem ucbCount_eq_sum (t : ℕ) (c : Fin A) :
    ucbCount tie L r ζ t c = ∑ s ∈ range t, if ucbArm tie L r ζ s = c then 1 else 0 := by
  induction t with
  | zero => simp [ucbCount_zero]
  | succ t ih => rw [ucbCount_succ, sum_range_succ, ih]

/-- The argmax set is nonempty. -/
theorem ucbArgmax_nonempty [NeZero A] (N : Fin A → ℕ) (S : Fin A → ℝ) :
    (ucbArgmax L N S).Nonempty := by
  obtain ⟨a, -, ha⟩ := exists_max_image univ (ucbIndex L N S) univ_nonempty
  exact ⟨a, by simp [ucbArgmax]; exact fun b => ha b (mem_univ b)⟩

theorem ucbArm_mem [NeZero A] (htie : ∀ t s, s.Nonempty → tie t s ∈ s) (t : ℕ) :
    ucbArm tie L r ζ t
      ∈ ucbArgmax L (ucbState tie L r ζ t).1 (ucbState tie L r ζ t).2 :=
  htie _ _ (ucbArgmax_nonempty L _ _)

/-- `r^sum_t(c) = N_t(c) r(c) + Σ_{s<t, a_s = c} ζ_s(c)`. -/
theorem ucbSum_eq (t : ℕ) (c : Fin A) :
    ucbSum tie L r ζ t c = ucbCount tie L r ζ t c * r c
      + ∑ s ∈ range t, if ucbArm tie L r ζ s = c then ζ s c else 0 := by
  induction t with
  | zero => simp [ucbSum, ucbState]
  | succ t ih =>
    rw [ucbSum_succ, ucbCount_succ, sum_range_succ, ih]
    split_ifs <;> push_cast <;> ring

/-- Number of pulls of `c` with pre-count below `n`, among rounds `< t`, is `min n N_t(c)`. -/
theorem sum_pull_below (n t : ℕ) (c : Fin A) :
    (∑ s ∈ range t, if ucbArm tie L r ζ s = c ∧ ucbCount tie L r ζ s c < n then 1 else 0)
      = min n (ucbCount tie L r ζ t c) := by
  induction t with
  | zero => simp [ucbCount_zero]
  | succ t ih =>
    rw [sum_range_succ, ih, ucbCount_succ]
    by_cases h1 : ucbArm tie L r ζ t = c <;> by_cases h2 : ucbCount tie L r ζ t c < n <;>
      simp [h1, h2] <;> omega

/-- Real-valued version of `sum_pull_below`. -/
theorem sum_pull_below_real (n t : ℕ) (c : Fin A) :
    (∑ s ∈ range t, if ucbArm tie L r ζ s = c ∧ ucbCount tie L r ζ s c < n then (1 : ℝ) else 0)
      = (min n (ucbCount tie L r ζ t c) : ℕ) := by
  rw [← sum_pull_below]; push_cast
  apply sum_congr rfl; intro s _; split_ifs <;> simp

/-- The running noise sum of `c` before round `t ≤ T` is the sum of its first `N_t(c)` noises. -/
theorem noise_eq_ucbNoiseSum {T t : ℕ} (ht : t ≤ T) (c : Fin A) :
    (∑ s ∈ range t, if ucbArm tie L r ζ s = c then ζ s c else 0)
      = ucbNoiseSum tie L r ζ T (ucbCount tie L r ζ t c) c := by
  unfold ucbNoiseSum
  rw [← sum_range_add_sum_Ico _ ht]
  have h2 : (∑ s ∈ Ico t T, if ucbArm tie L r ζ s = c ∧
      ucbCount tie L r ζ s c < ucbCount tie L r ζ t c then ζ s c else 0) = 0 := by
    apply sum_eq_zero
    intro s hs
    have hts : t ≤ s := (mem_Ico.mp hs).1
    have := ucbCount_mono tie L r ζ c hts
    rw [if_neg]; simp only [not_and, not_lt]; intro _; exact this
  rw [h2, add_zero]
  apply sum_congr rfl
  intro s hs
  have hst : s < t := mem_range.mp hs
  by_cases h : ucbArm tie L r ζ s = c
  · have hlt : ucbCount tie L r ζ s c < ucbCount tie L r ζ t c := by
      have h1 := ucbCount_succ tie L r ζ s c
      rw [if_pos h] at h1
      have h3 : ucbCount tie L r ζ (s + 1) c ≤ ucbCount tie L r ζ t c :=
        ucbCount_mono tie L r ζ c (show s + 1 ≤ t from hst)
      omega
    simp [h, hlt]
  · simp [h]

/-- The state before round `t` depends only on the noises of rounds `< t`. -/
theorem ucbState_congr {ζ' : ℕ → Fin A → ℝ} (t : ℕ) (h : ∀ s, s < t → ζ s = ζ' s) :
    ucbState tie L r ζ t = ucbState tie L r ζ' t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have ih' := ih (fun s hs => h s (Nat.lt_succ_of_lt hs))
    simp only [ucbState]
    rw [ih', h t (Nat.lt_succ_self t)]

theorem ucbArm_congr {ζ' : ℕ → Fin A → ℝ} (t : ℕ) (h : ∀ s, s < t → ζ s = ζ' s) :
    ucbArm tie L r ζ t = ucbArm tie L r ζ' t := by
  simp only [ucbArm]; rw [ucbState_congr tie L r ζ t h]

/-- Deterministic part of Step 1 (`chapters/bandits.tex:400–419`): if a suboptimal arm `a` with
`N_t(a) > 8 L / Δ(a)²` is pulled at round `t ≤ T`, then either the first-`N_t(a)` noise sum of
`a` exceeds `N_t(a) √(2L/N_t(a))`, or the first-`N_t(a⋆)` noise sum of `a⋆` is below
`-N_t(a⋆) √(2L/N_t(a⋆))`; in both cases the count lies in `[1, t]`. -/
theorem step1_pathwise [NeZero A] (htie : ∀ t s, s.Nonempty → tie t s ∈ s) (hL : 0 ≤ L)
    {T t : ℕ} (ht : t ≤ T) (a astar : Fin A) (hΔ : 0 < r astar - r a)
    (hpull : ucbArm tie L r ζ t = a)
    (hm : 8 * L / (r astar - r a) ^ 2 < ucbCount tie L r ζ t a) :
    (1 ≤ ucbCount tie L r ζ t a ∧ ucbCount tie L r ζ t a ≤ t ∧
      (ucbCount tie L r ζ t a : ℝ) * Real.sqrt (2 * L / ucbCount tie L r ζ t a)
        < ucbNoiseSum tie L r ζ T (ucbCount tie L r ζ t a) a) ∨
    (1 ≤ ucbCount tie L r ζ t astar ∧ ucbCount tie L r ζ t astar ≤ t ∧
      ucbNoiseSum tie L r ζ T (ucbCount tie L r ζ t astar) astar
        < -((ucbCount tie L r ζ t astar : ℝ) *
            Real.sqrt (2 * L / ucbCount tie L r ζ t astar))) := by
  set k := ucbCount tie L r ζ t a with hk
  set k' := ucbCount tie L r ζ t astar with hk'
  set Δ := r astar - r a with hΔdef
  have hmem := ucbArm_mem tie L r ζ htie t
  rw [hpull] at hmem
  simp only [ucbArgmax, mem_filter, mem_univ, true_and] at hmem
  have h8 : 0 ≤ 8 * L / Δ ^ 2 := by positivity
  have hkpos : (0 : ℝ) < k := lt_of_le_of_lt h8 hm
  have hk0 : k ≠ 0 := by intro h; rw [h] at hkpos; simp at hkpos
  have hidx_a : ucbIndex L (ucbState tie L r ζ t).1 (ucbState tie L r ζ t).2 a
      = ((ucbSum tie L r ζ t a / k + Real.sqrt (2 * L / k) : ℝ) : WithTop ℝ) := by
    simp [ucbIndex, hk0, ucbSum, k, ucbCount]
  have hstar := hmem astar
  rw [hidx_a] at hstar
  have hk'0 : k' ≠ 0 := by
    intro h
    simp [ucbIndex, ucbCount, k'] at hstar h
    simp [h] at hstar
  have hidx_s : ucbIndex L (ucbState tie L r ζ t).1 (ucbState tie L r ζ t).2 astar
      = ((ucbSum tie L r ζ t astar / k' + Real.sqrt (2 * L / k') : ℝ) : WithTop ℝ) := by
    simp [ucbIndex, hk'0, ucbSum, k', ucbCount]
  rw [hidx_s, WithTop.coe_le_coe] at hstar
  have hk'pos : (0 : ℝ) < k' := by exact_mod_cast Nat.pos_of_ne_zero hk'0
  have hkle : k ≤ t := ucbCount_le tie L r ζ t a
  have hk'le : k' ≤ t := ucbCount_le tie L r ζ t astar
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨h1, h2⟩ := hcon
  have hY1 : ucbNoiseSum tie L r ζ T k a ≤ k * Real.sqrt (2 * L / k) := by
    by_contra h; exact h1 ⟨Nat.one_le_iff_ne_zero.mpr hk0, hkle, lt_of_not_ge h⟩
  have hY2 : -(k' * Real.sqrt (2 * L / k')) ≤ ucbNoiseSum tie L r ζ T k' astar := by
    by_contra h; exact h2 ⟨Nat.one_le_iff_ne_zero.mpr hk'0, hk'le, lt_of_not_ge h⟩
  have hSa := ucbSum_eq tie L r ζ t a
  rw [noise_eq_ucbNoiseSum tie L r ζ ht] at hSa
  have hSs := ucbSum_eq tie L r ζ t astar
  rw [noise_eq_ucbNoiseSum tie L r ζ ht] at hSs
  rw [← hk] at hSa
  rw [← hk'] at hSs
  set β := Real.sqrt (2 * L / k)
  set β' := Real.sqrt (2 * L / k')
  set Y := ucbNoiseSum tie L r ζ T k a
  set Y' := ucbNoiseSum tie L r ζ T k' astar
  -- upper bound on the index of `a`
  have hva : ucbSum tie L r ζ t a / k + β ≤ r a + 2 * β := by
    rw [hSa, add_div, mul_div_cancel_left₀ _ hkpos.ne']
    have : Y / k ≤ β := by rw [div_le_iff₀ hkpos]; linarith
    linarith
  have hvs : r astar ≤ ucbSum tie L r ζ t astar / k' + β' := by
    rw [hSs, add_div, mul_div_cancel_left₀ _ hk'pos.ne']
    have : -β' ≤ Y' / k' := by rw [le_div_iff₀ hk'pos]; linarith
    linarith
  -- the bonus is below half the gap
  have hβ : 2 * β < Δ := by
    have hsq : (2 * β) ^ 2 = 8 * L / k := by
      rw [mul_pow, Real.sq_sqrt (by positivity)]; ring
    have h8k : 8 * L / k < Δ ^ 2 := by
      rw [div_lt_iff₀ hkpos]
      rw [div_lt_iff₀ (by positivity)] at hm
      linarith
    have hβnn : 0 ≤ 2 * β := by positivity
    nlinarith [sq_nonneg (2 * β - Δ), sq_nonneg (2 * β + Δ)]
  have : ucbSum tie L r ζ t a / k + β < ucbSum tie L r ζ t astar / k' + β' := by
    linarith
  linarith
