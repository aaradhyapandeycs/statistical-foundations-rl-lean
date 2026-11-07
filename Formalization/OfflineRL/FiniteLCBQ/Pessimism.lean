import Formalization.OfflineRL.FiniteLCBQ.Pathwise
import Formalization.OfflineRL.FiniteVILCB.Deterministic

/-!
# Finite-horizon LCB-Q: row decomposition and pessimism (Step 3 of the plan)

For one `(h,s,a)` with visit count `n = N_h^k(s,a) ≥ 1`,
`Q_h^k(s,a) = r_h(s,a) + Σ_{j<k visits} η^n_{N^j+1} P_h(s,a)·V^j_{h+1} - M_n - β_n`, where `M_n` is
the martingale sum over the first `n` visits (`mart`) and `β_n = Σ_{i≤n} η_i^n b_i`. On the lower
side of the event E1 (`-M_n ≤ b_n`) the estimates are pessimistic, the strict-increase policy rule
keeps `V_h(s) ≤ r_h(s,π̂_h(s)) + P_h(s,π̂_h(s))·V_{h+1}` (or `V_h(s) = 0`), and backward induction
gives `V^K_h ≤ V^{π̂}_h`.
-/

namespace StatisticalRL.LCBQFinite

open Finset OnlineRL StatisticalRL.FiniteVILCB

variable {S A : Type*} [Fintype S] [Fintype A] [Nonempty S] [Nonempty A]
set_option linter.unusedSectionVars false

noncomputable local instance psDecS : DecidableEq S := Classical.decEq S
noncomputable local instance psDecA : DecidableEq A := Classical.decEq A

/-! ## Generic weighted visit sums -/

section Generic

variable (X : ℕ → Prop) [DecidablePred X] {H : ℕ}

/-- Visits at or after `k` carry zero weight `η^{cnt k}_{cnt j+1}`. -/
theorem trunc_sum (F : ℕ → ℝ) {k m : ℕ} (hkm : k ≤ m) :
    ∑ j ∈ range m, (if X j then onlineQRateWeight H (cnt X k) (cnt X j + 1) * F j else 0) =
      ∑ j ∈ range k, (if X j then onlineQRateWeight H (cnt X k) (cnt X j + 1) * F j else 0) := by
  rw [← sum_range_add_sum_Ico _ hkm]
  have : ∑ j ∈ Ico k m, (if X j then onlineQRateWeight H (cnt X k) (cnt X j + 1) * F j
      else 0) = 0 := by
    refine sum_eq_zero fun j hj ↦ ?_
    split_ifs
    · have := cnt_mono X (mem_Ico.1 hj).1
      rw [onlineQRateWeight_eq_zero_of_lt (by omega), zero_mul]
    · rfl
  rw [this, add_zero]

/-- Sums of weights over the visits before `k`. -/
theorem weight_sum_eq_one (hH : 0 < H) {k : ℕ} (hn : 1 ≤ cnt X k) :
    ∑ j ∈ range k, (if X j then onlineQRateWeight H (cnt X k) (cnt X j + 1) else 0) = 1 := by
  have := sum_range_visits X (fun i ↦ onlineQRateWeight H (cnt X k) (i + 1)) k
  simp only at this
  rw [this, sum_range_succ_shift (fun i ↦ onlineQRateWeight H (cnt X k) i),
    onlineQRateWeight_sum_eq_one hH hn]

theorem weight_sum_mul (b : ℕ → ℝ) (k : ℕ) :
    ∑ j ∈ range k, (if X j then onlineQRateWeight H (cnt X k) (cnt X j + 1) * b (cnt X j + 1)
      else 0) = ∑ i ∈ Icc 1 (cnt X k), onlineQRateWeight H (cnt X k) i * b i := by
  have := sum_range_visits X (fun i ↦ onlineQRateWeight H (cnt X k) (i + 1) * b (i + 1)) k
  simp only at this
  rw [this, sum_range_succ_shift (fun i ↦ onlineQRateWeight H (cnt X k) i * b i)]

end Generic

/-! ## The row decomposition -/

variable {H K : ℕ} (E : Fin H → EnvironmentStage S A) (cb L : ℝ) (sel : (A → ℝ) → A)
  (π₀ : Fin H → S → A) (x : Fin K → Traj S A H)

/-- Rewards of the environment. -/
def rw' (E : Fin H → EnvironmentStage S A) : Fin H → S → A → ℝ := fun h ↦ (E h).reward

/-- Shorthand for the run on the environment's rewards. -/
noncomputable abbrev it (k : ℕ) : Iterate S A H := itr cb L sel (rw' E) π₀ x k

/-- `V^j_{h+1}` as read by the stage-`h` update in episode `j`. -/
noncomputable abbrev Vn (k : ℕ) (h : Fin H) : S → ℝ := nextV (it E cb L sel π₀ x k) h

/-- The martingale sum `M_n = Σ_{first n visits} η^n_i (P_h(s,a)·V^j_{h+1} - V^j_{h+1}(s'_j))`. -/
noncomputable def mart (h : Fin H) (s : S) (a : A) (n : ℕ) : ℝ :=
  ∑ j ∈ range K, (if vis x h s a j then onlineQRateWeight H n (cnt (vis x h s a) j + 1) *
    (((E h).transition s a).expectation (Vn E cb L sel π₀ x j h) -
      Vn E cb L sel π₀ x j h (nxt x h j)) else 0)

/-- `β_n = Σ_{i=1}^n η_i^n b_i`. -/
noncomputable def beta (H : ℕ) (cb L : ℝ) (n : ℕ) : ℝ := ∑ i ∈ Icc 1 n, onlineQRateWeight H n i * penalty cb L H i

theorem vis_lt {h : Fin H} {s : S} {a : A} {j : ℕ} (hv : vis x h s a j) : j < K := hv.1

theorem cnt_vis_le (h : Fin H) (s : S) (a : A) (k : ℕ) : cnt (vis x h s a) k ≤ K := by
  unfold cnt
  calc ((range k).filter (vis x h s a)).card ≤ (range K).card := by
        refine card_le_card fun j hj ↦ ?_
        simp only [mem_filter] at hj
        exact mem_range.2 (vis_lt x hj.2)
    _ = K := card_range K

/-- Sums over `range m` with `m ≥ K` do not see episodes beyond the data. -/
theorem sum_vis_range_K (h : Fin H) (s : S) (a : A) (G : ℕ → ℝ) {m : ℕ} (hm : K ≤ m) :
    ∑ j ∈ range m, (if vis x h s a j then G j else 0) =
      ∑ j ∈ range K, (if vis x h s a j then G j else 0) := by
  rw [← sum_range_add_sum_Ico _ hm]
  have : ∑ j ∈ Ico K m, (if vis x h s a j then G j else 0) = 0 :=
    sum_eq_zero fun j hj ↦ by
      rw [if_neg fun hv ↦ absurd (vis_lt x hv) (by have := (mem_Ico.1 hj).1; omega)]
  rw [this, add_zero]

theorem mart_eq_range (h : Fin H) (s : S) (a : A) (k : ℕ) :
    mart E cb L sel π₀ x h s a (cnt (vis x h s a) k) =
      ∑ j ∈ range k, (if vis x h s a j then onlineQRateWeight H (cnt (vis x h s a) k)
        (cnt (vis x h s a) j + 1) * (((E h).transition s a).expectation (Vn E cb L sel π₀ x j h) -
          Vn E cb L sel π₀ x j h (nxt x h j)) else 0) := by
  unfold mart
  set F : ℕ → ℝ := fun j ↦ ((E h).transition s a).expectation (Vn E cb L sel π₀ x j h) -
    Vn E cb L sel π₀ x j h (nxt x h j)
  have h1 := sum_vis_range_K x h s a
    (fun j ↦ onlineQRateWeight H (cnt (vis x h s a) k) (cnt (vis x h s a) j + 1) * F j)
    (le_max_right k K)
  have h2 := trunc_sum (H := H) (vis x h s a) F (le_max_left k K)
  rw [← h1, h2]

theorem penalty_eq (hL : 0 ≤ L) (i : ℕ) :
    penalty cb L H i = cb * Real.sqrt ((H : ℝ) ^ 3 * L) / Real.sqrt i := by
  unfold penalty
  rw [Real.sqrt_div (by positivity), mul_div_assoc]

theorem beta_bounds' (hH : 0 < H) (hcb : 0 ≤ cb) (hL : 0 ≤ L) {n : ℕ} (hn : 0 < n) :
    penalty cb L H n ≤ beta H cb L n ∧ beta H cb L n ≤ 2 * penalty cb L H n := by
  have h := beta_bounds hH (mul_nonneg hcb (Real.sqrt_nonneg ((H : ℝ) ^ 3 * L))) hn
  unfold beta
  simp only [penalty_eq cb L hL]
  refine ⟨h.1, h.2.trans_eq ?_⟩
  ring

/-- **Row decomposition.** -/
theorem Q_decomp (hH : 0 < H) (h : Fin H) (s : S) (a : A) (k : ℕ)
    (hn : 1 ≤ cnt (vis x h s a) k) :
    (it E cb L sel π₀ x k).Q h s a = (E h).reward s a +
      ∑ j ∈ range k, (if vis x h s a j then onlineQRateWeight H (cnt (vis x h s a) k)
        (cnt (vis x h s a) j + 1) * ((E h).transition s a).expectation (Vn E cb L sel π₀ x j h)
        else 0) - mart E cb L sel π₀ x h s a (cnt (vis x h s a) k) - beta H cb L (cnt (vis x h s a) k) := by
  rw [Q_unroll, mart_eq_range]
  unfold beta
  rw [← weight_sum_mul (H := H) (vis x h s a) (fun i ↦ penalty cb L H i) k]
  have hw := weight_sum_eq_one (vis x h s a) hH hn
  have e : (E h).reward s a = ∑ j ∈ range k, (if vis x h s a j then
      onlineQRateWeight H (cnt (vis x h s a) k) (cnt (vis x h s a) j + 1) * (E h).reward s a
      else 0) := by
    calc (E h).reward s a = (E h).reward s a * 1 := (mul_one _).symm
      _ = _ := by
        rw [← hw, mul_sum]
        refine sum_congr rfl fun j _ ↦ ?_
        split_ifs <;> ring
  rw [e, ← sum_add_distrib, ← sum_sub_distrib, ← sum_sub_distrib]
  refine sum_congr rfl fun j _ ↦ ?_
  split_ifs
  · unfold target; simp only [rw']; ring
  · ring

/-! ## Pessimism -/

/-- The lower side of the event E1, in the form used pathwise. -/
def LowerE1 : Prop :=
  ∀ (h : Fin H) (s : S) (a : A) (n : ℕ), 1 ≤ n → n ≤ K →
    -mart E cb L sel π₀ x h s a n ≤ penalty cb L H n

/-- On `LowerE1`, `Q_h^k(s,a) ≤ r_h(s,a) + P_h(s,a)·V^k_{h+1}`. -/
theorem Q_le_backup (hH : 0 < H) (hcb : 0 ≤ cb) (hL : 0 ≤ L) (hE : LowerE1 E cb L sel π₀ x)
    (k : ℕ) (h : Fin H) (s : S) (a : A) :
    (it E cb L sel π₀ x k).Q h s a ≤
      (E h).reward s a + ((E h).transition s a).expectation (Vn E cb L sel π₀ x k h) := by
  rcases Nat.eq_zero_or_pos (cnt (vis x h s a) k) with h0 | hpos
  · have hQ : (it E cb L sel π₀ x k).Q h s a = 0 := by
      rw [Q_unroll, h0]
      refine sum_eq_zero fun j _ ↦ ?_
      split_ifs
      · rw [onlineQRateWeight_eq_zero_of_lt (by omega), zero_mul]
      · rfl
    rw [hQ]
    exact add_nonneg ((E h).reward_nonneg s a)
      (FiniteDistribution.expectation_nonneg _ fun t ↦
        nextV_nonneg cb L sel (rw' E) π₀ x k h t)
  · rw [Q_decomp E cb L sel π₀ x hH h s a k hpos]
    have hlow := hE h s a _ hpos (cnt_vis_le x h s a k)
    have hb := (beta_bounds' cb L hH hcb hL hpos).1
    have hmono : ∑ j ∈ range k, (if vis x h s a j then onlineQRateWeight H (cnt (vis x h s a) k)
        (cnt (vis x h s a) j + 1) * ((E h).transition s a).expectation (Vn E cb L sel π₀ x j h)
        else 0) ≤ ((E h).transition s a).expectation (Vn E cb L sel π₀ x k h) := by
      rw [← mul_one (((E h).transition s a).expectation (Vn E cb L sel π₀ x k h)),
        ← weight_sum_eq_one (vis x h s a) hH hpos, mul_sum]
      refine sum_le_sum fun j hj ↦ ?_
      split_ifs
      · rw [mul_comm (((E h).transition s a).expectation _)]
        refine mul_le_mul_of_nonneg_left ?_ (onlineQRateWeight_nonneg hH _ _)
        exact FiniteDistribution.expectation_mono _ fun t ↦
          nextV_mono cb L sel (rw' E) π₀ x (mem_range.1 hj).le h t
      · simp
    linarith

/-- The policy invariant of the strict-increase rule. -/
theorem pol_invariant (hH : 0 < H) (hcb : 0 ≤ cb) (hL : 0 ≤ L) (hE : LowerE1 E cb L sel π₀ x)
    (hsel : ∀ (f : A → ℝ) (a : A), f a ≤ f (sel f)) :
    ∀ k (h : Fin H) (s : S), (it E cb L sel π₀ x k).V h s = 0 ∨
      (it E cb L sel π₀ x k).V h s ≤ (E h).reward s ((it E cb L sel π₀ x k).pol h s) +
        ((E h).transition s ((it E cb L sel π₀ x k).pol h s)).expectation
          (Vn E cb L sel π₀ x k h) := by
  intro k
  induction k with
  | zero => intro h s; left; rfl
  | succ k ih =>
    intro h s
    have hgrow : ∀ b, (E h).reward s b + ((E h).transition s b).expectation (Vn E cb L sel π₀ x k h)
        ≤ (E h).reward s b + ((E h).transition s b).expectation (Vn E cb L sel π₀ x (k + 1) h) :=
      fun b ↦ add_le_add le_rfl (FiniteDistribution.expectation_mono _ fun t ↦
        nextV_mono cb L sel (rw' E) π₀ x (Nat.le_succ k) h t)
    by_cases hinc : visS x h s k ∧
        (it E cb L sel π₀ x k).V h s < (it E cb L sel π₀ x (k + 1)).V h s
    · right
      have hp : (it E cb L sel π₀ x (k + 1)).pol h s =
          sel ((it E cb L sel π₀ x (k + 1)).Q h s) := by
        simp only [it]; rw [pol_succ, if_pos hinc]
      have hV : (it E cb L sel π₀ x (k + 1)).V h s =
          actionMaximum ((it E cb L sel π₀ x (k + 1)).Q h s) := by
        have e := V_succ cb L sel (rw' E) π₀ x k h s
        rw [if_pos hinc.1] at e
        have hlt := hinc.2
        simp only [it] at hlt ⊢
        rw [e] at hlt ⊢
        exact max_eq_right (le_of_lt (lt_max_iff.1 hlt |>.resolve_left (lt_irrefl _)))
      rw [hV, hp]
      have hmax : actionMaximum ((it E cb L sel π₀ x (k + 1)).Q h s) ≤
          (it E cb L sel π₀ x (k + 1)).Q h s (sel ((it E cb L sel π₀ x (k + 1)).Q h s)) := by
        unfold actionMaximum
        exact Finset.sup'_le _ _ fun a _ ↦ hsel _ a
      exact hmax.trans (Q_le_backup E cb L sel π₀ x hH hcb hL hE (k + 1) h s _)
    · have hp : (it E cb L sel π₀ x (k + 1)).pol h s = (it E cb L sel π₀ x k).pol h s := by
        simp only [it]; rw [pol_succ, if_neg hinc]
      have hV : (it E cb L sel π₀ x (k + 1)).V h s = (it E cb L sel π₀ x k).V h s := by
        have hle := V_mono_succ cb L sel (rw' E) π₀ x k h s
        by_cases hv : visS x h s k
        · exact le_antisymm (not_lt.1 fun hlt ↦ hinc ⟨hv, hlt⟩) hle
        · simp only [it]; rw [V_succ, if_neg hv]
      rw [hV, hp]
      rcases ih h s with h0 | hle
      · left; exact h0
      · right; exact hle.trans (hgrow _)

/-- **Pessimism**: on `LowerE1`, `V_h^K ≤ V^{π̂}_h` for the output policy. -/
theorem V_le_polV (hH : 0 < H) (hcb : 0 ≤ cb) (hL : 0 ≤ L) (hE : LowerE1 E cb L sel π₀ x)
    (hsel : ∀ (f : A → ℝ) (a : A), f a ≤ f (sel f)) (k : ℕ) :
    ∀ (h : Fin H) (s : S), (it E cb L sel π₀ x k).V h s ≤
      polV E (it E cb L sel π₀ x k).pol h.val s := by
  have key : ∀ m, ∀ h : Fin H, H - h.val = m → ∀ s, (it E cb L sel π₀ x k).V h s ≤
      polV E (it E cb L sel π₀ x k).pol h.val s := by
    intro m
    induction m with
    | zero => intro h hh; exact absurd hh (by have := h.isLt; omega)
    | succ m ih =>
      intro h hh s
      have hnext : ∀ t, Vn E cb L sel π₀ x k h t ≤ polV E (it E cb L sel π₀ x k).pol (h.val + 1) t := by
        intro t
        simp only [Vn, nextV]
        split_ifs with hlt
        · exact ih ⟨h.val + 1, hlt⟩ (by simp; omega) t
        · rw [polV_of_ge E _ (by omega)]
      rcases pol_invariant E cb L sel π₀ x hH hcb hL hE hsel k h s with h0 | hle
      · rw [h0]; exact polV_nonneg E _ _ s
      · rw [polV_of_lt]
        exact hle.trans (add_le_add le_rfl (FiniteDistribution.expectation_mono _ hnext))
  intro h s
  exact key (H - h.val) h rfl s

end StatisticalRL.LCBQFinite
