import Formalization.OfflineRL.FiniteLCBQ.Definitions
import Formalization.OfflineRL.FiniteLCBQ.Counting
import Formalization.MDP.Basic

/-!
# Finite-horizon LCB-Q: pathwise structure (Step 1 of the plan)

* `stage_episodeStep` (`run_episode_parallel`): under the forward stage order, the stage-`h` block
  after one episode is the single row update of the stage-`h` block before the episode, reading
  `V_{h+1}` from before the episode;
* per-episode component equations for `Q`, `V`, `N`, `π̂`;
* prefix dependence of `iterAfter`;
* invariants: `V ≥ 0`, monotonicity, `V ≥ max_a Q`, the bounds `Q, V ≤ H - h`, `N = cnt`;
* the unrolled form of `Q` (`eq:unroll-q-lcbq`).
-/

namespace StatisticalRL.LCBQFinite

open Finset OnlineRL StatisticalRL.FiniteVILCB

variable {S A : Type*} [Fintype S] [Fintype A] [Nonempty A]
set_option linter.unusedSectionVars false

noncomputable local instance pwDecS : DecidableEq S := Classical.decEq S
noncomputable local instance pwDecA : DecidableEq A := Classical.decEq A

variable {H : ℕ}

/-- The stage-`h` block of an iterate. -/
def stage (it : Iterate S A H) (h : Fin H) : (S → A → ℝ) × (S → ℝ) × (S → A → ℕ) × (S → A) :=
  (it.Q h, it.V h, it.N h, it.pol h)

/-- The row update acting on one stage block. -/
noncomputable def stageUpd (cb L : ℝ) (sel : (A → ℝ) → A) (r : Fin H → S → A → ℝ) (h : Fin H)
    (s : S) (a : A) (s' : S) (Q : S → A → ℝ) (V : S → ℝ) (N : S → A → ℕ) (p : S → A)
    (Vn : S → ℝ) : (S → A → ℝ) × (S → ℝ) × (S → A → ℕ) × (S → A) :=
  let n := N s a + 1
  let q := (1 - onlineQRate H n) * Q s a + onlineQRate H n * (r h s a + Vn s' - penalty cb L H n)
  let row := Function.update (Q s) a q
  let v := max (V s) (actionMaximum row)
  (Function.update Q s row, Function.update V s v, Function.update N s (Function.update (N s) a n),
    if V s < v then Function.update p s (sel row) else p)

variable (cb L : ℝ) (sel : (A → ℝ) → A) (r : Fin H → S → A → ℝ)

theorem stage_rowStep (h : Fin H) (s : S) (a : A) (s' : S) (it : Iterate S A H) :
    stage (rowStep cb L sel r h s a s' it) h =
      stageUpd cb L sel r h s a s' (it.Q h) (it.V h) (it.N h) (it.pol h) (nextV it h) := by
  simp only [stage, rowStep, stageUpd, Function.update_self]
  split_ifs <;> simp

theorem stage_rowStep_ne {h h' : Fin H} (hne : h' ≠ h) (s : S) (a : A) (s' : S)
    (it : Iterate S A H) : stage (rowStep cb L sel r h s a s' it) h' = stage it h' := by
  simp only [stage, rowStep, Function.update_of_ne hne]
  split_ifs <;> simp [Function.update_of_ne hne]

theorem nextV_eq_of_stage {it it' : Iterate S A H} (h : Fin H)
    (hst : ∀ hh : h.val + 1 < H, stage it ⟨h.val + 1, hh⟩ = stage it' ⟨h.val + 1, hh⟩) :
    nextV it h = nextV it' h := by
  unfold nextV
  split_ifs with hh
  · have := congrArg (fun t ↦ t.2.1) (hst hh)
    simpa [stage] using this
  · rfl

/-- The stage triple `(s_h, a_h, s_{h+1})` of a trajectory. -/
def trip (τ : Traj S A H) (h : Fin H) : S × A × S := (τ.1 h.castSucc, τ.2 h, τ.1 h.succ)

/-- **Stage parallelism** (`run_episode_parallel`) for the first `m` stages. -/
theorem stage_stagesUpTo (τ : Traj S A H) (it : Iterate S A H) :
    ∀ m, m ≤ H → ∀ h : Fin H, stage (stagesUpTo cb L sel r τ it m) h =
      if h.val < m then stageUpd cb L sel r h (trip τ h).1 (trip τ h).2.1 (trip τ h).2.2
        (it.Q h) (it.V h) (it.N h) (it.pol h) (nextV it h)
      else stage it h := by
  intro m
  induction m with
  | zero => intro _ h; simp [stagesUpTo]
  | succ m ih =>
    intro hm h
    have hmH : m < H := by omega
    simp only [stagesUpTo, dif_pos hmH]
    by_cases hh : h = ⟨m, hmH⟩
    · subst hh
      rw [stage_rowStep, if_pos (by simp)]
      have h1 := ih (by omega) ⟨m, hmH⟩
      rw [if_neg (by simp)] at h1
      have h2 : nextV (stagesUpTo cb L sel r τ it m) ⟨m, hmH⟩ = nextV it ⟨m, hmH⟩ := by
        refine nextV_eq_of_stage _ fun hh ↦ ?_
        have := ih (by omega) ⟨m + 1, hh⟩
        rw [if_neg (by simp)] at this
        exact this
      simp only [stage, Prod.mk.injEq] at h1
      rw [h1.1, h1.2.1, h1.2.2.1, h1.2.2.2, h2]
      rfl
    · rw [stage_rowStep_ne _ _ _ _ hh, ih (by omega) h]
      have : h.val ≠ m := fun e ↦ hh (Fin.ext e)
      by_cases hlt : h.val < m
      · rw [if_pos hlt, if_pos (by omega)]
      · rw [if_neg hlt, if_neg (by omega)]

/-- **Stage parallelism for a whole episode**. -/
theorem stage_episodeStep (τ : Traj S A H) (it : Iterate S A H) (h : Fin H) :
    stage (episodeStep cb L sel r τ it) h =
      stageUpd cb L sel r h (trip τ h).1 (trip τ h).2.1 (trip τ h).2.2
        (it.Q h) (it.V h) (it.N h) (it.pol h) (nextV it h) := by
  unfold episodeStep
  rw [stage_stagesUpTo cb L sel r τ it H le_rfl h, if_pos h.isLt]

/-! ## Episode-indexed iterates -/

variable {K : ℕ} (π₀ : Fin H → S → A) (x : Fin K → Traj S A H)

/-- Abbreviation for the iterate after `k` episodes. -/
noncomputable abbrev itr (k : ℕ) : Iterate S A H := iterAfter cb L sel π₀ r x k

theorem itr_succ_of_ge {k : ℕ} (hk : K ≤ k) : itr cb L sel r π₀ x (k + 1) = itr cb L sel r π₀ x k := by
  simp only [itr, iterAfter, dif_neg (show ¬ k < K by omega)]

theorem stage_itr_succ {k : ℕ} (hk : k < K) (h : Fin H) :
    stage (itr cb L sel r π₀ x (k + 1)) h =
      stageUpd cb L sel r h (trip (x ⟨k, hk⟩) h).1 (trip (x ⟨k, hk⟩) h).2.1
        (trip (x ⟨k, hk⟩) h).2.2 ((itr cb L sel r π₀ x k).Q h) ((itr cb L sel r π₀ x k).V h)
        ((itr cb L sel r π₀ x k).N h) ((itr cb L sel r π₀ x k).pol h)
        (nextV (itr cb L sel r π₀ x k) h) := by
  simp only [itr, iterAfter, dif_pos hk]
  exact stage_episodeStep cb L sel r _ _ h

/-- **Prefix dependence.** The iterate after `k` episodes depends only on the first `k`
trajectories. -/
theorem itr_congr (y : Fin K → Traj S A H) :
    ∀ k, (∀ j : Fin K, j.val < k → x j = y j) →
      itr cb L sel r π₀ x k = itr cb L sel r π₀ y k := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
    intro hxy
    simp only [itr, iterAfter] at ih ⊢
    split_ifs with hk
    · rw [ih fun j hj ↦ hxy j (by omega), hxy ⟨k, hk⟩ (by simp)]
    · exact ih fun j hj ↦ hxy j (by omega)

/-! ## Component equations -/

/-- Visit indicator of `(h,s,a)` at episode `j`. -/
def vis (h : Fin H) (s : S) (a : A) (j : ℕ) : Prop :=
  ∃ hj : j < K, (x ⟨j, hj⟩).1 h.castSucc = s ∧ (x ⟨j, hj⟩).2 h = a

/-- Visit indicator of the state `(h,s)` at episode `j`. -/
def visS (h : Fin H) (s : S) (j : ℕ) : Prop := ∃ hj : j < K, (x ⟨j, hj⟩).1 h.castSucc = s

noncomputable instance (h : Fin H) (s : S) (a : A) : DecidablePred (vis x h s a) :=
  Classical.decPred _
noncomputable instance (h : Fin H) (s : S) : DecidablePred (visS x h s) := Classical.decPred _

/-- Next state at episode `j` (arbitrary beyond the data). -/
noncomputable def nxt [Nonempty S] (h : Fin H) (j : ℕ) : S :=
  if hj : j < K then (x ⟨j, hj⟩).1 h.succ else Classical.arbitrary S

theorem Q_succ (k : ℕ) (h : Fin H) (s : S) (a : A) [Nonempty S] :
    (itr cb L sel r π₀ x (k + 1)).Q h s a =
      if vis x h s a k then
        (1 - onlineQRate H ((itr cb L sel r π₀ x k).N h s a + 1)) * (itr cb L sel r π₀ x k).Q h s a +
        onlineQRate H ((itr cb L sel r π₀ x k).N h s a + 1) * (r h s a +
          nextV (itr cb L sel r π₀ x k) h (nxt x h k) -
          penalty cb L H ((itr cb L sel r π₀ x k).N h s a + 1))
      else (itr cb L sel r π₀ x k).Q h s a := by
  by_cases hk : k < K
  · have e := congrArg (fun t ↦ t.1 s a) (stage_itr_succ cb L sel r π₀ x hk h)
    simp only [stage, stageUpd, trip] at e
    rw [e]
    by_cases hv : vis x h s a k
    · obtain ⟨_, hs, ha⟩ := hv
      rw [if_pos ⟨hk, hs, ha⟩]
      subst hs ha
      simp [nxt, hk]
    · rw [if_neg hv]
      by_cases hs : (x ⟨k, hk⟩).1 h.castSucc = s
      · subst hs
        have ha : (x ⟨k, hk⟩).2 h ≠ a := fun ha ↦ hv ⟨hk, rfl, ha⟩
        simp [Function.update_of_ne (Ne.symm ha)]
      · simp [Function.update_of_ne (Ne.symm hs)]
  · rw [if_neg (fun ⟨hk', _⟩ ↦ hk hk'), itr_succ_of_ge cb L sel r π₀ x (by omega)]

theorem N_succ (k : ℕ) (h : Fin H) (s : S) (a : A) :
    (itr cb L sel r π₀ x (k + 1)).N h s a =
      (itr cb L sel r π₀ x k).N h s a + if vis x h s a k then 1 else 0 := by
  by_cases hk : k < K
  · have e := congrArg (fun t ↦ t.2.2.1 s a) (stage_itr_succ cb L sel r π₀ x hk h)
    simp only [stage, stageUpd, trip] at e
    rw [e]
    by_cases hv : vis x h s a k
    · obtain ⟨_, hs, ha⟩ := hv
      rw [if_pos ⟨hk, hs, ha⟩]
      subst hs ha
      simp
    · rw [if_neg hv]
      by_cases hs : (x ⟨k, hk⟩).1 h.castSucc = s
      · subst hs
        have ha : (x ⟨k, hk⟩).2 h ≠ a := fun ha ↦ hv ⟨hk, rfl, ha⟩
        simp [Function.update_of_ne (Ne.symm ha)]
      · simp [Function.update_of_ne (Ne.symm hs)]
  · rw [if_neg (fun ⟨hk', _⟩ ↦ hk hk'), itr_succ_of_ge cb L sel r π₀ x (by omega), add_zero]

theorem N_eq_cnt (h : Fin H) (s : S) (a : A) :
    ∀ k, (itr cb L sel r π₀ x k).N h s a = cnt (vis x h s a) k := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih => rw [N_succ, ih, cnt_succ]

theorem V_succ (k : ℕ) (h : Fin H) (s : S) :
    (itr cb L sel r π₀ x (k + 1)).V h s =
      if visS x h s k then max ((itr cb L sel r π₀ x k).V h s)
        (actionMaximum ((itr cb L sel r π₀ x (k + 1)).Q h s))
      else (itr cb L sel r π₀ x k).V h s := by
  by_cases hk : k < K
  · have e := congrArg (fun t ↦ t.2.1 s) (stage_itr_succ cb L sel r π₀ x hk h)
    have eQ := congrArg (fun t ↦ t.1 s) (stage_itr_succ cb L sel r π₀ x hk h)
    simp only [stage, stageUpd, trip] at e eQ
    rw [e]
    by_cases hv : visS x h s k
    · obtain ⟨_, hs⟩ := hv
      rw [if_pos ⟨hk, hs⟩]
      subst hs
      rw [eQ]
      simp
    · rw [if_neg hv]
      have hs : (x ⟨k, hk⟩).1 h.castSucc ≠ s := fun hs ↦ hv ⟨hk, hs⟩
      simp [Function.update_of_ne (Ne.symm hs)]
  · rw [if_neg (fun ⟨hk', _⟩ ↦ hk hk'), itr_succ_of_ge cb L sel r π₀ x (by omega)]

theorem pol_succ (k : ℕ) (h : Fin H) (s : S) :
    (itr cb L sel r π₀ x (k + 1)).pol h s =
      if visS x h s k ∧ (itr cb L sel r π₀ x k).V h s < (itr cb L sel r π₀ x (k + 1)).V h s then
        sel ((itr cb L sel r π₀ x (k + 1)).Q h s)
      else (itr cb L sel r π₀ x k).pol h s := by
  by_cases hk : k < K
  · have e := congrArg (fun t ↦ t.2.2.2 s) (stage_itr_succ cb L sel r π₀ x hk h)
    have eQ := congrArg (fun t ↦ t.1 s) (stage_itr_succ cb L sel r π₀ x hk h)
    have eV := congrArg (fun t ↦ t.2.1 s) (stage_itr_succ cb L sel r π₀ x hk h)
    simp only [stage, stageUpd, trip] at e eQ eV
    rw [e]
    by_cases hv : visS x h s k
    · obtain ⟨hk', hs⟩ := hv
      have e' : hk' = hk := rfl
      subst e' hs
      have hv' : visS x h ((x ⟨k, hk'⟩).1 h.castSucc) k := ⟨hk', rfl⟩
      rw [eQ, eV]
      simp only [hv', true_and, Function.update_self]
      split_ifs <;> simp
    · have hs : (x ⟨k, hk⟩).1 h.castSucc ≠ s := fun hs ↦ hv ⟨hk, hs⟩
      have hc : ¬ (visS x h s k ∧ (itr cb L sel r π₀ x k).V h s <
          (itr cb L sel r π₀ x (k + 1)).V h s) := fun hc ↦ hv hc.1
      rw [if_neg hc]
      split_ifs <;> first | rfl | simp [Function.update_of_ne (Ne.symm hs)]
  · rw [if_neg (fun ⟨⟨hk', _⟩, _⟩ ↦ hk hk'), itr_succ_of_ge cb L sel r π₀ x (by omega)]

theorem Q_succ_of_not_visS (k : ℕ) (h : Fin H) (s : S) (hv : ¬ visS x h s k) (a : A)
    [Nonempty S] : (itr cb L sel r π₀ x (k + 1)).Q h s a = (itr cb L sel r π₀ x k).Q h s a := by
  rw [Q_succ, if_neg (fun ⟨hk, hs, _⟩ ↦ hv ⟨hk, hs⟩)]

/-! ## Invariants -/

theorem V_mono_succ (k : ℕ) (h : Fin H) (s : S) :
    (itr cb L sel r π₀ x k).V h s ≤ (itr cb L sel r π₀ x (k + 1)).V h s := by
  rw [V_succ]; split_ifs
  · exact le_max_left _ _
  · exact le_rfl

theorem V_mono {k k' : ℕ} (hk : k ≤ k') (h : Fin H) (s : S) :
    (itr cb L sel r π₀ x k).V h s ≤ (itr cb L sel r π₀ x k').V h s := by
  induction k', hk using Nat.le_induction with
  | base => exact le_rfl
  | succ k' _ ih => exact ih.trans (V_mono_succ cb L sel r π₀ x k' h s)

theorem V_nonneg (k : ℕ) (h : Fin H) (s : S) : 0 ≤ (itr cb L sel r π₀ x k).V h s :=
  (show (0 : ℝ) ≤ (itr cb L sel r π₀ x 0).V h s from le_rfl).trans
    (V_mono cb L sel r π₀ x (Nat.zero_le k) h s)

theorem nextV_nonneg (k : ℕ) (h : Fin H) (s : S) : 0 ≤ nextV (itr cb L sel r π₀ x k) h s := by
  unfold nextV; split_ifs
  · exact V_nonneg cb L sel r π₀ x k _ s
  · exact le_rfl

theorem nextV_mono {k k' : ℕ} (hk : k ≤ k') (h : Fin H) (s : S) :
    nextV (itr cb L sel r π₀ x k) h s ≤ nextV (itr cb L sel r π₀ x k') h s := by
  unfold nextV; split_ifs
  · exact V_mono cb L sel r π₀ x hk _ s
  · exact le_rfl

/-- `V_h(s) ≥ Q_h(s,a)` at every episode. -/
theorem Q_le_V [Nonempty S] (k : ℕ) (h : Fin H) (s : S) (a : A) :
    (itr cb L sel r π₀ x k).Q h s a ≤ (itr cb L sel r π₀ x k).V h s := by
  induction k with
  | zero => exact le_rfl
  | succ k ih =>
    by_cases hv : visS x h s k
    · rw [V_succ, if_pos hv]
      exact (le_actionMaximum _ a).trans (le_max_right _ _)
    · rw [Q_succ_of_not_visS cb L sel r π₀ x k h s hv, V_succ, if_neg hv]
      exact ih

theorem penalty_nonneg {cb L : ℝ} (hcb : 0 ≤ cb) (n : ℕ) : 0 ≤ penalty cb L H n :=
  mul_nonneg hcb (Real.sqrt_nonneg _)

theorem onlineQRate_le_one {n : ℕ} (hn : 1 ≤ n) : onlineQRate H n ≤ 1 := by
  unfold onlineQRate
  have h1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  rcases Nat.eq_zero_or_pos H with hH | hH
  · subst hH; simp only [Nat.cast_zero, zero_add]
    rw [div_le_one (by linarith)]; exact h1
  · rw [div_le_one (by positivity)]; linarith

theorem onlineQRate_nonneg' (n : ℕ) : 0 ≤ onlineQRate H n := by
  unfold onlineQRate; positivity

/-- Value bounds `Q_h, V_h ≤ H - h` (rewards in `[0,1]`, nonnegative penalty). -/
theorem le_bound [Nonempty S] {cb : ℝ} (hcb : 0 ≤ cb) (hr : ∀ h s a, r h s a ≤ 1) :
    ∀ k, ∀ h : Fin H, ∀ s, (∀ a, (itr cb L sel r π₀ x k).Q h s a ≤ (H : ℝ) - h.val) ∧
      (itr cb L sel r π₀ x k).V h s ≤ (H : ℝ) - h.val := by
  have hb : ∀ h : Fin H, (0 : ℝ) ≤ (H : ℝ) - h.val := fun h ↦ by
    have : (h.val : ℝ) ≤ H := by exact_mod_cast h.isLt.le
    linarith
  intro k
  induction k with
  | zero => intro h s; exact ⟨fun a ↦ hb h, hb h⟩
  | succ k ih =>
    have hnext : ∀ h : Fin H, ∀ t, nextV (itr cb L sel r π₀ x k) h t ≤ (H : ℝ) - h.val - 1 := by
      intro h t
      unfold nextV
      split_ifs with hh
      · have := (ih ⟨h.val + 1, hh⟩ t).2
        simp only at this; push_cast at this; linarith
      · have : h.val + 1 = H := by have := h.isLt; omega
        have : ((h.val : ℝ) + 1) = H := by exact_mod_cast this
        linarith
    have hQ : ∀ h : Fin H, ∀ s a, (itr cb L sel r π₀ x (k + 1)).Q h s a ≤ (H : ℝ) - h.val := by
      intro h s a
      rw [Q_succ]
      split_ifs
      · set n := (itr cb L sel r π₀ x k).N h s a + 1
        have h1 := onlineQRate_le_one (H := H) (show 1 ≤ n by omega)
        have h0 := onlineQRate_nonneg' (H := H) n
        have hq := (ih h s).1 a
        have ht : r h s a + nextV (itr cb L sel r π₀ x k) h (nxt x h k) - penalty cb L H n ≤
            (H : ℝ) - h.val := by
          have := hnext h (nxt x h k); have := hr h s a
          have := penalty_nonneg (H := H) (L := L) hcb n; linarith
        nlinarith
      · exact (ih h s).1 a
    intro h s
    refine ⟨hQ h s, ?_⟩
    rw [V_succ]
    split_ifs
    · refine max_le (ih h s).2 ?_
      unfold actionMaximum
      exact Finset.sup'_le _ _ fun a _ ↦ hQ h s a
    · exact (ih h s).2

/-! ## The unrolled Q -/

/-- The stage target at episode `j` (paper `r + V_{h+1}(s') - b`), with visit number `cnt j + 1`. -/
noncomputable def target [Nonempty S] (h : Fin H) (s : S) (a : A) (j : ℕ) : ℝ :=
  r h s a + nextV (itr cb L sel r π₀ x j) h (nxt x h j) -
    penalty cb L H (cnt (vis x h s a) j + 1)

/-- **Unrolling** (`eq:unroll-q-lcbq`): `Q_h^k(s,a) = Σ_{j<k visits} η^{N^k}_{N^j+1} y_j`. -/
theorem Q_unroll [Nonempty S] (h : Fin H) (s : S) (a : A) (k : ℕ) :
    (itr cb L sel r π₀ x k).Q h s a = ∑ j ∈ range k, (if vis x h s a j then
      onlineQRateWeight H (cnt (vis x h s a) k) (cnt (vis x h s a) j + 1) *
        target cb L sel r π₀ x h s a j else 0) := by
  refine unroll (vis x h s a) (fun k ↦ (itr cb L sel r π₀ x k).Q h s a)
    (target cb L sel r π₀ x h s a) rfl (fun k ↦ ?_) k
  dsimp only
  rw [Q_succ, N_eq_cnt]
  rfl

end StatisticalRL.LCBQFinite
