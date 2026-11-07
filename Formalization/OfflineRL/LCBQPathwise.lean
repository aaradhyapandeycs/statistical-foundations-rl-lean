import Formalization.OfflineRL.LCBQDefinitions
import Formalization.Online.QLearning.ScalarRecurrence

/-!
# LCB-Q: pathwise facts about the algorithm run

Deterministic properties of `run` (`alg:q-infinite-lcb`, `offlineRL.tex:1701–1745`) for every
data sequence: one-step equations, visit counts as `Nat.count`, the unrolled Q-iterate
(`eq:unroll-q-lcbq`, `:4436–4443`), value bounds (`eq:value-bounded-lcbq`, `:1840–1845`),
monotonicity of `V_t`, `V_t ≥ max_a Q_t`, the last-strict-increase description of `π_t`
(`:4590–4606`) and causality (the run up to time `u` depends only on the first `u` samples).
-/

open scoped BigOperators

namespace StatisticalRL.OfflineRL.LCBQ

open StatisticalRL StatisticalRL.OnlineRL
open Classical

set_option linter.unusedSectionVars false

variable {S A : Type*} [Fintype S] [Fintype A]

section Step

variable (M : DiscountedMDP S A) (cb ι : ℝ) (H : ℕ) (sel : (A → ℝ) → A)
  (σ : Iterate S A) (x : (S × A) × S)

theorem step_Q (s : S) (a : A) :
    (step M cb ι H sel σ x).Q s a =
      if s = x.1.1 ∧ a = x.1.2 then
        (1 - onlineQRate H (σ.count x.1.1 x.1.2 + 1)) * σ.Q x.1.1 x.1.2 +
          onlineQRate H (σ.count x.1.1 x.1.2 + 1) *
            (M.reward x.1.1 x.1.2 + M.discount * σ.V x.2 -
              penalty cb M.discount ι H (σ.count x.1.1 x.1.2 + 1))
      else σ.Q s a := rfl

theorem step_count (s : S) (a : A) :
    (step M cb ι H sel σ x).count s a =
      if s = x.1.1 ∧ a = x.1.2 then σ.count x.1.1 x.1.2 + 1 else σ.count s a := rfl

theorem step_V [Nonempty A] (s : S) :
    (step M cb ι H sel σ x).V s =
      if s = x.1.1 then max (σ.V x.1.1) (actionMaximum ((step M cb ι H sel σ x).Q x.1.1))
      else σ.V s := rfl

theorem step_policy [Nonempty A] (s : S) :
    (step M cb ι H sel σ x).policy s =
      if s = x.1.1 ∧ σ.V x.1.1 <
          max (σ.V x.1.1) (actionMaximum ((step M cb ι H sel σ x).Q x.1.1)) then
        sel ((step M cb ι H sel σ x).Q x.1.1)
      else σ.policy s := rfl

theorem step_Q_of_ne (s : S) (hs : s ≠ x.1.1) (a : A) :
    (step M cb ι H sel σ x).Q s a = σ.Q s a := by
  rw [step_Q, if_neg (fun h => hs h.1)]

theorem step_V_of_ne [Nonempty A] (s : S) (hs : s ≠ x.1.1) :
    (step M cb ι H sel σ x).V s = σ.V s := by
  rw [step_V, if_neg hs]

theorem step_V_self [Nonempty A] :
    (step M cb ι H sel σ x).V x.1.1 =
      max (σ.V x.1.1) (actionMaximum ((step M cb ι H sel σ x).Q x.1.1)) := by
  rw [step_V, if_pos rfl]

theorem step_policy_of_ne [Nonempty A] (s : S) (hs : s ≠ x.1.1) :
    (step M cb ι H sel σ x).policy s = σ.policy s := by
  rw [step_policy, if_neg (fun h => hs h.1)]

end Step

section Run

variable (M : DiscountedMDP S A) (cb δ : ℝ) (sel : (A → ℝ) → A) (π₀ : S → A)
  {T : ℕ} (data : Fin T → (S × A) × S)

theorem run_zero : run M cb δ sel π₀ data 0 = init π₀ := rfl

theorem run_succ_of_lt {t : ℕ} (h : t < T) :
    run M cb δ sel π₀ data (t + 1) =
      step M cb (iota S A T δ) (horizon M.discount (iota S A T δ)) sel
        (run M cb δ sel π₀ data t) (data ⟨t, h⟩) := by
  rw [run, dif_pos h]

theorem run_succ_of_ge {t : ℕ} (h : T ≤ t) :
    run M cb δ sel π₀ data (t + 1) = run M cb δ sel π₀ data t := by
  rw [run, dif_neg (by omega)]

/-- The visit predicate of `sa`: sample `u` exists and has label `sa`. -/
def visitPred (sa : S × A) (u : ℕ) : Prop := ∃ h : u < T, (data ⟨u, h⟩).1 = sa

noncomputable instance visitPred_decidable (sa : S × A) : DecidablePred (visitPred data sa) :=
  Classical.decPred _

theorem visitTime_eq (sa : S × A) (i : ℕ) :
    visitTime data sa i = Nat.nth (visitPred data sa) i := rfl

theorem visitPred_iff {u : ℕ} (h : u < T) (s : S) (a : A) :
    visitPred data (s, a) u ↔ s = (data ⟨u, h⟩).1.1 ∧ a = (data ⟨u, h⟩).1.2 := by
  constructor
  · rintro ⟨h', he⟩
    have he' : (data ⟨u, h⟩).1 = (s, a) := he
    rw [he']
    exact ⟨rfl, rfl⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h, by rw [h1, h2]⟩

/-- `n_t(s,a)` is the number of visits among the first `t` samples (`offlineRL.tex:1815`). -/
theorem run_count {t : ℕ} (ht : t ≤ T) (s : S) (a : A) :
    (run M cb δ sel π₀ data t).count s a = Nat.count (visitPred data (s, a)) t := by
  induction t generalizing s a with
  | zero => simp [run_zero, init]
  | succ t ih =>
    have htT : t < T := by omega
    rw [run_succ_of_lt M cb δ sel π₀ data htT, step_count, Nat.count_succ]
    by_cases hx : s = (data ⟨t, htT⟩).1.1 ∧ a = (data ⟨t, htT⟩).1.2
    · rw [if_pos hx, if_pos ((visitPred_iff data htT s a).2 hx)]
      obtain ⟨h1, h2⟩ := hx
      rw [← h1, ← h2, ih (by omega)]
    · rw [if_neg hx, if_neg (fun hp => hx ((visitPred_iff data htT s a).1 hp)), ih (by omega)]
      simp

theorem lt_card_of_lt_count {p : ℕ → Prop} [DecidablePred p] {i t : ℕ} (hi : i < Nat.count p t) :
    ∀ hf : (setOf p).Finite, i < hf.toFinset.card := by
  intro hf
  refine lt_of_lt_of_le hi ?_
  rw [Nat.count_eq_card_filter_range]
  apply Finset.card_le_card
  intro x hx
  rw [Finset.mem_filter] at hx
  exact hf.mem_toFinset.2 hx.2

theorem visitTime_lt {sa : S × A} {i t : ℕ} (hi : i < Nat.count (visitPred data sa) t) :
    visitTime data sa i < t := Nat.nth_lt_of_lt_count (p := visitPred data sa) hi

theorem visitPred_visitTime {sa : S × A} {i t : ℕ} (hi : i < Nat.count (visitPred data sa) t) :
    visitPred data sa (visitTime data sa i) :=
  Nat.nth_mem (p := visitPred data sa) i (lt_card_of_lt_count hi)

theorem count_visitTime {sa : S × A} {i t : ℕ} (hi : i < Nat.count (visitPred data sa) t) :
    Nat.count (visitPred data sa) (visitTime data sa i) = i :=
  Nat.count_nth (p := visitPred data sa) (lt_card_of_lt_count hi)

/-- The target of the `(i+1)`-st visit to `sa` in the unrolled recursion
`eq:unroll-q-lcbq`: `r(s,a) + γ V_{k_{i+1}-1}(s'_{k_{i+1}}) − b_{i+1}`; `0` if that visit does
not exist. -/
noncomputable def visitTarget (sa : S × A) (i : ℕ) : ℝ :=
  if h : visitTime data sa i < T then
    M.reward sa.1 sa.2 + M.discount *
      (run M cb δ sel π₀ data (visitTime data sa i)).V (data ⟨visitTime data sa i, h⟩).2 -
      penalty cb M.discount (iota S A T δ) (horizon M.discount (iota S A T δ)) (i + 1)
  else 0

theorem visitTarget_eq {sa : S × A} {i u : ℕ} (hu : visitTime data sa i = u) (h : u < T) :
    visitTarget M cb δ sel π₀ data sa i =
      M.reward sa.1 sa.2 + M.discount * (run M cb δ sel π₀ data u).V (data ⟨u, h⟩).2 -
        penalty cb M.discount (iota S A T δ) (horizon M.discount (iota S A T δ)) (i + 1) := by
  subst hu
  rw [visitTarget, dif_pos h]

theorem run_Q_eq_recurrence {t : ℕ} (ht : t ≤ T) (s : S) (a : A) :
    (run M cb δ sel π₀ data t).Q s a =
      qLearningScalarRecurrence (horizon M.discount (iota S A T δ)) 0
        (fun j => visitTarget M cb δ sel π₀ data (s, a) (j - 1))
        (Nat.count (visitPred data (s, a)) t) := by
  induction t generalizing s a with
  | zero => simp [run_zero, init, qLearningScalarRecurrence]
  | succ t ih =>
    have htT : t < T := by omega
    rw [run_succ_of_lt M cb δ sel π₀ data htT, step_Q, Nat.count_succ]
    by_cases hx : s = (data ⟨t, htT⟩).1.1 ∧ a = (data ⟨t, htT⟩).1.2
    · have hp := (visitPred_iff data htT s a).2 hx
      rw [if_pos hx, if_pos hp]
      have hcnt := run_count M cb δ sel π₀ data (le_of_lt htT) s a
      have hv : visitTime data (s, a) (Nat.count (visitPred data (s, a)) t) = t :=
        Nat.nth_count (p := visitPred data (s, a)) hp
      obtain ⟨h1, h2⟩ := hx
      rw [qLearningScalarRecurrence, ← ih (by omega) s a, Nat.add_sub_cancel,
        visitTarget_eq M cb δ sel π₀ data hv htT, ← hcnt]
      rw [← h1, ← h2]
    · rw [if_neg hx, if_neg (fun hp => hx ((visitPred_iff data htT s a).1 hp)), add_zero,
        ih (by omega)]

theorem sum_Icc_one_eq_sum_range (f : ℕ → ℝ) (n : ℕ) :
    ∑ i ∈ Finset.Icc 1 n, f i = ∑ i ∈ Finset.range n, f (i + 1) := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ]

/-- The unrolled Q-iterate (`eq:unroll-q-lcbq`, first line):
`Q_t(s,a) = Σ_{i=1}^{n} η_i^n {r(s,a) + γ V_{k_i-1}(s'_{k_i}) − b_i}` with `n = n_t(s,a)`,
written with zero-based `i`. For `n = 0` it reads `Q_t(s,a) = 0`. -/
theorem run_Q_unroll {t : ℕ} (ht : t ≤ T) (s : S) (a : A) :
    (run M cb δ sel π₀ data t).Q s a =
      ∑ i ∈ Finset.range ((run M cb δ sel π₀ data t).count s a),
        onlineQRateWeight (horizon M.discount (iota S A T δ))
          ((run M cb δ sel π₀ data t).count s a) (i + 1) *
          visitTarget M cb δ sel π₀ data (s, a) i := by
  rw [run_Q_eq_recurrence M cb δ sel π₀ data ht, qLearningScalarRecurrence_eq_weighted,
    run_count M cb δ sel π₀ data ht, mul_zero, zero_add, sum_Icc_one_eq_sum_range]
  rfl

/-- `V_t ≥ 0`. -/
theorem run_V_nonneg (t : ℕ) (s : S) : 0 ≤ (run M cb δ sel π₀ data t).V s := by
  letI : Nonempty A := M.action_nonempty
  induction t generalizing s with
  | zero => simp [run_zero, init]
  | succ t ih =>
    by_cases htT : t < T
    · rw [run_succ_of_lt M cb δ sel π₀ data htT]
      by_cases hs : s = (data ⟨t, htT⟩).1.1
      · subst hs
        rw [step_V_self]
        exact le_max_of_le_left (ih _)
      · rw [step_V_of_ne _ _ _ _ _ _ _ _ hs]
        exact ih s
    · rw [run_succ_of_ge M cb δ sel π₀ data (by omega)]
      exact ih s

/-- One-step monotonicity of the value iterate (`eq:Q-lcb-update-rule-V`). -/
theorem run_V_le_succ (t : ℕ) (s : S) :
    (run M cb δ sel π₀ data t).V s ≤ (run M cb δ sel π₀ data (t + 1)).V s := by
  letI : Nonempty A := M.action_nonempty
  by_cases htT : t < T
  · rw [run_succ_of_lt M cb δ sel π₀ data htT]
    by_cases hs : s = (data ⟨t, htT⟩).1.1
    · subst hs
      rw [step_V_self]
      exact le_max_left _ _
    · rw [step_V_of_ne _ _ _ _ _ _ _ _ hs]
  · rw [run_succ_of_ge M cb δ sel π₀ data (by omega)]

/-- `V_u ≤ V_t` for `u ≤ t`. -/
theorem run_V_mono {u t : ℕ} (hut : u ≤ t) (s : S) :
    (run M cb δ sel π₀ data u).V s ≤ (run M cb δ sel π₀ data t).V s := by
  induction t, hut using Nat.le_induction with
  | base => exact le_rfl
  | succ t _ ih => exact ih.trans (run_V_le_succ M cb δ sel π₀ data t s)

/-- `V_{t+1}(s) ≤ max{V_t(s), max_a Q_{t+1}(s,a)}`. -/
theorem run_V_succ_le [Nonempty A] {t : ℕ} (htT : t < T) (s : S) :
    (run M cb δ sel π₀ data (t + 1)).V s ≤
      max ((run M cb δ sel π₀ data t).V s)
        (actionMaximum ((run M cb δ sel π₀ data (t + 1)).Q s)) := by
  rw [run_succ_of_lt M cb δ sel π₀ data htT]
  by_cases hs : s = (data ⟨t, htT⟩).1.1
  · subst hs
    rw [step_V_self]
  · rw [step_V_of_ne _ _ _ _ _ _ _ _ hs]
    exact le_max_left _ _

/-- `V_t(s) ≥ max_a Q_t(s,a)` (used at `offlineRL.tex:1963–1965`). -/
theorem actionMaximum_le_run_V [Nonempty A] (t : ℕ) (s : S) :
    actionMaximum ((run M cb δ sel π₀ data t).Q s) ≤ (run M cb δ sel π₀ data t).V s := by
  induction t generalizing s with
  | zero =>
    simp only [run_zero, init]
    exact Finset.sup'_le _ _ (fun _ _ => le_rfl)
  | succ t ih =>
    by_cases htT : t < T
    · rw [run_succ_of_lt M cb δ sel π₀ data htT]
      by_cases hs : s = (data ⟨t, htT⟩).1.1
      · subst hs
        rw [step_V_self]
        exact le_max_right _ _
      · rw [step_V_of_ne _ _ _ _ _ _ _ _ hs]
        have hQ : (step M cb (iota S A T δ) (horizon M.discount (iota S A T δ)) sel
            (run M cb δ sel π₀ data t) (data ⟨t, htT⟩)).Q s = (run M cb δ sel π₀ data t).Q s := by
          funext a
          exact step_Q_of_ne _ _ _ _ _ _ _ _ hs a
        rw [hQ]
        exact ih s
    · rw [run_succ_of_ge M cb δ sel π₀ data (by omega)]
      exact ih s

/-- The value bounds `0 ≤ V_t ≤ 1/(1-γ)` (`eq:value-bounded-lcbq`), together with
`Q_t ≤ 1/(1-γ)`, for a nonnegative penalty constant. -/
theorem run_bounds (hcb : 0 ≤ cb) (t : ℕ) :
    (∀ s a, (run M cb δ sel π₀ data t).Q s a ≤ 1 / (1 - M.discount)) ∧
      ∀ s, 0 ≤ (run M cb δ sel π₀ data t).V s ∧
        (run M cb δ sel π₀ data t).V s ≤ 1 / (1 - M.discount) := by
  letI : Nonempty A := M.action_nonempty
  have hγ0 := M.discount_nonneg
  have hγ1 := M.discount_lt_one
  have hc0 : 0 < 1 / (1 - M.discount) := by apply div_pos one_pos; linarith
  have hne : 1 - M.discount ≠ 0 := (by linarith : (0 : ℝ) < 1 - M.discount).ne'
  have hc : 1 + M.discount * (1 / (1 - M.discount)) = 1 / (1 - M.discount) := by
    field_simp
    ring
  induction t with
  | zero =>
    simp only [run_zero, init]
    exact ⟨fun _ _ => hc0.le, fun _ => ⟨le_rfl, hc0.le⟩⟩
  | succ t ih =>
    by_cases htT : t < T
    · obtain ⟨ihQ, ihV⟩ := ih
      set σ := run M cb δ sel π₀ data t with hσ
      set x := data ⟨t, htT⟩ with hxdef
      set ι := iota S A T δ
      set H := horizon M.discount ι
      rw [run_succ_of_lt M cb δ sel π₀ data htT]
      have hQ' : ∀ s a, (step M cb ι H sel σ x).Q s a ≤ 1 / (1 - M.discount) := by
        intro s a
        rw [step_Q]
        split_ifs with hx
        · set k := σ.count x.1.1 x.1.2 + 1
          have hk : (1 : ℝ) ≤ k := by simp [k]
          have hHk : (0 : ℝ) < (H : ℝ) + k := by positivity
          have hη0 : 0 ≤ onlineQRate H k := by
            unfold onlineQRate; positivity
          have hη1 : onlineQRate H k ≤ 1 := by
            unfold onlineQRate
            rw [div_le_one hHk]
            linarith
          have hb : 0 ≤ penalty cb M.discount ι H k := by
            unfold penalty
            exact mul_nonneg hcb (Real.sqrt_nonneg _)
          have hr := M.reward_le_one x.1.1 x.1.2
          have hVy := (ihV x.2).2
          have htarget : M.reward x.1.1 x.1.2 + M.discount * σ.V x.2 -
              penalty cb M.discount ι H k ≤ 1 / (1 - M.discount) := by
            have := mul_le_mul_of_nonneg_left hVy hγ0
            linarith
          have hQx := ihQ x.1.1 x.1.2
          calc (1 - onlineQRate H k) * σ.Q x.1.1 x.1.2 + onlineQRate H k *
                (M.reward x.1.1 x.1.2 + M.discount * σ.V x.2 - penalty cb M.discount ι H k)
              ≤ (1 - onlineQRate H k) * (1 / (1 - M.discount)) +
                  onlineQRate H k * (1 / (1 - M.discount)) := by
                gcongr
                linarith
            _ = 1 / (1 - M.discount) := by ring
        · exact ihQ s a
      refine ⟨hQ', fun s => ?_⟩
      have hmax : actionMaximum ((step M cb ι H sel σ x).Q x.1.1) ≤ 1 / (1 - M.discount) :=
        Finset.sup'_le _ _ (fun a _ => hQ' x.1.1 a)
      by_cases hs : s = x.1.1
      · subst hs
        rw [step_V_self]
        exact ⟨le_max_of_le_left (ihV _).1, max_le (ihV _).2 hmax⟩
      · rw [step_V_of_ne _ _ _ _ _ _ _ _ hs]
        exact ihV s
    · rw [run_succ_of_ge M cb δ sel π₀ data (by omega)]
      exact ih

/-- The last strict increase of `V_·(s)` (`offlineRL.tex:4590–4606`): if `V_t(s) > 0` there is a
time `1 ≤ τ ≤ min(t,T)` with `π_t(s) = sel(Q_τ(s,·))` and `V_t(s) = max_a Q_τ(s,a)`. -/
theorem run_policy_lastIncrease [Nonempty A] (t : ℕ) (s : S)
    (hpos : 0 < (run M cb δ sel π₀ data t).V s) :
    ∃ τ, 1 ≤ τ ∧ τ ≤ t ∧ τ ≤ T ∧
      (run M cb δ sel π₀ data t).policy s = sel ((run M cb δ sel π₀ data τ).Q s) ∧
      (run M cb δ sel π₀ data t).V s = actionMaximum ((run M cb δ sel π₀ data τ).Q s) := by
  induction t generalizing s with
  | zero => simp [run_zero, init] at hpos
  | succ t ih =>
    by_cases htT : t < T
    · have hrun := run_succ_of_lt M cb δ sel π₀ data htT
      set σ := run M cb δ sel π₀ data t with hσ
      set x := data ⟨t, htT⟩ with hxdef
      by_cases hs : s = x.1.1
      · subst hs
        by_cases hlt : σ.V x.1.1 < max (σ.V x.1.1) (actionMaximum
            ((step M cb (iota S A T δ) (horizon M.discount (iota S A T δ)) sel σ x).Q x.1.1))
        · refine ⟨t + 1, le_add_self, le_rfl, htT, ?_, ?_⟩
          · rw [hrun, step_policy, if_pos ⟨rfl, hlt⟩]
          · rw [hrun, step_V_self]
            have hm := (lt_max_iff.mp hlt).resolve_left (lt_irrefl _)
            exact max_eq_right hm.le
        · have hV : (run M cb δ sel π₀ data (t + 1)).V x.1.1 = σ.V x.1.1 := by
            rw [hrun, step_V_self]
            exact le_antisymm (not_lt.mp hlt) (le_max_left _ _)
          have hP : (run M cb δ sel π₀ data (t + 1)).policy x.1.1 = σ.policy x.1.1 := by
            rw [hrun, step_policy, if_neg (fun h => hlt h.2)]
          rw [hV] at hpos ⊢
          obtain ⟨τ, h1, h2, h3, h4, h5⟩ := ih x.1.1 hpos
          exact ⟨τ, h1, by omega, h3, by rw [hP]; exact h4, h5⟩
      · have hV : (run M cb δ sel π₀ data (t + 1)).V s = σ.V s := by
          rw [hrun, step_V_of_ne _ _ _ _ _ _ _ _ hs]
        have hP : (run M cb δ sel π₀ data (t + 1)).policy s = σ.policy s := by
          rw [hrun, step_policy_of_ne _ _ _ _ _ _ _ _ hs]
        rw [hV] at hpos ⊢
        obtain ⟨τ, h1, h2, h3, h4, h5⟩ := ih s hpos
        exact ⟨τ, h1, by omega, h3, by rw [hP]; exact h4, h5⟩
    · have hrun := run_succ_of_ge M cb δ sel π₀ data (t := t) (by omega)
      rw [hrun] at hpos ⊢
      obtain ⟨τ, h1, h2, h3, h4, h5⟩ := ih s hpos
      exact ⟨τ, h1, by omega, h3, h4, h5⟩

/-- Causality: if two data sequences agree on the samples with index `< u`, the runs agree up to
time `u`. -/
theorem run_congr_prefix {data' : Fin T → (S × A) × S} {u : ℕ}
    (h : ∀ i : Fin T, i.val < u → data i = data' i) {t : ℕ} (htu : t ≤ u) :
    run M cb δ sel π₀ data t = run M cb δ sel π₀ data' t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    by_cases htT : t < T
    · rw [run_succ_of_lt M cb δ sel π₀ data htT, run_succ_of_lt M cb δ sel π₀ data' htT,
        ih (by omega), h ⟨t, htT⟩ (by simp; omega)]
    · rw [run_succ_of_ge M cb δ sel π₀ data (by omega),
        run_succ_of_ge M cb δ sel π₀ data' (by omega), ih (by omega)]

end Run

end StatisticalRL.OfflineRL.LCBQ
