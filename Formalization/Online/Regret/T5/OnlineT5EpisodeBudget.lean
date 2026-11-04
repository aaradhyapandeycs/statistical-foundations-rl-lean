import Formalization.Online.Regret.T5.OnlineT5Shift

/-! Actual-law variance and gap proof component: OnlineT5EpisodeBudget.
This module supplies an intermediate proof, not the complete T56 theorem. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators
variable {State Action : Type*} [Fintype State] [Fintype Action]

theorem onlineT5_episode_square_budget
    (H : ℕ) (stage : Fin H → OnlineObservedPlanningStage State Action)
    (state : ℕ → State) (action : ℕ → Action) (L c₁ c₂ : ℝ)
    (hL : 0 ≤ L) (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂)
    (hgreedy : ∀ h : Fin H, letI : Nonempty Action := (stage h).environment.action_nonempty
      onlineCappedStageQ (H : ℝ) L c₁ c₂ (stage h)
        (onlineCappedBackwardValue (H : ℝ) L c₁ c₂ ((List.ofFn stage).drop (h.val + 1)))
        (state h.val) (action h.val) =
      actionMaximum (onlineCappedStageQ (H : ℝ) L c₁ c₂ (stage h)
        (onlineCappedBackwardValue (H : ℝ) L c₁ c₂ ((List.ofFn stage).drop (h.val + 1)))
        (state h.val))) :
    (∑ n ∈ Finset.range H,
      ((onlineCappedBackwardValue (H : ℝ) L c₁ c₂ ((List.ofFn stage).drop (n + 1)) (state (n + 1)))^2 -
       (if hn : n < H then (onlineObservedPlanningRow (stage ⟨n, hn⟩) (state n) (action n)).expectation
         (onlineCappedBackwardValue (H : ℝ) L c₁ c₂ ((List.ofFn stage).drop (n + 1))) else 0)^2)) ≤
    2 * (H : ℝ) * ((∑ n ∈ Finset.range H, onlineCappedEpisodeT2 H stage state action L c₁ c₂ n) + H) := by
  classical
  let v := fun n => onlineCappedBackwardValue (H : ℝ) L c₁ c₂ ((List.ofFn stage).drop n) (state n)
  let m := fun n => if hn : n < H then (onlineObservedPlanningRow (stage ⟨n, hn⟩) (state n) (action n)).expectation
         (onlineCappedBackwardValue (H : ℝ) L c₁ c₂ ((List.ofFn stage).drop (n + 1))) else 0
  have hterminal : v H = 0 := by
    dsimp [v]
    rw [List.drop_eq_nil_of_le (by simp)]
    rfl
  have hshift := onlineT5_square_shift_le H v m hterminal
  have hpoint (n : ℕ) (hn : n ∈ Finset.range H) :
      (v n)^2 - (m n)^2 ≤ 2 * (H : ℝ) *
        ((if hi : n < H then (stage ⟨n, hi⟩).environment.reward (state n) (action n) else 0) +
          onlineCappedEpisodeT2 H stage state action L c₁ c₂ n) := by
    have hnH := Finset.mem_range.mp hn
    let h : Fin H := ⟨n, hnH⟩
    letI : Nonempty Action := (stage h).environment.action_nonempty
    have hd : (List.ofFn stage).drop n = stage h :: (List.ofFn stage).drop (n + 1) := by
      have hi : n < (List.ofFn stage).length := by simpa using hnH
      simpa only [List.getElem_ofFn] using List.drop_eq_getElem_cons hi
    have hh := onlineT5_greedy_stage_square_bound (H : ℝ) L c₁ c₂ (stage h)
      ((List.ofFn stage).drop (n + 1)) (state n) (action n) (by positivity) hL hc₁ hc₂ (hgreedy h)
    simpa only [v, m, hd, dif_pos hnH, onlineCappedEpisodeT2, h] using hh
  have hs := Finset.sum_le_sum (s := Finset.range H) hpoint
  have hr : (∑ n ∈ Finset.range H, if hn : n < H then
      (stage ⟨n, hn⟩).environment.reward (state n) (action n) else 0) ≤ (H : ℝ) := by
    calc
      _ ≤ ∑ _n ∈ Finset.range H, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro n hn
        simp only [dif_pos (Finset.mem_range.mp hn)]
        exact (stage ⟨n, Finset.mem_range.mp hn⟩).environment.reward_le_one _ _
      _ = (H : ℝ) := by simp
  dsimp [v, m] at hshift
  have hH : 0 ≤ (H : ℝ) := by positivity
  calc
    _ ≤ _ := hshift
    _ ≤ _ := hs
    _ ≤ _ := by
      rw [← Finset.mul_sum, Finset.sum_add_distrib]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      linarith
end StatisticalRL.OnlineRL
