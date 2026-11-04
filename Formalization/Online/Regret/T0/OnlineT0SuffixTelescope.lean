import Formalization.Online.Regret.Telescope
import Mathlib.Algebra.BigOperators.Intervals

/-! Same-experiment suffix proof component: OnlineT0SuffixTelescope.
Scope and source confidence are established only by the final applying theorem. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators
variable {State Action : Type*} [Fintype State] [Fintype Action]

theorem onlineCappedEpisode_realized_suffix_telescope
    (H j : ℕ) (hj : j ≤ H) (stage : Fin H → OnlineObservedPlanningStage State Action)
    (state : ℕ → State) (action : ℕ → Action)
    (δ' c₁ c₂ : ℝ) (hδ' : 0 < δ') (hδ'small : δ' ≤ 1 / 100)
    (hc₁ : 4 ≤ c₁) (hc₂ : c₁ ^ 2 ≤ c₂)
    (hAction : ∀ h : Fin H, Nonempty Action)
    (hgreedy : ∀ h : Fin H,
      letI : Nonempty Action := hAction h
      onlineCappedStageQ (H : ℝ) (Real.log (1 / δ')) c₁ c₂ (stage h)
        (onlineCappedBackwardValue (H : ℝ) (Real.log (1 / δ')) c₁ c₂
          ((List.ofFn stage).drop (h.val + 1))) (state h.val) (action h.val) =
      actionMaximum (onlineCappedStageQ (H : ℝ) (Real.log (1 / δ')) c₁ c₂ (stage h)
        (onlineCappedBackwardValue (H : ℝ) (Real.log (1 / δ')) c₁ c₂
          ((List.ofFn stage).drop (h.val + 1))) (state h.val))) :
    onlineCappedEpisodeValueAlongPath stage state (H : ℝ) (Real.log (1 / δ')) c₁ c₂ j ≤
      ∑ n ∈ Finset.Ico j H,
        onlineCappedEpisodeTelescopeSummand H stage state action (Real.log (1 / δ')) c₁ c₂ n := by
  let stages := List.ofFn stage
  have hL : 0 ≤ Real.log (1 / δ') := by
    have hlog := onlineSmallConfidence_log_ge_one δ' hδ' hδ'small
    linarith
  have hc₁' : 0 ≤ c₁ := by linarith
  have hc₂' : 0 ≤ c₂ := by nlinarith [hc₁]
  let v : ℕ → ℝ := fun n =>
    onlineCappedBackwardValue (H : ℝ) (Real.log (1 / δ')) c₁ c₂
      (stages.drop n) (state n)
  let g : ℕ → ℝ := fun n =>
    onlineCappedEpisodeTelescopeSummand H stage state action (Real.log (1 / δ')) c₁ c₂ n
  have hstep : ∀ n, v n ≤ g n + v (n + 1) := by
    intro n
    by_cases hn : n < H
    · let h : Fin H := ⟨n, hn⟩
      have hdrop : stages.drop n = stage h :: stages.drop (n + 1) := by
        have hi : n < stages.length := by simpa [stages] using hn
        simpa only [stages, List.getElem_ofFn] using List.drop_eq_getElem_cons hi
      have hnext : ∀ x, 0 ≤ onlineCappedBackwardValue (H : ℝ) (Real.log (1 / δ')) c₁ c₂
          (stages.drop (n + 1)) x := by
        exact fun x => (onlineCappedBackwardValue_range (H : ℝ) (Real.log (1 / δ')) c₁ c₂
          (by positivity) hL hc₁' hc₂'  (stages.drop (n + 1)) x).1
      have hrow := onlineCappedStage_greedy_step_telescope (H : ℝ) (Real.log (1 / δ')) c₁ c₂
        (stage h) (stages.drop (n + 1)) (state n) (state (n + 1)) (action n)
        (by positivity) hL hc₁' hc₂' (hAction h) (hgreedy h)
      have hcurrent : v n =
          onlineCappedBackwardValue (H : ℝ) (Real.log (1 / δ')) c₁ c₂
            (stage h :: stages.drop (n + 1)) (state n) := by
        simp only [v]
        rw [hdrop]
      have hgoal := hrow
      rw [← hcurrent] at hgoal
      simpa [g, hn, h, v, stages, onlineCappedEpisodeTelescopeSummand] using hgoal
    · have hlen : stages.length = H := by simp [stages]
      have hdropn : stages.drop n = [] := List.drop_eq_nil_of_le (by omega)
      have hdropSucc : stages.drop (n + 1) = [] :=
        List.drop_eq_nil_of_le (by omega)
      have hvn : v n = 0 := by simp [v, hdropn, onlineCappedBackwardValue]
      have hvSucc : v (n + 1) = 0 :=
        by simp [v, hdropSucc, onlineCappedBackwardValue]
      simp [g, onlineCappedEpisodeTelescopeSummand, hn, hvn, hvSucc]
  have hterminal : v H = 0 := by
    have hlen : stages.length = H := by simp [stages]
    have hdrop : stages.drop H = [] := List.drop_eq_nil_of_le (by omega)
    simp [v, hdrop, onlineCappedBackwardValue]
  have htel := onlineRealSequence_telescope_from (H - j) j v g hstep
  have hend : j + (H - j) = H := Nat.add_sub_of_le hj
  rw [hend, hterminal, add_zero] at htel
  have hsum : (∑ n ∈ Finset.range (H - j), g (j + n)) =
      ∑ n ∈ Finset.Ico j H, g n := (Finset.sum_Ico_eq_sum_range g j H).symm
  rw [hsum] at htel
  exact htel

end StatisticalRL.OnlineRL
