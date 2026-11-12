import Formalization.Online.Regret.Telescope

/-! Nonnegative-parameter telescopes for the corrected zero-count UCBVI backup. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators
open MeasureTheory ProbabilityTheory
variable {State Action : Type*} [Fintype State] [Fintype Action]

/-- The pathwise telescope uses only nonnegative log and bonus parameters. -/
theorem onlineCappedEpisode_realized_telescope_nonnegative
    (H : ℕ) (stage : Fin H → OnlineObservedPlanningStage State Action)
    (state : ℕ → State) (action : ℕ → Action)
    (L c₁ c₂ : ℝ) (hL : 0 ≤ L) (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂)
    (hAction : ∀ h : Fin H, Nonempty Action)
    (hgreedy : ∀ h : Fin H,
      letI : Nonempty Action := hAction h
      onlineCappedStageQ (H : ℝ) (L) c₁ c₂ (stage h)
        (onlineCappedBackwardValue (H : ℝ) (L) c₁ c₂
          ((List.ofFn stage).drop (h.val + 1))) (state h.val) (action h.val) =
      actionMaximum (onlineCappedStageQ (H : ℝ) (L) c₁ c₂ (stage h)
        (onlineCappedBackwardValue (H : ℝ) (L) c₁ c₂
          ((List.ofFn stage).drop (h.val + 1))) (state h.val))) :
    onlineCappedEpisodeValueAlongPath stage state (H : ℝ) (L) c₁ c₂ 0 ≤
      ∑ n ∈ Finset.range H,
        onlineCappedEpisodeTelescopeSummand H stage state action (L) c₁ c₂ n := by
  let stages := List.ofFn stage
  let v : ℕ → ℝ := fun n =>
    onlineCappedBackwardValue (H : ℝ) (L) c₁ c₂
      (stages.drop n) (state n)
  let g : ℕ → ℝ := fun n =>
    onlineCappedEpisodeTelescopeSummand H stage state action (L) c₁ c₂ n
  have hstep : ∀ n, v n ≤ g n + v (n + 1) := by
    intro n
    by_cases hn : n < H
    · let h : Fin H := ⟨n, hn⟩
      have hdrop : stages.drop n = stage h :: stages.drop (n + 1) := by
        have hi : n < stages.length := by simpa [stages] using hn
        simpa only [stages, List.getElem_ofFn] using List.drop_eq_getElem_cons hi
      have hnext : ∀ x, 0 ≤ onlineCappedBackwardValue (H : ℝ) (L) c₁ c₂
          (stages.drop (n + 1)) x := by
        exact fun x => (onlineCappedBackwardValue_range (H : ℝ) (L) c₁ c₂
          (by positivity) hL hc₁ hc₂  (stages.drop (n + 1)) x).1
      have hrow := onlineCappedStage_greedy_step_telescope (H : ℝ) (L) c₁ c₂
        (stage h) (stages.drop (n + 1)) (state n) (state (n + 1)) (action n)
        (by positivity) hL hc₁ hc₂ (hAction h) (hgreedy h)
      have hcurrent : v n =
          onlineCappedBackwardValue (H : ℝ) (L) c₁ c₂
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
  have htel := onlineRealSequence_telescope_from H 0 v g hstep
  have hresult : v 0 ≤ ∑ n ∈ Finset.range H, g n := by
    simpa [hterminal] using htel
  simpa [v, g, stages, onlineCappedEpisodeValueAlongPath] using hresult

end StatisticalRL.OnlineRL
