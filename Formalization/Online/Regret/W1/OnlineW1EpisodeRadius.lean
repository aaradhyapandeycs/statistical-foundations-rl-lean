import Formalization.Online.Regret.W1.OnlineW1ObservedPointwise

/-! OnlineW1EpisodeRadius: an intermediate component for the corrected-zero-count, fixed-tie W₁ analysis. Source-facing K≥2 scope and remaining W₂/regret obligations are stated at the final export. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators
variable {State Action : Type*} [Fintype State] [Fintype Action]
noncomputable local instance OnlineW1EpisodeRadiusLocalInstance1 : DecidableEq State := Classical.decEq State
noncomputable local instance OnlineW1EpisodeRadiusLocalInstance2 : DecidableEq Action := Classical.decEq Action

noncomputable def onlineActualEpisodeW1RadiusSum
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (initial : Fin K → State) (fallback : State)
    (path : OnlineOutcomePath State (K * H)) (k : Fin K)
    (δ' c₁ c₂ : ℝ) : ℝ :=
    let planner := onlineCappedGreedyPlanner E (Real.log (1 / δ')) c₁ c₂
    let history := onlineSequentialPathHistory
      (onlineEpisodicChoose H K hH initial fallback planner) (K * H) [] path
    let prehist := history.take (k.val * H)
    let stage : Fin H → OnlineObservedPlanningStage State Action :=
      fun h => onlineHistoryPlanningStage E prehist h
    let state : ℕ → State := fun n =>
      onlineEpisodicCurrentState H K initial fallback
        (history.take (k.val * H + n))
    let action : ℕ → Action := fun n =>
      if hn : n < H then
        (history.get ⟨k.val * H + n, by
          have hlen := onlineSequentialPathHistory_length
            (onlineEpisodicChoose H K hH initial fallback planner) (K * H) [] path
          rw [hlen]
          simp only [List.length_nil, zero_add]
          calc
            k.val * H + n < k.val * H + H := Nat.add_lt_add_left hn _
            _ = (k.val + 1) * H := by rw [Nat.succ_mul]
            _ ≤ K * H := Nat.mul_le_mul_right H (Nat.succ_le_of_lt k.isLt)⟩).1.2.2
      else Classical.choice ((E ⟨0, hH⟩).action_nonempty)
    ∑ n ∈ Finset.range H,
      if hn : n < H then
        let h : Fin H := ⟨n, hn⟩
        let row := (h, (state n, action n))
        let count := (onlineRowOutcomes prehist row).length
        if 3 ≤ count then onlineTrueW1Radius (H : ℝ) δ' count
          ((E h).transition (state n) (action n)) (onlineTrueSuffixRowFamily E row)
        else H
      else 0

/-- For each episode on an actual path, the observed certificate controls
its fixed-optimal empirical error; no event probability is assumed here. -/
theorem onlineActualEpisodeW1_le_radiusSum
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (initial : Fin K → State) (fallback : State)
    (path : OnlineOutcomePath State (K * H)) (k : Fin K)
    (δ' c₁ c₂ : ℝ)
    (hcert : onlineObservedTrueW1Certificates H K E δ'
      (onlineSequentialPathHistory
        (onlineEpisodicChoose H K hH initial fallback
          (onlineCappedGreedyPlanner E (Real.log (1 / δ')) c₁ c₂))
        (K * H) [] path)) :
    onlineActualEpisodeW1 H K hH E initial fallback path k δ' c₁ c₂ ≤
      onlineActualEpisodeW1RadiusSum H K hH E initial fallback path k δ' c₁ c₂ := by
  classical
  let planner := onlineCappedGreedyPlanner E (Real.log (1 / δ')) c₁ c₂
  let history := onlineSequentialPathHistory
    (onlineEpisodicChoose H K hH initial fallback planner) (K * H) [] path
  let prehist := history.take (k.val * H)
  let stage : Fin H → OnlineObservedPlanningStage State Action :=
    fun h => onlineHistoryPlanningStage E prehist h
  let state : ℕ → State := fun n =>
    onlineEpisodicCurrentState H K initial fallback
      (history.take (k.val * H + n))
  let action : ℕ → Action := fun n =>
    if hn : n < H then
      (history.get ⟨k.val * H + n, by
        have hlen := onlineSequentialPathHistory_length
          (onlineEpisodicChoose H K hH initial fallback planner) (K * H) [] path
        rw [hlen]
        simp only [List.length_nil, zero_add]
        calc
          k.val * H + n < k.val * H + H := Nat.add_lt_add_left hn _
          _ = (k.val + 1) * H := by rw [Nat.succ_mul]
          _ ≤ K * H := Nat.mul_le_mul_right H (Nat.succ_le_of_lt k.isLt)⟩).1.2.2
    else Classical.choice ((E ⟨0, hH⟩).action_nonempty)
  change (∑ n ∈ Finset.range H, onlineEpisodeFixedOptimalW1 H E stage state action n) ≤
    (∑ n ∈ Finset.range H, if hn : n < H then
      let h : Fin H := ⟨n, hn⟩
      let row := (h, (state n, action n))
      let count := (onlineRowOutcomes prehist row).length
      if 3 ≤ count then onlineTrueW1Radius (H : ℝ) δ' count
        ((E h).transition (state n) (action n)) (onlineTrueSuffixRowFamily E row) else H
      else 0)

  apply Finset.sum_le_sum
  intro n hn
  have hnH : n < H := Finset.mem_range.mp hn
  let h : Fin H := ⟨n, hnH⟩
  have hpoint := onlineObservedW1_pointwise_bound H K E history k h (state n) (action n) δ' hcert
  have hv : onlineFixedOptimalContinuation H E n =
      onlineTrueSuffixRowFamily E (h, (state n, action n)) := by
    funext x
    exact EnvironmentStage.greedy_suffix_value (List.ofFn E) (n + 1) x
  simp only [onlineEpisodeFixedOptimalW1, dif_pos hnH]
  rw [hv]
  simpa [h, stage, prehist, onlineHistoryPlanningStage] using hpoint
end StatisticalRL.OnlineRL
