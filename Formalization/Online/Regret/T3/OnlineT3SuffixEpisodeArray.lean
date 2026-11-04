import Formalization.Online.Regret.T3.OnlineRegretT3PublicArray
import Formalization.Online.Regret.T4.OnlineT4SuffixTelescope
import Formalization.Online.Regret.T3.OnlineT3SuffixMasked

/-! Exact chronological-to-episode/stage identity for the deterministic
masked T₃ process. This is the bridge consumed by the actual suffix-telescope
consumer; it is a samplewise identity under the same planner and path. -/

namespace StatisticalRL.OnlineRL
open scoped BigOperators

universe uState uAction
variable {State : Type uState} {Action : Type uAction}
  [Fintype State] [Fintype Action]
noncomputable local instance t3SuffixArrayStateMeasurable : MeasurableSpace State := ⊤
noncomputable local instance t3SuffixArrayStateDecidable : DecidableEq State := Classical.decEq State
noncomputable local instance t3SuffixArrayActionDecidable : DecidableEq Action := Classical.decEq Action

noncomputable def onlineT3SuffixArrayStage
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (initial : Fin K → State) (fallback : State) (path : OnlineOutcomePath State (K * H))
    (δ c₁ c₂ : ℝ) (k : Fin K) (h : Fin H) : OnlineObservedPlanningStage State Action :=
  let planner := onlineCappedGreedyPlanner E (Real.log (1 / δ)) c₁ c₂
  let history := onlineSequentialPathHistory
    (onlineEpisodicChoose H K hH initial fallback planner) (K * H) [] path
  onlineHistoryPlanningStage E (history.take (k.val * H)) h

noncomputable def onlineT3SuffixArrayState
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (initial : Fin K → State) (fallback : State)
    (path : OnlineOutcomePath State (K * H)) (δ c₁ c₂ : ℝ) (k : Fin K) (n : ℕ) : State :=
  let planner := onlineCappedGreedyPlanner E (Real.log (1 / δ)) c₁ c₂
  let history := onlineSequentialPathHistory
    (onlineEpisodicChoose H K hH initial fallback planner) (K * H) [] path
  onlineEpisodicCurrentState H K initial fallback (history.take (k.val * H + n))

noncomputable def onlineT3SuffixArrayAction
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (initial : Fin K → State) (fallback : State)
    (path : OnlineOutcomePath State (K * H)) (δ c₁ c₂ : ℝ) (k : Fin K) (n : ℕ) : Action :=
  let planner := onlineCappedGreedyPlanner E (Real.log (1 / δ)) c₁ c₂
  let history := onlineSequentialPathHistory
    (onlineEpisodicChoose H K hH initial fallback planner) (K * H) [] path
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

/-- The source episode-major sum of capped T₃ terms from suffix start `j`.
Each episode uses its own pre-episode table and selected policy. -/
noncomputable def onlineT3ActualSuffixEpisodeArray
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (initial : Fin K → State) (fallback : State) (path : OnlineOutcomePath State (K * H))
    (δ c₁ c₂ : ℝ) (j : Fin H) : ℝ :=
  ∑ k : Fin K, ∑ n ∈ Finset.Ico j.val H,
    onlineCappedEpisodeT3 H
      (onlineT3SuffixArrayStage H K hH E initial fallback path δ c₁ c₂ k)
      (onlineT3SuffixArrayState H K hH E initial fallback path δ c₁ c₂ k)
      (onlineT3SuffixArrayAction H K hH E initial fallback path δ c₁ c₂ k)
      (Real.log (1 / δ)) c₁ c₂ n

/-- The chronological masked increment sum is exactly the episode-major
source suffix array. -/
theorem onlineT3SuffixMaskedY_sum_eq_actualEpisodeArray
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (ρ : FiniteDistribution State) (initial : Fin K → State) (fallback : State)
    (path : OnlineOutcomePath State (K * H)) (δ c₁ c₂ : ℝ) (j : Fin H) :
    (∑ n ∈ Finset.range (K * H),
      onlineT3SuffixMaskedY H K hH E ρ fallback
        (onlineCappedGreedyPlanner E (Real.log (1 / δ)) c₁ c₂)
        (Real.log (1 / δ)) c₁ c₂ j n (initial, path)) =
      onlineT3ActualSuffixEpisodeArray H K hH E initial fallback path δ c₁ c₂ j := by
  classical
  let planner := onlineCappedGreedyPlanner E (Real.log (1 / δ)) c₁ c₂
  let masked := fun n => onlineT3SuffixMaskedY H K hH E ρ fallback planner
    (Real.log (1 / δ)) c₁ c₂ j n (initial, path)
  have hpoint (k : Fin K) (h : Fin H) :
      masked (k.val * H + h.val) =
        if j.val ≤ h.val then
          onlineCappedEpisodeT3 H
            (onlineT3SuffixArrayStage H K hH E initial fallback path δ c₁ c₂ k)
            (onlineT3SuffixArrayState H K hH E initial fallback path δ c₁ c₂ k)
            (onlineT3SuffixArrayAction H K hH E initial fallback path δ c₁ c₂ k)
            (Real.log (1 / δ)) c₁ c₂ h.val
        else 0 := by
    have hmod : (k.val * H + h.val) % H = h.val := by
      rw [Nat.mul_comm k.val H, Nat.add_comm (H * k.val) h.val,
        Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h.isLt]
    rw [show masked (k.val * H + h.val) =
      (if j.val ≤ (k.val * H + h.val) % H then
        onlineT3PaddedY H K hH E ρ fallback planner (Real.log (1 / δ)) c₁ c₂
          (k.val * H + h.val) (initial, path) else 0) by rfl, hmod]
    by_cases hj : j.val ≤ h.val
    · simp only [if_pos hj]
      have hpub := onlineT3PaddedY_eq_publicEpisodeT3Stage H K hH E ρ fallback planner
        (Real.log (1 / δ)) c₁ c₂ initial path k h
      exact hpub
    · simp [hj]
  have hindex :
      (∑ n ∈ Finset.range (K * H), masked n) =
        ∑ k : Fin K, ∑ h : Fin H, masked (k.val * H + h.val) := by
    rw [← Finset.sum_product']
    apply Finset.sum_bij (fun n hn =>
      ((⟨n / H, by
        have hbound : n < K * H := Finset.mem_range.mp hn
        rw [Nat.div_lt_iff_lt_mul hH]
        exact hbound⟩ : Fin K), (⟨n % H, Nat.mod_lt n hH⟩ : Fin H)))
    · intro n hn
      exact Finset.mem_univ _
    · intro n hn m hm he
      have hq : n / H = m / H := congrArg Fin.val (congrArg Prod.fst he)
      have hr : n % H = m % H := congrArg Fin.val (congrArg Prod.snd he)
      calc
        n = n / H * H + n % H := by
          simpa [Nat.mul_comm, Nat.add_comm] using (Nat.mod_add_div n H).symm
        _ = m / H * H + m % H := by rw [hq, hr]
        _ = m := by
          simpa [Nat.mul_comm, Nat.add_comm] using (Nat.mod_add_div m H)
    · intro pair hp
      rcases pair with ⟨k, h⟩
      refine ⟨k.val * H + h.val, Finset.mem_range.mpr ?_, ?_⟩
      · calc
          k.val * H + h.val < (k.val + 1) * H := by
            rw [Nat.succ_mul]
            exact Nat.add_lt_add_left h.isLt _
          _ ≤ K * H := Nat.mul_le_mul_right H (Nat.succ_le_of_lt k.isLt)
      · apply Prod.ext
        · apply Fin.ext
          dsimp
          rw [Nat.mul_comm k.val H, Nat.add_comm (H * k.val) h.val,
            Nat.add_mul_div_left]
          · simp [Nat.div_eq_of_lt h.isLt]
          · exact hH
        · apply Fin.ext
          dsimp
          rw [Nat.mul_comm k.val H, Nat.add_comm (H * k.val) h.val,
            Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h.isLt]
    · intro n hn
      have hdecomp : n = n / H * H + n % H := by
        simpa [Nat.mul_comm, Nat.add_comm] using (Nat.mod_add_div n H).symm
      exact congrArg masked hdecomp
  rw [hindex]
  unfold onlineT3ActualSuffixEpisodeArray
  apply Finset.sum_congr rfl
  intro k hk
  simp_rw [hpoint]
  symm
  rw [← Finset.sum_filter, onlineSumFin_suffix_eq_Ico]
  apply Finset.sum_congr rfl
  intro n hn
  simp [((Finset.mem_Ico.mp hn).2)]
end StatisticalRL.OnlineRL
