import Formalization.Online.Regret.T3.OnlineRegretT3PublicArray
import Formalization.Online.Regret.Definitions

/-! Finite-sum identity for the actual T₃ array and public decomposition coordinate. -/

namespace StatisticalRL.OnlineRL
open scoped BigOperators
universe uState uAction
variable {State : Type uState} {Action : Type uAction}
  [Fintype State] [Fintype Action]
noncomputable local instance t3SumStateMeasurable : MeasurableSpace State := ⊤
noncomputable local instance t3SumStateDecidable : DecidableEq State := Classical.decEq State
noncomputable local instance t3SumActionDecidable : DecidableEq Action := Classical.decEq Action

/-- The padded T₃ process over the actual `K*H` transition records is exactly
the sum of the third coordinates in the source episode decomposition. -/
theorem onlineT3PaddedY_sum_eq_publicT3
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (ρ : FiniteDistribution State) (fallback : State)
    (sample : (Fin K → State) × OnlineOutcomePath State (K * H))
    (δ c₁ c₂ : ℝ) :
    (∑ n ∈ Finset.range (K * H),
      onlineT3PaddedY H K hH E ρ fallback
        (onlineCappedGreedyPlanner E (Real.log (1 / δ)) c₁ c₂)
        (Real.log (1 / δ)) c₁ c₂ n sample) =
      ∑ k : Fin K,
        (onlineActualEpisodeRegretTerms H K hH E sample.1 fallback sample.2 k δ c₁ c₂).2.2.1 := by
  classical
  let planner := onlineCappedGreedyPlanner E (Real.log (1 / δ)) c₁ c₂
  have hperEpisode (k : Fin K) :
      (∑ h : Fin H, onlineT3PaddedY H K hH E ρ fallback planner
        (Real.log (1 / δ)) c₁ c₂ (k.val * H + h.val) sample) =
      (onlineActualEpisodeRegretTerms H K hH E sample.1 fallback sample.2 k δ c₁ c₂).2.2.1 := by
    let history := onlineSequentialPathHistory
      (onlineEpisodicChoose H K hH sample.1 fallback planner) (K * H) [] sample.2
    let prehist := history.take (k.val * H)
    let stage : Fin H → OnlineObservedPlanningStage State Action :=
      fun h => onlineHistoryPlanningStage E prehist h
    let state : ℕ → State := fun n =>
      onlineEpisodicCurrentState H K sample.1 fallback (history.take (k.val * H + n))
    let action : ℕ → Action := fun n =>
      if hn : n < H then
        (history.get ⟨k.val * H + n, by
          have hlen := onlineSequentialPathHistory_length
            (onlineEpisodicChoose H K hH sample.1 fallback planner) (K * H) [] sample.2
          rw [hlen]
          simp only [List.length_nil, zero_add]
          calc
            k.val * H + n < k.val * H + H := Nat.add_lt_add_left hn _
            _ = (k.val + 1) * H := by rw [Nat.succ_mul]
            _ ≤ K * H := Nat.mul_le_mul_right H (Nat.succ_le_of_lt k.isLt)⟩).1.2.2
      else Classical.choice ((E ⟨0, hH⟩).action_nonempty)
    have hpoint (h : Fin H) :
        onlineT3PaddedY H K hH E ρ fallback planner
          (Real.log (1 / δ)) c₁ c₂ (k.val * H + h.val) sample =
        onlineCappedEpisodeT3 H stage state action (Real.log (1 / δ)) c₁ c₂ h.val := by
      simpa [history, prehist, stage, state, action, planner] using
        onlineT3PaddedY_eq_publicEpisodeT3Stage H K hH E ρ fallback
          (onlineCappedGreedyPlanner E (Real.log (1 / δ)) c₁ c₂)
          (Real.log (1 / δ)) c₁ c₂ sample.1 sample.2 k h
    calc
      _ = ∑ h : Fin H,
          onlineCappedEpisodeT3 H stage state action (Real.log (1 / δ)) c₁ c₂ h.val := by
            apply Finset.sum_congr rfl
            intro h hh
            exact hpoint h
      _ = (onlineActualEpisodeRegretTerms H K hH E sample.1 fallback sample.2
            k δ c₁ c₂).2.2.1 := by
          change _ = ∑ n ∈ Finset.range H,
            onlineCappedEpisodeT3 H stage state action (Real.log (1 / δ)) c₁ c₂ n
          apply Finset.sum_bij (fun h _ => h.val)
          · intro h hh
            exact Finset.mem_range.mpr h.isLt
          · intro h hh h' hh' he
            exact Fin.ext he
          · intro n hn
            exact ⟨⟨n, Finset.mem_range.mp hn⟩, Finset.mem_univ _, rfl⟩
          · intro h hh
            rfl
  have hindex :
      (∑ n ∈ Finset.range (K * H),
        onlineT3PaddedY H K hH E ρ fallback planner
          (Real.log (1 / δ)) c₁ c₂ n sample) =
      ∑ k : Fin K, ∑ h : Fin H,
        onlineT3PaddedY H K hH E ρ fallback planner
          (Real.log (1 / δ)) c₁ c₂ (k.val * H + h.val) sample := by
    rw [← Finset.sum_product']
    apply Finset.sum_bij (fun n hn =>
      ((⟨n / H, by
        have hbound : n < K * H := Finset.mem_range.mp hn
        have hdiv : n / H < K := by
          rw [Nat.div_lt_iff_lt_mul hH]
          exact hbound
        exact hdiv⟩ : Fin K), (⟨n % H, Nat.mod_lt _ hH⟩ : Fin H)))
    · intro n hn
      exact Finset.mem_univ _
    · intro n hn m hm he
      have hq : n / H = m / H := congrArg Fin.val (congrArg Prod.fst he)
      have hr : n % H = m % H := congrArg Fin.val (congrArg Prod.snd he)
      have hdecomp : n = n / H * H + n % H := by
        simpa [Nat.mul_comm, Nat.add_comm] using (Nat.mod_add_div n H).symm
      have hdecomp' : m = m / H * H + m % H := by
        simpa [Nat.mul_comm, Nat.add_comm] using (Nat.mod_add_div m H).symm
      rw [hdecomp, hdecomp', hq, hr]
    · intro pair hp
      rcases pair with ⟨k, h⟩
      refine ⟨k.val * H + h.val, Finset.mem_range.mpr ?_, ?_⟩
      · calc
          k.val * H + h.val < k.val * H + H := Nat.add_lt_add_left h.isLt _
          _ = (k.val + 1) * H := by rw [Nat.succ_mul]
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
      exact congrArg (fun t : ℕ =>
        onlineT3PaddedY H K hH E ρ fallback planner (Real.log (1 / δ)) c₁ c₂ t sample) hdecomp
  rw [hindex]
  apply Finset.sum_congr rfl
  intro k hk
  exact hperEpisode k
end StatisticalRL.OnlineRL
