import Formalization.Online.Regret.MVP.T6.MVPActualT8ConditionalVariance
import Formalization.Online.Regret.MVP.T6.MVPActualVarianceDefinitions
import Formalization.Online.Regret.W1.OnlineW1ActualRowAlignment

/-! Actual-law transport from the padded T₃ predictable variance to the source T6-UCB sum. -/

namespace StatisticalRL.OnlineRL
open scoped BigOperators
open MeasureTheory
universe uState uAction
variable {State : Type uState} {Action : Type uAction}
  [Fintype State] [Fintype Action]
noncomputable local instance t6MVPActualTailVariance_mvpTransportMeasurable : MeasurableSpace State := ⊤
noncomputable local instance t6MVPActualTailVariance_mvpTransportSampleMeasurable (H K : ℕ) :
    MeasurableSpace ((Fin K → State) × OnlineOutcomePath State (K * H)) :=
  StatisticalRL.FiniteDistribution.empiricalRowStateMeasurable
noncomputable local instance t6MVPActualTailVariance_mvpTransportDecState : DecidableEq State := Classical.decEq State
noncomputable local instance t6MVPActualTailVariance_mvpTransportDecAction : DecidableEq Action := Classical.decEq Action

/-- At the flattening of episode `k`, stage `h`, the padded row variance is
exactly the corresponding actual T6-UCB summand. -/
theorem mvpTailVariance_eq_actualT6Term
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (initial : Fin K → State) (fallback : State)
    (path : OnlineOutcomePath State (K * H)) (k : Fin K) (h : Fin H)
    (δ c₁ c₂ : ℝ) :
    let planner := onlineMVPCommittedGreedyPlanner hH E fallback (Real.log (1 / δ)) c₁ c₂
    mvpT8PaddedTailVariance H K hH E fallback planner (Real.log (1 / δ)) c₁ c₂
      (k.val * H + h.val) (initial, path) =
      let planner := onlineMVPCommittedGreedyPlanner hH E fallback (Real.log (1 / δ)) c₁ c₂
      let sa := onlineActualStageRowSequence H K hH initial fallback planner path h k.val
      ((E h).transition sa.1 sa.2).variance
        (mvpVarianceContinuation H K hH E initial fallback path δ c₁ c₂ h k) := by
  classical
  dsimp
  let planner := onlineMVPCommittedGreedyPlanner hH E fallback (Real.log (1 / δ)) c₁ c₂
  let history := onlineSequentialPathHistory
    (onlineEpisodicChoose H K hH initial fallback planner) (K * H) [] path
  let n := k.val * H + h.val
  have hn : n < K * H := by
    calc
      n < k.val * H + H := Nat.add_lt_add_left h.isLt _
      _ = (k.val + 1) * H := by rw [Nat.succ_mul]
      _ ≤ K * H := Nat.mul_le_mul_right H (Nat.succ_le_of_lt k.isLt)
  have hnH : n / H = k.val := by
    have hn' : n = h.val + H * k.val := by dsimp [n]; rw [Nat.mul_comm k.val H]; omega
    rw [hn']
    rw [Nat.add_mul_div_left]
    · simp [Nat.div_eq_of_lt h.isLt]
    · exact hH
  have hnmod : n % H = h.val := by
    have hn' : n = h.val + H * k.val := by dsimp [n]; rw [Nat.mul_comm k.val H]; omega
    rw [hn', Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h.isLt]
  have hlen : history.length = K * H := by
    simpa [history, planner] using onlineSequentialPathHistory_length
      (onlineEpisodicChoose H K hH initial fallback planner) (K * H) [] path
  have hkcut : k.val * H ≤ n := by dsimp [n]; omega
  have hchoose : onlineEpisodicChoose H K hH initial fallback planner
      (history.take n) =
      (h, (onlineEpisodicCurrentState H K initial fallback (history.take n),
        planner (history.take (k.val * H)) h
          (onlineEpisodicCurrentState H K initial fallback (history.take n)))) := by
    simp [onlineEpisodicChoose, hlen, hn.le, hnH, hnmod,
      List.take_take, Nat.min_eq_left hkcut]
  have hrow := onlineSequentialEpisode_actual_row H K hH E initial fallback planner path k h
  have hrow' : (history.get ⟨n, by rw [hlen]; exact hn⟩).1 =
      (h, (onlineEpisodicCurrentState H K initial fallback (history.take n),
        planner (history.take (k.val * H)) h
          (onlineEpisodicCurrentState H K initial fallback (history.take n)))) := by
    simpa [history, n] using hrow
  have hrowAt := onlineTranscriptRowSequence_agrees
    (onlineEpisodicChoose H K hH initial fallback planner []) history
    ⟨n, by rw [hlen]; exact hn⟩
  have hsa : onlineActualStageRowSequence H K hH initial fallback planner path h k.val =
      (onlineEpisodicCurrentState H K initial fallback (history.take n),
        planner (history.take (k.val * H)) h
          (onlineEpisodicCurrentState H K initial fallback (history.take n))) := by
    change (onlineTranscriptRowSequence
      (onlineEpisodicChoose H K hH initial fallback planner []) history n).2 = _
    rw [hrowAt, hrow']
  have htail : mvpT8CompletedPrefixTail H hH E fallback
      (Real.log (1 / δ)) c₁ c₂ n (history.take n) =
      mvpVarianceContinuation H K hH E initial fallback path δ c₁ c₂ h k := by
    simp [mvpT8CompletedPrefixTail, mvpVarianceContinuation, mvpVarianceHistory,
      hnH, hnmod, history, planner, List.take_take, Nat.min_eq_left hkcut]
  have hnH' : (k.val * H + h.val) / H = k.val := by simpa [n] using hnH
  have hnmod' : (k.val * H + h.val) % H = h.val := by simpa [n] using hnmod
  rw [mvpT8PaddedTailVariance, if_pos hn]
  simp only [hnH', hnmod']
  have hobs : onlineT3CommonPrefixObservation H K (K * H) hH fallback planner n (initial, path) =
      (initial, history.take n) := by
    simp [onlineT3CommonPrefixObservation, onlineT3CommonFullHistory, history]
  rw [hobs]
  rw [hchoose, htail, hsa]
  simp [onlineMDPSuccessorRowLaw]

/-- Reindex the finite sequence of valid chronological T₃ row variances into
the source's stage-major T6-UCB sum. -/
theorem mvpTailVarianceSum_eq_actualT6UCB
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (initial : Fin K → State) (fallback : State)
    (path : OnlineOutcomePath State (K * H)) (δ c₁ c₂ : ℝ) :
    ∑ n ∈ Finset.range (K * H),
        mvpT8PaddedTailVariance H K hH E fallback
          (onlineMVPCommittedGreedyPlanner hH E fallback (Real.log (1 / δ)) c₁ c₂)
          (Real.log (1 / δ)) c₁ c₂ n (initial, path) =
      mvpVarianceT6UCB H K hH E initial fallback path δ c₁ c₂ := by
  classical
  unfold mvpVarianceT6UCB
  let f : Fin H → Fin K → ℝ := fun h k =>
    let planner := onlineMVPCommittedGreedyPlanner hH E fallback (Real.log (1 / δ)) c₁ c₂
    let sa := onlineActualStageRowSequence H K hH initial fallback planner path h k.val
    ((E h).transition sa.1 sa.2).variance
      (mvpVarianceContinuation H K hH E initial fallback path δ c₁ c₂ h k)
  change (∑ n ∈ Finset.range (K * H),
    mvpT8PaddedTailVariance H K hH E fallback
      (onlineMVPCommittedGreedyPlanner hH E fallback (Real.log (1 / δ)) c₁ c₂)
      (Real.log (1 / δ)) c₁ c₂ n (initial, path)) =
    ∑ h : Fin H, ∑ k : Fin K, f h k
  rw [← Fintype.sum_prod_type']
  apply Finset.sum_bij
    (fun n hn =>
      ((⟨n % H, Nat.mod_lt n hH⟩ : Fin H),
       (⟨n / H, (onlineT3NaturalTime_decomposition H hH K n
         (Finset.mem_range.mp hn)).1⟩ : Fin K)))
  · intro n hn
    exact Finset.mem_univ _
  · intro n hn m hm he
    have hdecN := onlineT3NaturalTime_decomposition H hH K n (Finset.mem_range.mp hn)
    have hdecM := onlineT3NaturalTime_decomposition H hH K m (Finset.mem_range.mp hm)
    have hmod : n % H = m % H := congrArg Fin.val (congrArg Prod.fst he)
    have hdiv : n / H = m / H := congrArg Fin.val (congrArg Prod.snd he)
    calc
      n = n / H * H + n % H := hdecN.2.2
      _ = m / H * H + m % H := by rw [hdiv, hmod]
      _ = m := hdecM.2.2.symm
  · intro ⟨h, k⟩ hp
    refine ⟨k.val * H + h.val, Finset.mem_range.mpr ?_, ?_⟩
    · calc
        k.val * H + h.val < (k.val + 1) * H := by
          rw [Nat.succ_mul]
          exact Nat.add_lt_add_left h.isLt _
        _ ≤ K * H := Nat.mul_le_mul_right H (Nat.succ_le_of_lt k.isLt)
    · apply Prod.ext
      · apply Fin.ext
        have hhmod : (k.val * H + h.val) % H = h.val := by
          rw [Nat.mul_comm k.val H, Nat.add_comm (H * k.val) h.val,
            Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h.isLt]
        exact hhmod
      · apply Fin.ext
        have hhdiv : (k.val * H + h.val) / H = k.val := by
          rw [Nat.mul_comm k.val H, Nat.add_comm (H * k.val) h.val,
            Nat.add_mul_div_left]
          · simp [Nat.div_eq_of_lt h.isLt]
          · exact hH
        exact hhdiv
  · intro n hn
    have hdec := onlineT3NaturalTime_decomposition H hH K n (Finset.mem_range.mp hn)
    let k' : Fin K := ⟨n / H, hdec.1⟩
    let h' : Fin H := ⟨n % H, hdec.2.1⟩
    have hrow := mvpTailVariance_eq_actualT6Term H K hH E initial fallback path
      k' h' δ c₁ c₂
    calc
      mvpT8PaddedTailVariance H K hH E fallback
          (onlineMVPCommittedGreedyPlanner hH E fallback (Real.log (1 / δ)) c₁ c₂)
          (Real.log (1 / δ)) c₁ c₂ n (initial, path) =
        mvpT8PaddedTailVariance H K hH E fallback
          (onlineMVPCommittedGreedyPlanner hH E fallback (Real.log (1 / δ)) c₁ c₂)
          (Real.log (1 / δ)) c₁ c₂ (k'.val * H + h'.val) (initial, path) := by
            congr 1
            exact hdec.2.2
      _ = f h' k' := by simpa [f] using hrow

end StatisticalRL.OnlineRL
