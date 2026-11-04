import Formalization.Online.Regret.T3.OnlineRegretT3PaddedProcess

/-! common T3/T4 terminal-state bridge. A terminal continuation
must vanish, so the next episode's reset and the recorded terminal successor
give the same value. At other stages the actual current state is the fresh
recorded successor. This helper does not establish a probability bound. -/
namespace StatisticalRL.OnlineRL
universe uState uAction
variable {State : Type uState} {Action : Type uAction} [Fintype State] [Fintype Action]

omit [Fintype State] [Fintype Action] in
theorem onlineEpisodicCurrentState_append_value
    (H K : ℕ) (initial : Fin K → State) (fallback : State)
    (history : List (OnlineMDPRow State Action H × State))
    (row : OnlineMDPRow State Action H) (x : State) (V : State → ℝ)
    (hterminal : (history.length + 1) % H = 0 → ∀ s, V s = 0) :
    V (onlineEpisodicCurrentState H K initial fallback (history ++ [(row, x)])) = V x := by
  by_cases hm : (history.length + 1) % H = 0
  · rw [hterminal hm, hterminal hm]
  · have hstate : onlineEpisodicCurrentState H K initial fallback
        (history ++ [(row, x)]) = x := by
      simp [onlineEpisodicCurrentState, List.length_append, hm]
    rw [hstate]

/-- Value of the actual state after one transition equals value of that
transition's fresh successor, including the terminal/reset boundary. -/
theorem onlineSequentialEpisode_nextState_value_eq_fresh
    (H K T : ℕ) (hH : 0 < H) (fallback : State)
    (planner : OnlineEpisodePlanner State Action H) (m n : ℕ)
    (hT : T = (m + 1) + n)
    (sample : (Fin K → State) × OnlineOutcomePath.{uState, 0} State T)
    (V : State → ℝ) (hterminal : (n + 1) % H = 0 → ∀ s, V s = 0) :
    V (onlineEpisodicCurrentState H K sample.1 fallback
      (onlineT3CommonPrefixObservation H K T hH fallback planner (n + 1) sample).2) =
      V (onlineSequentialPathSuffix n (m + 1) (hT ▸ sample).2).2.1 := by
  have hobs := onlineT3CommonPrefixObservation_succ_eq
    H K T hH fallback planner m n hT sample
  have hlen : (onlineT3CommonPrefixObservation H K T hH fallback planner n sample).2.length = n := by
    have hfull := onlineSequentialPathHistory_length
      (onlineEpisodicChoose H K hH sample.1 fallback planner) T [] sample.2
    have hn : n ≤ T := by omega
    simpa [onlineT3CommonPrefixObservation, onlineT3CommonFullHistory, hfull,
      Nat.min_eq_left hn] using
        (List.length_take (l := onlineT3CommonFullHistory H K T hH fallback planner sample)
          (i := n))
  rw [hobs]
  exact onlineEpisodicCurrentState_append_value H K sample.1 fallback
    (onlineT3CommonPrefixObservation H K T hH fallback planner n sample).2
    (onlineEpisodicChoose H K hH sample.1 fallback planner
      (onlineT3CommonPrefixObservation H K T hH fallback planner n sample).2)
    (onlineSequentialPathSuffix n (m + 1) (hT ▸ sample).2).2.1 V
    (by simpa only [hlen] using hterminal)

end StatisticalRL.OnlineRL
