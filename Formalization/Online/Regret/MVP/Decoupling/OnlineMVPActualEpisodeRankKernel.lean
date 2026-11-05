import Formalization.Online.Regret.MVP.Model.OnlineMVPActualSampler
import Formalization.Online.Regret.MVP.MVPUniformSourceDefinitions
import Formalization.Online.Regret.MVP.MVPProfileDefinitions
import Formalization.Online.Regret.MVP.OnlineMVPDyadicTrigger
import Formalization.Online.Regret.W1.OnlineW1StageEpisodeCount
import Formalization.Online.Regret.MVP.Decoupling.OnlineMVPActualTypedRankKernel

/-! Pre-episode actual rows always have a valid finite visit-rank index. The
strict bound follows from the stage clock and k<K; it is not a source premise. -/
namespace StatisticalRL.OnlineRL

open StatisticalRL.OnlineRL.MVPUniformSource
open StatisticalRL.OnlineRL.MVPProfile

variable {State Action : Type*} [Fintype State] [Fintype Action]

/-- At the start of episode k<K, the actual MVP planning row is the typed
visit-rank kernel, with rank validity derived from the actual stage clock. -/
theorem onlineMVPActualEpisodePlanningRow_eq_typedVisitRankKernel
    {H K : ℕ} (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (initial : Fin K → State) (fallback : State)
    (planner : OnlineEpisodePlanner State Action H)
    (data : OnlineMDPRow State Action H × Fin K → State)
    (k : Fin K) (h : Fin H) (s : State) (a : Action) :
    letI : Nonempty State := (E ⟨0, hH⟩).state_nonempty
    onlineObservedPlanningRow
      (onlineMVPActualPlanningStage E
        (onlineMVPActualStackRowAt hH initial fallback planner data)
        (onlineMVPActualStackNextAt hH initial fallback planner data) (k.val * H) h) s a =
      mvp_visitRankKernel K onlineUniformInitialRow
        (onlineMVPActualFirstVisitRow data (h, (s, a)) (by have hk := k.isLt; omega))
        (fun j => MVPUniformSource.batchRow data j h s a)
        ⟨onlineVisitCount (onlineMVPActualStackRowAt hH initial fallback planner data)
          (k.val * H) (h, (s, a)), by
            classical
            let rowAt := onlineMVPActualStackRowAt hH initial fallback planner data
            let r : Fin H × (State × Action) := (h, (s, a))
            have hrow : onlineVisitCount rowAt (k.val * H) r ≤ k.val := by
              have hstage : ∀ n, n < k.val * H → (rowAt n).1.val = n % H := by
                intro n hn
                exact onlineMVPActualStackRowAt_stage hH initial fallback planner data n
              have hcount := onlineVisitCount_stage_episode_eq rowAt h k.val hH r rfl hstage
              calc
                onlineVisitCount (onlineMVPActualStackRowAt hH initial fallback planner data)
                    (k.val * H) r = onlineVisitCount rowAt (k.val * H) r := rfl
                _ = onlineVisitCount (fun e => rowAt (e * H + h.val)) k.val r := hcount
                _ ≤ k.val := onlineVisitCount_le_prefix _ _ _
            exact lt_of_le_of_lt hrow k.isLt⟩ := by
  letI : Nonempty State := (E ⟨0, hH⟩).state_nonempty
  classical
  let rowAt := onlineMVPActualStackRowAt hH initial fallback planner data
  have hn : k.val * H ≤ K * H := Nat.mul_le_mul_right H k.isLt.le
  have huK : onlineVisitCount rowAt (k.val * H) (h, (s, a)) < K := by
    let r : Fin H × (State × Action) := (h, (s, a))
    have hstage : ∀ n, n < k.val * H → (rowAt n).1.val = n % H := by
      intro n hn
      exact onlineMVPActualStackRowAt_stage hH initial fallback planner data n
    have hcount := onlineVisitCount_stage_episode_eq rowAt h k.val hH r rfl hstage
    calc
      onlineVisitCount rowAt (k.val * H) r =
        onlineVisitCount (fun e => rowAt (e * H + h.val)) k.val r := hcount
      _ ≤ k.val := onlineVisitCount_le_prefix _ _ _
      _ < K := k.isLt
  exact onlineMVPActualPlanningRow_eq_typedVisitRankKernel hH E initial fallback
    planner data (k.val * H) hn h s a huK

end StatisticalRL.OnlineRL
