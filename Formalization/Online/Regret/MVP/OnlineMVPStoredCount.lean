import Formalization.Online.Regret.MVP.MVPCountDefinitions
import Formalization.Online.Regret.W1.OnlineW1StageEpisodeCount
import Mathlib.Data.Nat.Log

/-! MVP count and deterministic visit-budget results. -/
namespace StatisticalRL.OnlineRL

/-- The row's actual completed-prefix count, under the same realized history;
no claim is made here that an arbitrary online planner implements MVP. -/
noncomputable def onlineMVPStoredPreEpisodeCount {Row : Type*}
    (rowAt : ℕ → Row) (upto : ℕ) (r : Row) : ℕ :=
  onlineMVPStoredCount (onlineVisitCount rowAt upto r)

/-- Finite diagnostic for the proof's proposed pointwise factor-two claim.
It is not a counterexample to the lemma's final summed inequality. -/
theorem onlineMVP_factor_two_pointwise_fails : 2 * onlineMVPStoredCount 3 < 3 := by
  decide

theorem onlineMVP_first_eight_stored_counts :
    [onlineMVPStoredCount 0, onlineMVPStoredCount 1, onlineMVPStoredCount 2,
      onlineMVPStoredCount 3, onlineMVPStoredCount 4, onlineMVPStoredCount 5,
      onlineMVPStoredCount 6, onlineMVPStoredCount 7] = [0, 1, 1, 1, 2, 2, 2, 2] := by
  decide
/-- Each actually observed row visit advances exactly its row's local MVP
recurrence; non-visits leave that row's state unchanged. -/
theorem onlineMVPStoredPreEpisodeCount_succ {Row : Type*} [DecidableEq Row]
    (rowAt : ℕ → Row) (k : ℕ) (r : Row) :
    onlineMVPStoredPreEpisodeCount rowAt (k + 1) r =
      if rowAt k = r then onlineMVPStoredCount (onlineVisitCount rowAt k r + 1)
      else onlineMVPStoredCount (onlineVisitCount rowAt k r) := by
  by_cases h : rowAt k = r <;>
    simp [onlineMVPStoredPreEpisodeCount, onlineVisitCount_succ, h]

/-- Stage-tagging identifies the same stored batch count when the physical
history is restricted to completed episodes. -/
theorem onlineMVPStoredCount_completedHistory
    {H : ℕ} {Row Outcome : Type*} [DecidableEq Row] (history : List ((Fin H × Row) × Outcome))
    (rowAt : ℕ → Fin H × Row) (h : Fin H) (k : ℕ) (hH : 0 < H)
    (hk : k * H ≤ history.length) (r : Fin H × Row) (hr : r.1 = h)
    (hrows : ∀ j : Fin history.length, rowAt j.val = (history.get j).1)
    (hstage : ∀ j, j < k * H → (rowAt j).1.val = j % H) :
    onlineMVPStoredCount ((onlineRowOutcomes (history.take (k * H)) r).length) =
      onlineMVPStoredPreEpisodeCount (fun e => rowAt (e * H + h.val)) k r := by
  unfold onlineMVPStoredPreEpisodeCount
  rw [onlineObserved_stage_episode_count_eq history rowAt h k hH hk r hr hrows hstage]

end StatisticalRL.OnlineRL
