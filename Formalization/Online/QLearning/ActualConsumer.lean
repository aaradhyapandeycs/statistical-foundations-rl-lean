import Formalization.Online.QLearning.VisitFold
import Formalization.Online.QLearning.ScalarRecurrence
import Mathlib.Data.List.GetD

/-! actual-table recurrence. Logged targets are read from
actual pre-update tables; no external recurrence hypothesis is assumed. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators
variable {State Action : Type*} [Fintype State] [Fintype Action]
attribute [local instance] Classical.propDecidable

/-- A log-accumulating fold initialized with an arbitrary previous log. -/
noncomputable def qLearningLogFrom {H : ℕ} (hH : 0 < H)
    (E : Fin H → EnvironmentStage State Action) (bonus : ℕ → ℝ)
    (r : OnlineMDPRow State Action H)
    (acc : QLearningChronologicalTable (State := State) (Action := Action) H × List ℝ)
    (history : List (OnlineMDPRow State Action H × State)) := by
  classical
  exact history.foldl (fun a obs =>
    (qLearningChronologicalUpdate hH E bonus a.1 obs,
      if obs.1 = r then a.2 ++ [qLearningVisitTarget hH E bonus a.1 obs] else a.2)) acc

lemma qLearningLogFrom_q {H : ℕ} (hH : 0 < H)
    (E : Fin H → EnvironmentStage State Action) (bonus : ℕ → ℝ)
    (r : OnlineMDPRow State Action H) (acc : QLearningChronologicalTable (State := State) (Action := Action) H × List ℝ)
    (hist : List (OnlineMDPRow State Action H × State)) :
    (qLearningLogFrom hH E bonus r acc hist).1 =
      qLearningChronologicalFold hH E bonus acc.1 hist := by
  classical
  induction hist generalizing acc with
  | nil => rfl
  | cons x xs ih =>
      simpa [qLearningLogFrom, qLearningChronologicalFold] using
        (ih (qLearningChronologicalUpdate hH E bonus acc.1 x,
          if x.1 = r then acc.2 ++ [qLearningVisitTarget hH E bonus acc.1 x] else acc.2))

lemma qLearningLogged_eq_from {H : ℕ} (hH : 0 < H)
    (E : Fin H → EnvironmentStage State Action) (bonus : ℕ → ℝ)
    (r : OnlineMDPRow State Action H) (table : QLearningChronologicalTable (State := State) (Action := Action) H)
    (hist : List (OnlineMDPRow State Action H × State)) :
    qLearningLoggedVisitFold hH E bonus r table hist = qLearningLogFrom hH E bonus r (table,[]) hist := by
  classical
  simp [qLearningLoggedVisitFold, qLearningLogFrom]

lemma qLearningLogFrom_snoc {H : ℕ} (hH : 0 < H)
    (E : Fin H → EnvironmentStage State Action) (bonus : ℕ → ℝ)
    (r : OnlineMDPRow State Action H) (table : QLearningChronologicalTable (State := State) (Action := Action) H)
    (hist : List (OnlineMDPRow State Action H × State)) (obs : OnlineMDPRow State Action H × State) :
    qLearningLoggedVisitFold hH E bonus r table (hist ++ [obs]) =
      (qLearningChronologicalUpdate hH E bonus (qLearningChronologicalFold hH E bonus table hist) obs,
        if obs.1 = r then (qLearningLoggedVisitFold hH E bonus r table hist).2 ++
          [qLearningVisitTarget hH E bonus (qLearningChronologicalFold hH E bonus table hist) obs]
        else (qLearningLoggedVisitFold hH E bonus r table hist).2) := by
  classical
  simp only [qLearningLogged_eq_from, qLearningLogFrom, List.foldl_append, List.foldl_cons, List.foldl_nil]
  rw [show (List.foldl _ (table, []) hist).1 = qLearningChronologicalFold hH E bonus table hist from
    qLearningLogFrom_q hH E bonus r (table,[]) hist]

/-- The target log contains exactly one entry for each actual row visit. -/
theorem qLearningLogged_length {H : ℕ} (hH : 0 < H)
    (E : Fin H → EnvironmentStage State Action) (bonus : ℕ → ℝ)
    (r : OnlineMDPRow State Action H) (table : QLearningChronologicalTable (State := State) (Action := Action) H)
    (hist : List (OnlineMDPRow State Action H × State)) :
    (qLearningLoggedVisitFold hH E bonus r table hist).2.length = (qLearningRowVisits r hist).length := by
  classical
  induction hist using List.reverseRecOn with
  | nil => simp [qLearningLoggedVisitFold, qLearningRowVisits]
  | @append_singleton hist obs ih =>
      rw [qLearningLogFrom_snoc]
      by_cases h : obs.1 = r
      · simp [h, qLearningRowVisits, ih]
      · simp [h, qLearningRowVisits, ih]

/-- Actual table Q is exactly the source weighted expression for the targets
recorded at real pre-update tables. -/
theorem qLearningActualFold_weighted {H : ℕ} (hH : 0 < H)
    (E : Fin H → EnvironmentStage State Action) (bonus : ℕ → ℝ)
    (r : OnlineMDPRow State Action H) (table : QLearningChronologicalTable (State := State) (Action := Action) H)
    (hzero : table.count r = 0) (hist : List (OnlineMDPRow State Action H × State)) :
    let log := (qLearningLoggedVisitFold hH E bonus r table hist).2
    (qLearningChronologicalFold hH E bonus table hist).q r =
      onlineQRateWeight H log.length 0 * table.q r +
        ∑ i ∈ Finset.Icc 1 log.length, onlineQRateWeight H log.length i * log.getD (i-1) 0 := by
  classical
  induction hist using List.reverseRecOn with
  | nil => simp [qLearningLoggedVisitFold, qLearningChronologicalFold, onlineQRateWeight]
  | @append_singleton hist obs ih =>
      let log := (qLearningLoggedVisitFold hH E bonus r table hist).2
      let current := qLearningChronologicalFold hH E bonus table hist
      have hcount : current.count r = log.length := by
        rw [qLearningChronologicalFold_count, hzero, zero_add]
        exact (qLearningLogged_length hH E bonus r table hist).symm
      have hfold : qLearningChronologicalFold hH E bonus table (hist ++ [obs]) =
          qLearningChronologicalUpdate hH E bonus current obs := by
        simp [qLearningChronologicalFold, List.foldl_append, current]
      rw [hfold, qLearningLogFrom_snoc]
      by_cases heq : obs.1 = r
      · have hsum :
            (∑ i ∈ Finset.Icc 1 log.length, onlineQRateWeight H log.length i *
              (log ++ [qLearningVisitTarget hH E bonus current obs]).getD (i-1) 0) =
            ∑ i ∈ Finset.Icc 1 log.length, onlineQRateWeight H log.length i * log.getD (i-1) 0 := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [List.getD_append _ _ _ _ (by have := Finset.mem_Icc.mp hi; omega)]
        have hrow : r = obs.1 := heq.symm
        simp only [heq, if_pos, List.length_append, List.length_singleton]
        rw [qLearningInitialWeight_succ, onlineQRateWeight_sum_succ, hsum]
        have hend : (log ++ [qLearningVisitTarget hH E bonus current obs]).getD (log.length + 1 - 1) 0 =
            qLearningVisitTarget hH E bonus current obs := by
          simp [List.getD_append_right]
        rw [hend]
        have hi := ih
        change current.q r = onlineQRateWeight H log.length 0 * table.q r +
          ∑ i ∈ Finset.Icc 1 log.length, onlineQRateWeight H log.length i * log.getD (i-1) 0 at hi
        subst r
        simp only [qLearningChronologicalUpdate, ↓reduceIte]
        change (1 - onlineQRate H (current.count obs.1 + 1)) * current.q obs.1 +
          onlineQRate H (current.count obs.1 + 1) * qLearningVisitTarget hH E bonus current obs = _
        rw [hcount, hi]
        ring
      · have hr : r ≠ obs.1 := Ne.symm heq
        simpa [heq, hr, qLearningChronologicalUpdate, current, log] using ih

end StatisticalRL.OnlineRL
