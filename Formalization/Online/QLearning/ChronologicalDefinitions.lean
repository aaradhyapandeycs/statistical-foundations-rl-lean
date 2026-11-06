import Formalization.Online.SourceOptimism.EpisodicSelectorDefinitions
import Formalization.MDP.EnvironmentDefinitions
import Formalization.Online.QLearning.RateWeightDefinitions
import Mathlib.Data.Finset.Lattice.Fold

namespace StatisticalRL.OnlineRL
variable {State Action : Type*} [Fintype State] [Fintype Action]

structure QLearningChronologicalTable (H : ℕ) where
  q : OnlineMDPRow State Action H → ℝ
  count : OnlineMDPRow State Action H → ℕ

noncomputable def qLearningChronologicalInitial (H : ℕ) :
    QLearningChronologicalTable (State := State) (Action := Action) H where
  q := fun _ => H
  count := fun _ => 0

/-- Capped running value, with the actual source terminal value zero. -/
noncomputable def qLearningChronologicalValue {H : ℕ} (hH : 0 < H)
    (E : Fin H → EnvironmentStage State Action)
    (table : QLearningChronologicalTable (State := State) (Action := Action) H)
    (h : ℕ) (s : State) : ℝ :=
  if hh : h < H then
    letI : Nonempty Action := (E ⟨h, hh⟩).action_nonempty
    min (H : ℝ) (actionMaximum (fun a => table.q (⟨h, hh⟩, (s, a))))
  else 0

/-- Fixed deterministic greedy tie selector; it is chosen at episode start. -/
noncomputable def qLearningChronologicalPolicy {H : ℕ}
    (E : Fin H → EnvironmentStage State Action)
    (table : QLearningChronologicalTable (State := State) (Action := Action) H)
    (h : Fin H) (s : State) : Action := by
  letI : Nonempty Action := (E h).action_nonempty
  exact Classical.choose (by
    obtain ⟨a, _, ha⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
      (fun a => table.q (h, (s, a)))
    exact ⟨a, ha.symm⟩)

/-- One actual visited-row update uses the current table's next-stage value. -/
noncomputable def qLearningChronologicalUpdate {H : ℕ} (hH : 0 < H)
    (E : Fin H → EnvironmentStage State Action) (bonus : ℕ → ℝ)
    (table : QLearningChronologicalTable (State := State) (Action := Action) H)
    (obs : OnlineMDPRow State Action H × State) :
    QLearningChronologicalTable (State := State) (Action := Action) H := by
  classical
  let row := obs.1
  let n := table.count row + 1
  exact {
    count := fun r => if r = row then n else table.count r
    q := fun r => if r = row then
      (1 - onlineQRate H n) * table.q row + onlineQRate H n *
        ((E row.1).reward row.2.1 row.2.2 +
          qLearningChronologicalValue hH E table (row.1.val + 1) obs.2 + bonus n)
      else table.q r }

/-- Chronological fold of the actually observed row/successor records. -/
noncomputable def qLearningChronologicalFold {H : ℕ} (hH : 0 < H)
    (E : Fin H → EnvironmentStage State Action) (bonus : ℕ → ℝ)
    (table : QLearningChronologicalTable (State := State) (Action := Action) H)
    (history : List (OnlineMDPRow State Action H × State)) :=
  history.foldl (qLearningChronologicalUpdate hH E bonus) table


end StatisticalRL.OnlineRL
