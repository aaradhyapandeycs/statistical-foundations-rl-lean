import Formalization.MDP.InfiniteTrajectory
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

/-!
# Controlled infinite trajectory: finite-cylinder recurrence

The singleton-prefix recurrence is derived from the actual infinite trajectory
law and its history kernels. A bridge to the separately constructed finite
trajectory law remains to be proved.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace StatisticalRL.DiscountedMDP

variable {State Action : Type*} [Fintype State] [Fintype Action]
local instance infinitePrefixStateMeasurable : MeasurableSpace State := ⊤
local instance infinitePrefixActionMeasurable : MeasurableSpace Action := ⊤

/-- Appending an observed action/next-state pair to any finite history has
mass equal to the history mass times the actual policy-transition mass. -/
theorem infiniteTrajectoryLaw_history_singleton_step
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action) (s : State)
    (n : ℕ) (history : ↥(Finset.Iic n) → Action × State) (a : Action) (t : State) :
    (M.infiniteTrajectoryLaw π s).map
      (fun path ↦ (Preorder.frestrictLe n path, path (n + 1))) {(history, (a, t))} =
      (M.infiniteTrajectoryLaw π s).map (Preorder.frestrictLe n) {history} *
        ENNReal.ofReal ((π (history ⟨n, Finset.mem_Iic.mpr le_rfl⟩).2).prob a *
          (M.transition (history ⟨n, Finset.mem_Iic.mpr le_rfl⟩).2 a).prob t) := by
  rw [← M.infiniteTrajectoryLaw_history_step π s n]
  have hset : ({(history, (a, t))} : Set ((↥(Finset.Iic n) → Action × State) × (Action × State))) =
      ({history} : Set (↥(Finset.Iic n) → Action × State)) ×ˢ ({(a, t)} : Set (Action × State)) := by
    ext x
    simp
  rw [hset, Measure.compProd_apply_prod (measurableSet_singleton _) (measurableSet_singleton _)]
  rw [lintegral_singleton]
  rw [M.historyKernel_apply, M.stepMeasure_singleton]
  exact mul_comm _ _

/-- Drop only the last recorded pair of a nonempty finite history. -/
def historyCut (n : ℕ) (history : ↥(Finset.Iic (n + 1)) → Action × State) :
    ↥(Finset.Iic n) → Action × State :=
  fun i ↦ history ⟨i.1, Finset.mem_Iic.mpr (Nat.le_trans (Finset.mem_Iic.mp i.2) (Nat.le_succ n))⟩

/-- The cylinder of a history through `n+1` is exactly the cylinder of its
prefix through `n` together with its last sampled pair. -/
theorem historyCylinder_succ (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (s : State) (n : ℕ)
    (history : ↥(Finset.Iic (n + 1)) → Action × State) :
    (M.infiniteTrajectoryLaw π s).map (Preorder.frestrictLe (n + 1)) {history} =
      (M.infiniteTrajectoryLaw π s).map
        (fun path ↦ (Preorder.frestrictLe n path, path (n + 1)))
          {(historyCut n history, history ⟨n + 1, Finset.mem_Iic.mpr le_rfl⟩)} := by
  rw [Measure.map_apply (by fun_prop) (measurableSet_singleton _),
      Measure.map_apply (by fun_prop) (measurableSet_singleton _)]
  congr 1
  ext path
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Prod.mk.injEq]
  constructor
  · intro h
    constructor
    · funext i
      exact congrFun h ⟨i.1, Finset.mem_Iic.mpr
        (Nat.le_trans (Finset.mem_Iic.mp i.2) (Nat.le_succ n))⟩
    · exact congrFun h ⟨n + 1, Finset.mem_Iic.mpr le_rfl⟩
  · rintro ⟨hcut, hlast⟩
    funext i
    by_cases hi : i.1 ≤ n
    · exact congrFun hcut ⟨i.1, Finset.mem_Iic.mpr hi⟩
    · have heq : i.1 = n + 1 := by
        have hib := Finset.mem_Iic.mp i.2
        omega
      have hi_eq : i = ⟨n + 1, Finset.mem_Iic.mpr le_rfl⟩ := Subtype.ext heq
      rw [hi_eq]
      exact hlast

/-- Consecutive singleton prefix masses are related by the exact controlled kernel. -/
theorem infiniteTrajectoryLaw_prefix_singleton_succ (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (s : State) (n : ℕ)
    (history : ↥(Finset.Iic (n + 1)) → Action × State) :
    (M.infiniteTrajectoryLaw π s).map (Preorder.frestrictLe (n + 1)) {history} =
      (M.infiniteTrajectoryLaw π s).map (Preorder.frestrictLe n) {historyCut n history} *
      ENNReal.ofReal
        ((π (history ⟨n, Finset.mem_Iic.mpr (Nat.le_succ n)⟩).2).prob
          (history ⟨n + 1, Finset.mem_Iic.mpr le_rfl⟩).1 *
        (M.transition (history ⟨n, Finset.mem_Iic.mpr (Nat.le_succ n)⟩).2
          (history ⟨n + 1, Finset.mem_Iic.mpr le_rfl⟩).1).prob
          (history ⟨n + 1, Finset.mem_Iic.mpr le_rfl⟩).2) := by
  rw [historyCylinder_succ]
  exact M.infiniteTrajectoryLaw_history_singleton_step π s n (historyCut n history) _ _

/-- The single first-pair cylinder has its actual step distribution. -/
theorem infiniteTrajectoryLaw_prefix_singleton_zero (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (s : State)
    (history : ↥(Finset.Iic 0) → Action × State) :
    (M.infiniteTrajectoryLaw π s).map (Preorder.frestrictLe 0) {history} =
      ENNReal.ofReal ((π s).prob (history ⟨0, Finset.mem_Iic.mpr le_rfl⟩).1 *
        (M.transition s (history ⟨0, Finset.mem_Iic.mpr le_rfl⟩).1).prob
          (history ⟨0, Finset.mem_Iic.mpr le_rfl⟩).2) := by
  have hevent : (M.infiniteTrajectoryLaw π s).map (Preorder.frestrictLe 0) {history} =
      (M.infiniteTrajectoryLaw π s).map (fun path ↦ path 0)
        {history ⟨0, Finset.mem_Iic.mpr le_rfl⟩} := by
    rw [Measure.map_apply (by fun_prop) (measurableSet_singleton _),
      Measure.map_apply (by fun_prop) (measurableSet_singleton _)]
    congr 1
    ext path
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro h
      exact congrFun h ⟨0, Finset.mem_Iic.mpr le_rfl⟩
    · intro h
      funext i
      have hi : i = ⟨0, Finset.mem_Iic.mpr le_rfl⟩ := by
        apply Subtype.ext
        exact Nat.eq_zero_of_le_zero (Finset.mem_Iic.mp i.2)
      rw [hi]
      exact h
  rw [hevent, M.infiniteTrajectoryLaw_first π s, M.stepMeasure_singleton]

/-- Product of the actual policy and transition masses for all pairs through n. -/
noncomputable def historyMass (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (s : State) :
    (n : ℕ) → (↥(Finset.Iic n) → Action × State) → ℝ≥0∞
  | 0, history =>
    ENNReal.ofReal ((π s).prob (history ⟨0, Finset.mem_Iic.mpr le_rfl⟩).1 *
      (M.transition s (history ⟨0, Finset.mem_Iic.mpr le_rfl⟩).1).prob
        (history ⟨0, Finset.mem_Iic.mpr le_rfl⟩).2)
  | n + 1, history =>
    historyMass M π s n (historyCut n history) *
      ENNReal.ofReal
        ((π (history ⟨n, Finset.mem_Iic.mpr (Nat.le_succ n)⟩).2).prob
          (history ⟨n + 1, Finset.mem_Iic.mpr le_rfl⟩).1 *
        (M.transition (history ⟨n, Finset.mem_Iic.mpr (Nat.le_succ n)⟩).2
          (history ⟨n + 1, Finset.mem_Iic.mpr le_rfl⟩).1).prob
          (history ⟨n + 1, Finset.mem_Iic.mpr le_rfl⟩).2)

/-- Every singleton finite cylinder has the full product of its actual
policy and transition probabilities, at arbitrary length. -/
theorem infiniteTrajectoryLaw_prefix_singleton_eq_historyMass
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action) (s : State)
    (n : ℕ) (history : ↥(Finset.Iic n) → Action × State) :
    (M.infiniteTrajectoryLaw π s).map (Preorder.frestrictLe n) {history} =
      historyMass M π s n history := by
  induction n with
  | zero => exact M.infiniteTrajectoryLaw_prefix_singleton_zero π s history
  | succ n ih =>
    rw [M.infiniteTrajectoryLaw_prefix_singleton_succ π s n history]
    rw [ih (historyCut n history)]
    rfl

end StatisticalRL.DiscountedMDP
