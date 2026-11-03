import Formalization.MDP.InfiniteTrajectory
import Formalization.MDP.FiniteOptimal

/-! A forced first action on the actual infinite controlled trajectory law. -/

open MeasureTheory ProbabilityTheory

namespace StatisticalRL.DiscountedMDP

variable {State Action : Type*} [Fintype State] [Fintype Action]

local instance forcedTrajectoryStateMeasurable : MeasurableSpace State := ⊤
local instance forcedTrajectoryActionMeasurable : MeasurableSpace Action := ⊤
noncomputable local instance forcedTrajectoryActionDecidable : DecidableEq Action := Classical.decEq Action

/-- Only the initial action is forced; later history steps use the original π. -/
noncomputable def forcedActionTrajectoryLaw (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (s : State) (a : Action) :
    Measure (ℕ → Action × State) :=
  Kernel.trajMeasure (M.stepMeasure (fun _ ↦ EnvironmentStage.pointMass a) s)
    (M.historyKernel π)

instance forcedActionTrajectoryLaw_isProbabilityMeasure (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (s : State) (a : Action) :
    IsProbabilityMeasure (M.forcedActionTrajectoryLaw π s a) := by
  unfold forcedActionTrajectoryLaw
  infer_instance

/-- The initial pair has the forced action and its genuine next-state kernel. -/
theorem forcedActionTrajectoryLaw_first (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (s : State) (a : Action) :
    (M.forcedActionTrajectoryLaw π s a).map (fun path ↦ path 0) =
      M.stepMeasure (fun _ ↦ EnvironmentStage.pointMass a) s := by
  have hf : (fun path : ℕ → Action × State ↦ path 0) =
      (fun x : ↥(Finset.Iic 0) → Action × State ↦ x ⟨0, Finset.mem_Iic.mpr le_rfl⟩) ∘
        Preorder.frestrictLe 0 := rfl
  rw [hf, ← Measure.map_map (by fun_prop) (by fun_prop)]
  unfold forcedActionTrajectoryLaw Kernel.trajMeasure
  rw [Measure.map_comp _ _ (by fun_prop), Kernel.traj_map_frestrictLe,
    Kernel.partialTraj_self, Measure.id_comp]
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  simp only [Function.comp_def, MeasurableEquiv.piUnique_symm_apply]
  simp

/-- The first action is exactly the supplied action, including when π assigns
that action zero probability; the next-state mass is its actual transition. -/
theorem forcedActionTrajectoryLaw_first_pair (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (s : State) (a b : Action) (t : State) :
    (M.forcedActionTrajectoryLaw π s a).map (fun path ↦ path 0) {(b, t)} =
      if b = a then ENNReal.ofReal ((M.transition s a).prob t) else 0 := by
  classical
  rw [forcedActionTrajectoryLaw_first, stepMeasure_singleton]
  by_cases h : b = a <;> simp [EnvironmentStage.pointMass, h]

/-- After the forced first action, the original π governs each next step. -/
theorem forcedActionTrajectoryLaw_history_step (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (s : State) (a : Action) (n : ℕ) :
    (M.forcedActionTrajectoryLaw π s a).map (Preorder.frestrictLe n) ⊗ₘ
        M.historyKernel π n =
      (M.forcedActionTrajectoryLaw π s a).map
        (fun path ↦ (Preorder.frestrictLe n path, path (n + 1))) := by
  exact Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure

end StatisticalRL.DiscountedMDP
