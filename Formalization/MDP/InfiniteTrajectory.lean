import Formalization.MDP.DiscountedFiniteTrajectory
import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Data.ENNReal.BigOperators

/-!
# Infinite controlled trajectories

The stationary policy and transition kernel determine a probability measure on
infinite action/next-state sequences, starting from a specified initial state.
The measure is constructed by the Ionescu–Tulcea extension theorem.
Source: arXiv:2610.41903v1, Chapter 2, `eq:defn-Vpi-inf`.
-/

open scoped BigOperators ENNReal
open MeasureTheory ProbabilityTheory

namespace StatisticalRL

variable {State Action : Type*} [Fintype State] [Fintype Action]

/-- The joint law of the sampled action and its resulting state. -/
def DecisionStage.stepDistribution (stage : DecisionStage State Action) (s : State) :
    FiniteDistribution (Action × State) where
  prob p := (stage.policy s).prob p.1 * (stage.transition s p.1).prob p.2
  prob_nonneg p := mul_nonneg ((stage.policy s).prob_nonneg _) ((stage.transition s p.1).prob_nonneg _)
  sum_prob := by
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum, FiniteDistribution.sum_prob, mul_one]
    exact (stage.policy s).sum_prob

/-- Conversion from the project's real-valued finite probability law into a
Mathlib probability mass function; no mass or normalization is changed. -/
noncomputable def FiniteDistribution.toPMF {Ω : Type*} [Fintype Ω]
    (d : FiniteDistribution Ω) : PMF Ω :=
  PMF.ofFintype (fun x ↦ ENNReal.ofReal (d.prob x)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun x _ ↦ d.prob_nonneg x), d.sum_prob]
    exact ENNReal.ofReal_one)

@[simp]
theorem FiniteDistribution.toPMF_apply {Ω : Type*} [Fintype Ω]
    (d : FiniteDistribution Ω) (x : Ω) : d.toPMF x = ENNReal.ofReal (d.prob x) := rfl

namespace DiscountedMDP

local instance : MeasurableSpace State := ⊤
local instance : MeasurableSpace Action := ⊤

/-- The actual distribution of a single action/next-state step. -/
noncomputable def stepMeasure (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (s : State) : Measure (Action × State) :=
  ((M.stationaryStage π).stepDistribution s).toPMF.toMeasure

instance stepMeasure_isProbabilityMeasure (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (s : State) :
    IsProbabilityMeasure (M.stepMeasure π s) := inferInstanceAs
      (IsProbabilityMeasure (((M.stationaryStage π).stepDistribution s).toPMF.toMeasure))

/-- The next action and state are sampled from the last state of the observed
history. The history's final pair records the state to act from. -/
noncomputable def historyKernel (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (n : ℕ) :
    Kernel (↥(Finset.Iic n) → Action × State) (Action × State) :=
  Kernel.ofFunOfCountable (fun history ↦ M.stepMeasure π (history ⟨n, Finset.mem_Iic.mpr le_rfl⟩).2)

instance historyKernel_isMarkovKernel (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (n : ℕ) :
    IsMarkovKernel (M.historyKernel π n) := by
  constructor
  intro history
  change IsProbabilityMeasure (M.stepMeasure π (history ⟨n, Finset.mem_Iic.mpr le_rfl⟩).2)
  infer_instance

/-- Infinite law on sequences `(a₀,s₁), (a₁,s₂), …`, constructed by
Ionescu–Tulcea from the actual initial-step law and controlled transition law. -/
noncomputable def infiniteTrajectoryLaw (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (s : State) : Measure (ℕ → Action × State) :=
  Kernel.trajMeasure (M.stepMeasure π s) (M.historyKernel π)

instance infiniteTrajectoryLaw_isProbabilityMeasure (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (s : State) :
    IsProbabilityMeasure (M.infiniteTrajectoryLaw π s) := by
  unfold infiniteTrajectoryLaw
  infer_instance

/-- The mass of each action/next-state pair is precisely the source's policy
probability times its transition probability. -/
theorem stepMeasure_singleton (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (s : State) (a : Action) (t : State) :
    M.stepMeasure π s {(a, t)} =
      ENNReal.ofReal ((π s).prob a * (M.transition s a).prob t) := by
  rw [stepMeasure, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
  rfl

/-- Every finite prefix of the infinite law is Mathlib's iterated finite
history-kernel law, started from the same first-step distribution. -/
theorem infiniteTrajectoryLaw_prefix (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (s : State) (n : ℕ) :
    (M.infiniteTrajectoryLaw π s).map (Preorder.frestrictLe n) =
      ((M.stepMeasure π s).map (MeasurableEquiv.piUnique
          (fun _ : ↥(Finset.Iic 0) ↦ Action × State)).symm).bind
        (fun x ↦ Kernel.partialTraj (X := fun _ : ℕ ↦ Action × State) (M.historyKernel π) 0 n x) := by
  unfold infiniteTrajectoryLaw Kernel.trajMeasure
  rw [Measure.map_comp _ _ (by fun_prop), Kernel.traj_map_frestrictLe]

/-- The first action/next-state pair has the actual policy-transition law. -/
theorem infiniteTrajectoryLaw_first (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (s : State) :
    (M.infiniteTrajectoryLaw π s).map (fun path ↦ path 0) = M.stepMeasure π s := by
  have hf : (fun path : ℕ → Action × State ↦ path 0) =
      (fun x : ↥(Finset.Iic 0) → Action × State ↦ x ⟨0, Finset.mem_Iic.mpr le_rfl⟩) ∘
        Preorder.frestrictLe 0 := rfl
  rw [hf, ← Measure.map_map (by fun_prop) (by fun_prop)]
  unfold infiniteTrajectoryLaw Kernel.trajMeasure
  rw [Measure.map_comp _ _ (by fun_prop), Kernel.traj_map_frestrictLe,
    Kernel.partialTraj_self, Measure.id_comp]
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  simp only [Function.comp_def, MeasurableEquiv.piUnique_symm_apply]
  simp

/-- The first finite prefix of the infinite law equals the independently
constructed one-stage trajectory law. -/
theorem infiniteTrajectoryLaw_one_prefix (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (s : State) :
    (M.infiniteTrajectoryLaw π s).map (fun path ↦
      (show FinitePath State Action [M.stationaryStage π].length from
        ((path 0).1, (path 0).2, PUnit.unit))) =
      ((DecisionStage.trajectoryLaw [M.stationaryStage π] s).toPMF).toMeasure := by
  have hf : (fun path : ℕ → Action × State ↦
      (show FinitePath State Action [M.stationaryStage π].length from
        ((path 0).1, (path 0).2, PUnit.unit))) =
      (fun p : Action × State ↦
        (show FinitePath State Action [M.stationaryStage π].length from
          (p.1, p.2, PUnit.unit))) ∘ (fun path ↦ path 0) := rfl
  rw [hf, ← Measure.map_map (by fun_prop) (by fun_prop), infiniteTrajectoryLaw_first]
  apply Measure.ext_of_singleton
  rintro ⟨a, t, ⟨⟩⟩
  rw [Measure.map_apply (by fun_prop) (measurableSet_singleton _)]
  have h : (fun p : Action × State ↦ (p.1, p.2, PUnit.unit)) ⁻¹' {(a, t, PUnit.unit)} =
      {(a, t)} := by
    ext p
    rcases p with ⟨b, u⟩
    simp
  rw [h, stepMeasure_singleton, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
  simp [FiniteDistribution.toPMF_apply, DecisionStage.trajectoryLaw, DecisionStage.pathWeight,
    stationaryStage]

/-- The history kernel uses the state actually reached by the previous step. -/
theorem historyKernel_apply (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (n : ℕ)
    (history : ↥(Finset.Iic n) → Action × State) :
    M.historyKernel π n history =
      M.stepMeasure π (history ⟨n, Finset.mem_Iic.mpr le_rfl⟩).2 := rfl

/-- Every finite history and next pair have the joint law obtained by applying
the actual policy/transition kernel to that history. -/
theorem infiniteTrajectoryLaw_history_step (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (s : State) (n : ℕ) :
    (M.infiniteTrajectoryLaw π s).map (Preorder.frestrictLe n) ⊗ₘ M.historyKernel π n =
      (M.infiniteTrajectoryLaw π s).map (fun path ↦ (Preorder.frestrictLe n path, path (n + 1))) := by
  exact Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure

end DiscountedMDP
end StatisticalRL
