import Formalization.MDP.PrefixValueBridge
import Formalization.MDP.ForcedActionReturn
import Formalization.MDP.PolicyValueQ
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.Probability.ProbabilityMassFunction.Integrals

/-! # Forced first-action prefix and infinite Q value

The initial action is intervened on, including when its policy probability is
zero; the policy controls all subsequent actions. Source: arXiv:2610.41903v1,
`eq:defn-Qpi-inf-horizon` and `eq:bellman_consistency`.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal BigOperators Topology

namespace StatisticalRL.DiscountedMDP
variable {State Action : Type*} [Fintype State] [Fintype Action]
local instance forcedPrefixStateMeasurable : MeasurableSpace State := ⊤
local instance forcedPrefixActionMeasurable : MeasurableSpace Action := ⊤

/-- The same model with its initial decision rule concentrated on `a`. -/
noncomputable def forcedInitialStage (M : DiscountedMDP State Action) (a : Action) :
    DecisionStage State Action := M.stationaryStage (fun _ ↦ EnvironmentStage.pointMass a)

/-- Initial forced probability followed by actual π-controlled history masses. -/
noncomputable def forcedHistoryMass (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (s : State) (a : Action) :
    (n : ℕ) → (↥(Finset.Iic n) → Action × State) → ℝ≥0∞
  | 0, history =>
    ENNReal.ofReal (((EnvironmentStage.pointMass a).prob
      (history ⟨0, Finset.mem_Iic.mpr le_rfl⟩).1) *
      (M.transition s (history ⟨0, Finset.mem_Iic.mpr le_rfl⟩).1).prob
        (history ⟨0, Finset.mem_Iic.mpr le_rfl⟩).2)
  | n + 1, history =>
    forcedHistoryMass M π s a n (historyCut n history) *
      ENNReal.ofReal
        ((π (history ⟨n, Finset.mem_Iic.mpr (Nat.le_succ n)⟩).2).prob
          (history ⟨n + 1, Finset.mem_Iic.mpr le_rfl⟩).1 *
        (M.transition (history ⟨n, Finset.mem_Iic.mpr (Nat.le_succ n)⟩).2
          (history ⟨n + 1, Finset.mem_Iic.mpr le_rfl⟩).1).prob
          (history ⟨n + 1, Finset.mem_Iic.mpr le_rfl⟩).2)

/-- The cylinder of a forced-law history through `n+1` splits into its
preceding history and final pair. -/
theorem forcedHistoryCylinder_succ (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (s : State) (a : Action) (n : ℕ)
    (history : ↥(Finset.Iic (n + 1)) → Action × State) :
    (M.forcedActionTrajectoryLaw π s a).map (Preorder.frestrictLe (n + 1)) {history} =
      (M.forcedActionTrajectoryLaw π s a).map
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

/-- First forced-pair cylinder mass. -/
theorem forcedPrefix_singleton_zero (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (s : State) (a : Action)
    (history : ↥(Finset.Iic 0) → Action × State) :
    (M.forcedActionTrajectoryLaw π s a).map (Preorder.frestrictLe 0) {history} =
      forcedHistoryMass M π s a 0 history := by
  have hevent : (M.forcedActionTrajectoryLaw π s a).map (Preorder.frestrictLe 0) {history} =
      (M.forcedActionTrajectoryLaw π s a).map (fun path ↦ path 0)
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
  rw [hevent, M.forcedActionTrajectoryLaw_first, M.stepMeasure_singleton]
  rfl

/-- The actual forced law's finite cylinders have the corresponding product. -/
theorem forcedPrefix_singleton_eq_mass (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (s : State) (a : Action) (n : ℕ)
    (history : ↥(Finset.Iic n) → Action × State) :
    (M.forcedActionTrajectoryLaw π s a).map (Preorder.frestrictLe n) {history} =
      forcedHistoryMass M π s a n history := by
  induction n with
  | zero => exact M.forcedPrefix_singleton_zero π s a history
  | succ n ih =>
    rw [M.forcedHistoryCylinder_succ π s a n history, ← M.forcedActionTrajectoryLaw_history_step]
    have hset : ({(historyCut n history, history ⟨n + 1, Finset.mem_Iic.mpr le_rfl⟩)} :
        Set ((↥(Finset.Iic n) → Action × State) × (Action × State))) =
        ({historyCut n history} : Set (↥(Finset.Iic n) → Action × State)) ×ˢ
        ({history ⟨n + 1, Finset.mem_Iic.mpr le_rfl⟩} : Set (Action × State)) := by
      ext x
      simp
    rw [hset, Measure.compProd_apply_prod (measurableSet_singleton _) (measurableSet_singleton _),
      lintegral_singleton, M.historyKernel_apply, M.stepMeasure_singleton, mul_comm,
      ih (historyCut n history)]
    rfl

/-- Forced first-pair factor, followed by the ordinary stationary cylinder. -/
theorem forcedHistoryMass_first_step (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (s : State) (a : Action) (n : ℕ)
    (history : ↥(Finset.Iic (n + 1)) → Action × State) :
    forcedHistoryMass M π s a (n + 1) history =
      ENNReal.ofReal (((EnvironmentStage.pointMass a).prob
          (history ⟨0, Finset.mem_Iic.mpr (Nat.zero_le _)⟩).1) *
        (M.transition s (history ⟨0, Finset.mem_Iic.mpr (Nat.zero_le _)⟩).1).prob
          (history ⟨0, Finset.mem_Iic.mpr (Nat.zero_le _)⟩).2) *
      historyMass M π (history ⟨0, Finset.mem_Iic.mpr (Nat.zero_le _)⟩).2 n
        (historyTail n history) := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    rw [forcedHistoryMass, ih s (historyCut (n + 1) history), historyMass,
      ← historyTail_cut]
    simp only [historyCut, historyTail, mul_assoc]

/-- Forced cylinder mass equals the independently defined path weight for a
forced initial stage followed by the original stationary policy. -/
theorem forcedHistoryMass_eq_pathWeight (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (s : State) (a : Action)
    (tail : List (DecisionStage State Action))
    (htail : ∀ x ∈ tail, x = M.stationaryStage π)
    (history : ↥(Finset.Iic tail.length) → Action × State) :
    forcedHistoryMass M π s a tail.length history =
      ENNReal.ofReal (DecisionStage.pathWeight (M.forcedInitialStage a :: tail) s
        (historyToFinitePath tail history)) := by
  cases tail with
  | nil =>
    simp [forcedHistoryMass, historyToFinitePath, DecisionStage.pathWeight, forcedInitialStage,
      stationaryStage]
  | cons stage tail =>
    have hs : stage = M.stationaryStage π := htail stage (by simp)
    subst stage
    have ht : ∀ x ∈ tail, x = M.stationaryStage π := by
      intro x hx
      exact htail x (by simp [hx])
    change forcedHistoryMass M π s a (tail.length + 1) history = _
    rw [M.forcedHistoryMass_first_step π s a tail.length history]
    rw [M.historyMass_eq_finitePathWeight π tail ht]
    simp only [historyToFinitePath, DecisionStage.pathWeight, forcedInitialStage, stationaryStage]
    rw [ENNReal.ofReal_mul (mul_nonneg ((EnvironmentStage.pointMass a).prob_nonneg _)
      ((M.transition s _).prob_nonneg _))]

/-- The forced-law finite prefix is the genuine finite law with the same
forced first action and the original stationary policy on all later stages. -/
theorem forcedActionTrajectoryLaw_map_finitePrefix (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (s : State) (a : Action)
    (tail : List (DecisionStage State Action))
    (htail : ∀ x ∈ tail, x = M.stationaryStage π) :
    (M.forcedActionTrajectoryLaw π s a).map (finitePrefix (M.forcedInitialStage a :: tail)) =
      (DecisionStage.trajectoryLaw (M.forcedInitialStage a :: tail) s).toPMF.toMeasure := by
  change (M.forcedActionTrajectoryLaw π s a).map
    ((historyToFinitePath tail) ∘ (Preorder.frestrictLe tail.length)) = _
  rw [← Measure.map_map (measurable_of_countable _) (by fun_prop)]
  apply Measure.ext_of_singleton
  intro path
  rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _)]
  have hpre : (historyToFinitePath tail) ⁻¹' {path} = {finitePathToHistory tail path} := by
    ext history
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro h
      apply (historyFinitePathEquiv tail).injective
      change historyToFinitePath tail history =
        historyToFinitePath tail (finitePathToHistory tail path)
      rw [h, historyToFinitePath_finitePathToHistory]
    · intro h
      rw [h, historyToFinitePath_finitePathToHistory]
  rw [hpre, M.forcedPrefix_singleton_eq_mass, M.forcedHistoryMass_eq_pathWeight π s a tail htail]
  have hr : (DecisionStage.trajectoryLaw (M.forcedInitialStage a :: tail) s).toPMF.toMeasure
      {path} = ENNReal.ofReal (DecisionStage.pathWeight (M.forcedInitialStage a :: tail) s path) := by
    rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
    rfl
  simpa only [historyToFinitePath_finitePathToHistory] using hr.symm

/-- The actual (n+1)-reward path sum agrees with its forced finite prefix. -/
theorem partialDiscountedReturn_eq_forcedPath (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (s : State) (a : Action)
    (tail : List (DecisionStage State Action))
    (htail : ∀ x ∈ tail, x = M.stationaryStage π) (path : ℕ → Action × State) :
    M.partialDiscountedReturn s (tail.length + 1) path =
      DecisionStage.discountedPathReward M.discount (M.forcedInitialStage a :: tail) s
        (finitePrefix (M.forcedInitialStage a :: tail) path) := by
  rw [M.partialDiscountedReturn_first_step, M.partialDiscountedReturn_eq_finitePath π tail htail]
  change M.reward s (path 0).1 + M.discount *
      DecisionStage.discountedPathReward M.discount tail (path 0).2
        (finitePrefix tail (fun n ↦ path (n + 1))) = _
  change _ = M.reward s (finitePrefix (M.forcedInitialStage a :: tail) path).1 +
      M.discount * DecisionStage.discountedPathReward M.discount tail
        (finitePrefix (M.forcedInitialStage a :: tail) path).2.1
        (finitePrefix (M.forcedInitialStage a :: tail) path).2.2
  rw [finitePrefix_cons_tail]
  have hh := finitePrefix_cons_head (M.forcedInitialStage a) tail path
  have ha := congrArg Prod.fst hh
  have hs := congrArg Prod.snd hh
  simp only at ha hs
  rw [ha, hs]

/-- Finite probability integrals agree with the original finite expectations. -/
private theorem forcedFiniteDistribution_integral {Ω : Type*} [Fintype Ω]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (d : FiniteDistribution Ω) (f : Ω → ℝ) :
    ∫ x, f x ∂d.toPMF.toMeasure = d.expectation f := by
  rw [PMF.integral_eq_sum]
  simp only [FiniteDistribution.toPMF_apply, ENNReal.toReal_ofReal (d.prob_nonneg _),
    smul_eq_mul, FiniteDistribution.expectation]

/-- Expected forced finite prefix return is the immediate reward plus the
actual transition average of n further policy-controlled rewards. -/
theorem forced_integral_partial_return (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (s : State) (a : Action) (n : ℕ) :
    (∫ path, M.partialDiscountedReturn s (n + 1) path ∂M.forcedActionTrajectoryLaw π s a) =
      M.reward s a + M.discount * (M.transition s a).expectation (M.finiteDiscountedValue π n) := by
  let tail := List.replicate n (M.stationaryStage π)
  have ht : ∀ x ∈ tail, x = M.stationaryStage π := by
    intro x hx
    exact (List.mem_replicate.mp hx).2
  have heq (path : ℕ → Action × State) : M.partialDiscountedReturn s (n + 1) path =
      DecisionStage.discountedPathReward M.discount (M.forcedInitialStage a :: tail) s
        (finitePrefix (M.forcedInitialStage a :: tail) path) := by
    simpa only [tail, List.length_replicate] using
      M.partialDiscountedReturn_eq_forcedPath π s a tail ht path
  calc
    (∫ path, M.partialDiscountedReturn s (n + 1) path ∂M.forcedActionTrajectoryLaw π s a) =
        ∫ path, DecisionStage.discountedPathReward M.discount (M.forcedInitialStage a :: tail) s
          (finitePrefix (M.forcedInitialStage a :: tail) path)
          ∂M.forcedActionTrajectoryLaw π s a := integral_congr_ae (Filter.Eventually.of_forall heq)
    _ = ∫ path, DecisionStage.discountedPathReward M.discount (M.forcedInitialStage a :: tail) s path
          ∂((M.forcedActionTrajectoryLaw π s a).map (finitePrefix (M.forcedInitialStage a :: tail))) := by
      symm
      exact integral_map (measurable_finitePrefix _).aemeasurable
        (measurable_of_countable _).aestronglyMeasurable
    _ = ∫ path, DecisionStage.discountedPathReward M.discount (M.forcedInitialStage a :: tail) s path
          ∂(DecisionStage.trajectoryLaw (M.forcedInitialStage a :: tail) s).toPMF.toMeasure := by
      rw [M.forcedActionTrajectoryLaw_map_finitePrefix π s a tail ht]
    _ = M.reward s a + M.discount * (M.transition s a).expectation (M.finiteDiscountedValue π n) := by
      rw [forcedFiniteDistribution_integral]
      change DecisionStage.discountedTrajectoryValue M.discount (M.forcedInitialStage a :: tail) s = _
      rw [DecisionStage.discountedTrajectoryValue_cons]
      change (EnvironmentStage.pointMass a).expectation (fun b ↦ M.reward s b + M.discount *
        (M.transition s b).expectation (M.finiteDiscountedValue π n)) = _
      rw [EnvironmentStage.expectation_pointMass]

/-- The source's actual forced-action infinite Q equals the unique policy
Q-Bellman fixed point for every action, including zero-support actions. -/
theorem trajectoryExpectedQ_eq_policyFixedPoint (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (s : State) (a : Action) :
    M.trajectoryExpectedQ π s a = M.policyFixedPoint π s a := by
  have hnext : Tendsto (fun n ↦ (M.transition s a).expectation (M.finiteDiscountedValue π n))
      atTop (𝓝 ((M.transition s a).expectation (M.valueFixedPoint π))) := by
    unfold FiniteDistribution.expectation
    apply tendsto_finset_sum
    intro t _
    exact tendsto_const_nhds.mul ((tendsto_pi_nhds.mp (M.tendsto_finiteDiscountedValue π)) t)
  have hlim : Tendsto (fun n ↦ M.reward s a + M.discount *
      (M.transition s a).expectation (M.finiteDiscountedValue π n)) atTop
      (𝓝 (M.reward s a + M.discount * (M.transition s a).expectation (M.valueFixedPoint π))) :=
    tendsto_const_nhds.add (tendsto_const_nhds.mul hnext)
  have hshift : Tendsto (fun n : ℕ ↦ n + 1) atTop atTop :=
    tendsto_atTop_mono (fun n ↦ Nat.le_succ n) tendsto_id
  have hq := (M.tendsto_integral_partialDiscountedReturn_forced π s a).comp hshift
  change Tendsto (fun n : ℕ ↦ ∫ path, M.partialDiscountedReturn s (n + 1) path
    ∂M.forcedActionTrajectoryLaw π s a) atTop (𝓝 (M.trajectoryExpectedQ π s a)) at hq
  have heq : M.trajectoryExpectedQ π s a =
      M.reward s a + M.discount * (M.transition s a).expectation (M.valueFixedPoint π) := by
    apply tendsto_nhds_unique hq
    simpa only [M.forced_integral_partial_return π s a] using hlim
  rw [M.policyFixedPoint_eq_reward_add_value π s a]
  exact heq

/-- The actual intervention Q satisfies the source policy Q-Bellman equation. -/
theorem trajectoryExpectedQ_bellman (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) : M.qBellman π (M.trajectoryExpectedQ π) =
      M.trajectoryExpectedQ π := by
  have hq : M.trajectoryExpectedQ π = M.policyFixedPoint π := by
    funext s a
    exact M.trajectoryExpectedQ_eq_policyFixedPoint π s a
  rw [hq]
  exact M.policyFixedPoint_spec π

/-- Actual state value is the policy average of actual forced-action values. -/
theorem trajectoryExpectedValue_eq_policyAverageQ (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (s : State) :
    M.trajectoryExpectedValue π s = (π s).expectation (M.trajectoryExpectedQ π s) := by
  rw [M.trajectoryExpectedValue_eq_valueFixedPoint π, M.valueFixedPoint_eq_policyAverageQ π]
  change (π s).expectation (M.policyFixedPoint π s) = _
  congr 1
  funext a
  exact (M.trajectoryExpectedQ_eq_policyFixedPoint π s a).symm

end StatisticalRL.DiscountedMDP
