import Formalization.MDP.InfinitePrefix

/-!
# Bridge toward finite path semantics

These lemmas analyze finite cylinders of the actual infinite trajectory law.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace StatisticalRL.DiscountedMDP

variable {State Action : Type*} [Fintype State] [Fintype Action]
local instance finitePrefixBridgeStateMeasurable : MeasurableSpace State := ⊤
local instance finitePrefixBridgeActionMeasurable : MeasurableSpace Action := ⊤

/-- Drop the first pair and reindex a history from zero. -/
def historyTail (n : ℕ) (history : ↥(Finset.Iic (n + 1)) → Action × State) :
    ↥(Finset.Iic n) → Action × State :=
  fun i ↦ history ⟨i.1 + 1, Finset.mem_Iic.mpr (Nat.succ_le_succ (Finset.mem_Iic.mp i.2))⟩

omit [Fintype State] [Fintype Action] in
/-- Dropping the first and last pairs commutes. -/
theorem historyTail_cut (n : ℕ)
    (history : ↥(Finset.Iic (n + 2)) → Action × State) :
    historyTail n (historyCut (n + 1) history) =
      historyCut n (historyTail (n + 1) history) := by
  funext i
  rfl

/-- Every cylinder mass factors as its first policy-transition probability and
its remaining product started from the state reached by that first step. -/
theorem historyMass_first_step (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (s : State) (n : ℕ)
    (history : ↥(Finset.Iic (n + 1)) → Action × State) :
    historyMass M π s (n + 1) history =
      ENNReal.ofReal ((π s).prob (history ⟨0, Finset.mem_Iic.mpr (Nat.zero_le _)⟩).1 *
        (M.transition s (history ⟨0, Finset.mem_Iic.mpr (Nat.zero_le _)⟩).1).prob
          (history ⟨0, Finset.mem_Iic.mpr (Nat.zero_le _)⟩).2) *
      historyMass M π (history ⟨0, Finset.mem_Iic.mpr (Nat.zero_le _)⟩).2 n
        (historyTail n history) := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    rw [historyMass, ih s (historyCut (n + 1) history), historyMass,
      ← historyTail_cut]
    simp only [historyCut, historyTail, mul_assoc]

/-- Reindex the first `stages.length + 1` action/state pairs into the actual
inductively defined finite path type. The stage list supplies only the length. -/
def historyToFinitePath : (stages : List (DecisionStage State Action)) →
    (↥(Finset.Iic stages.length) → Action × State) →
      FinitePath State Action (stages.length + 1)
  | [], history => ((history ⟨0, Finset.mem_Iic.mpr le_rfl⟩).1,
      (history ⟨0, Finset.mem_Iic.mpr le_rfl⟩).2, PUnit.unit)
  | _ :: tail, history =>
    ((history ⟨0, Finset.mem_Iic.mpr (Nat.zero_le _)⟩).1,
      (history ⟨0, Finset.mem_Iic.mpr (Nat.zero_le _)⟩).2,
      historyToFinitePath tail (historyTail tail.length history))

/-- The cylinder product is the independently defined finite path mass for
any list consisting of copies of the same stationary stage. -/
theorem historyMass_eq_finitePathWeight (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (stages : List (DecisionStage State Action))
    (hstage : ∀ x ∈ stages, x = M.stationaryStage π) (s : State)
    (history : ↥(Finset.Iic stages.length) → Action × State) :
    historyMass M π s stages.length history =
      ENNReal.ofReal (DecisionStage.pathWeight (M.stationaryStage π :: stages) s
        (historyToFinitePath stages history)) := by
  induction stages generalizing s with
  | nil => simp [historyMass, historyToFinitePath, DecisionStage.pathWeight, stationaryStage]
  | cons stage tail ih =>
    have hs : stage = M.stationaryStage π := hstage stage (by simp)
    subst stage
    have ht : ∀ x ∈ tail, x = M.stationaryStage π := by
      intro x hx
      exact hstage x (by simp [hx])
    change historyMass M π s (tail.length + 1) history = _
    rw [historyMass_first_step]
    rw [ih ht]
    simp only [historyToFinitePath, DecisionStage.pathWeight, stationaryStage]
    rw [ENNReal.ofReal_mul (mul_nonneg ((π s).prob_nonneg _)
      ((M.transition s _).prob_nonneg _))]

/-- Add a first pair to a finite history and shift all previous indices. -/
def historyCons (n : ℕ) (p : Action × State) (tail : ↥(Finset.Iic n) → Action × State) :
    ↥(Finset.Iic (n + 1)) → Action × State := fun i ↦
  if hi : i.1 = 0 then p else tail ⟨i.1 - 1, Finset.mem_Iic.mpr (by
    have hib := Finset.mem_Iic.mp i.2
    omega)⟩

omit [Fintype State] [Fintype Action] in
@[simp] theorem historyTail_cons (n : ℕ) (p : Action × State)
    (tail : ↥(Finset.Iic n) → Action × State) :
    historyTail n (historyCons n p tail) = tail := by
  funext i
  simp [historyTail, historyCons]

omit [Fintype State] [Fintype Action] in
/-- Decomposing a history into its first pair and tail loses no information. -/
theorem historyCons_head_tail (n : ℕ) (history : ↥(Finset.Iic (n + 1)) → Action × State) :
    historyCons n (history ⟨0, Finset.mem_Iic.mpr (Nat.zero_le _)⟩)
      (historyTail n history) = history := by
  funext i
  by_cases hi : i.1 = 0
  · have heq : i = ⟨0, Finset.mem_Iic.mpr (Nat.zero_le _)⟩ := Subtype.ext hi
    subst i
    simp [historyCons]
  · simp only [historyCons, hi, dite_false, historyTail]
    apply congrArg history
    apply Subtype.ext
    change i.1 - 1 + 1 = i.1
    omega

/-- Encode a finite path as its indexed action/next-state history. -/
def finitePathToHistory : (stages : List (DecisionStage State Action)) →
    FinitePath State Action (stages.length + 1) →
      (↥(Finset.Iic stages.length) → Action × State)
  | [], path => fun _ ↦ (path.1, path.2.1)
  | _ :: tail, path => historyCons tail.length (path.1, path.2.1)
      (finitePathToHistory tail path.2.2)

/-- Every indexed history is recovered from its finite path. -/
theorem finitePathToHistory_historyToFinitePath
    (stages : List (DecisionStage State Action))
    (history : ↥(Finset.Iic stages.length) → Action × State) :
    finitePathToHistory stages (historyToFinitePath stages history) = history := by
  induction stages with
  | nil =>
    funext i
    have heq : i = ⟨0, Finset.mem_Iic.mpr le_rfl⟩ := by
      apply Subtype.ext
      exact Nat.eq_zero_of_le_zero (Finset.mem_Iic.mp i.2)
    rw [heq]
    rfl
  | cons stage tail ih =>
    simp only [historyToFinitePath, finitePathToHistory]
    rw [ih]
    exact historyCons_head_tail _ _

/-- Every finite path is recovered from its indexed history. -/
theorem historyToFinitePath_finitePathToHistory
    (stages : List (DecisionStage State Action))
    (path : FinitePath State Action (stages.length + 1)) :
    historyToFinitePath stages (finitePathToHistory stages path) = path := by
  induction stages with
  | nil => rcases path with ⟨a, t, ⟨⟩⟩; rfl
  | cons stage tail ih =>
    rcases path with ⟨a, t, path⟩
    simp only [finitePathToHistory, historyToFinitePath, historyTail_cons, ih]
    simp [historyCons]

/-- The two encodings are a genuine equivalence. -/
def historyFinitePathEquiv (stages : List (DecisionStage State Action)) :
    (↥(Finset.Iic stages.length) → Action × State) ≃
      FinitePath State Action (stages.length + 1) where
  toFun := historyToFinitePath stages
  invFun := finitePathToHistory stages
  left_inv := finitePathToHistory_historyToFinitePath stages
  right_inv := historyToFinitePath_finitePathToHistory stages

/-- For a nonempty stationary stage list, the indexed cylinder law is exactly
the independently constructed finite trajectory law after reindexing. -/
theorem infiniteTrajectoryLaw_map_historyFinitePath (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (stages : List (DecisionStage State Action))
    (hstage : ∀ x ∈ stages, x = M.stationaryStage π) (s : State) :
    ((M.infiniteTrajectoryLaw π s).map (Preorder.frestrictLe stages.length)).map
      (historyToFinitePath stages) =
        (DecisionStage.trajectoryLaw (M.stationaryStage π :: stages) s).toPMF.toMeasure := by
  apply Measure.ext_of_singleton
  intro path
  rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _)]
  have hpre : (historyToFinitePath stages) ⁻¹' {path} =
      {finitePathToHistory stages path} := by
    ext history
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro h
      apply (historyFinitePathEquiv stages).injective
      change historyToFinitePath stages history =
        historyToFinitePath stages (finitePathToHistory stages path)
      rw [h, historyToFinitePath_finitePathToHistory]
    · intro h
      rw [h, historyToFinitePath_finitePathToHistory]
  rw [hpre, M.infiniteTrajectoryLaw_prefix_singleton_eq_historyMass,
    M.historyMass_eq_finitePathWeight π stages hstage s]
  have hr : (DecisionStage.trajectoryLaw (M.stationaryStage π :: stages) s).toPMF.toMeasure
      {path} = ENNReal.ofReal (DecisionStage.pathWeight (M.stationaryStage π :: stages) s path) := by
    rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
    rfl
  simpa only [historyToFinitePath_finitePathToHistory] using hr.symm

/-- Extract precisely as many leading action/state pairs as there are stages. -/
def finitePrefix : (stages : List (DecisionStage State Action)) →
    (ℕ → Action × State) → FinitePath State Action stages.length
  | [], _ => PUnit.unit
  | _ :: tail, path => historyToFinitePath tail (Preorder.frestrictLe tail.length path)

/-- The entire finite-prefix pushforward of the infinite law agrees with the
independently constructed finite trajectory law, including the empty prefix. -/
theorem infiniteTrajectoryLaw_map_finitePrefix (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (stages : List (DecisionStage State Action))
    (hstage : ∀ x ∈ stages, x = M.stationaryStage π) (s : State) :
    (M.infiniteTrajectoryLaw π s).map (finitePrefix stages) =
      (DecisionStage.trajectoryLaw stages s).toPMF.toMeasure := by
  cases stages with
  | nil =>
    apply Measure.ext_of_singleton
    rintro ⟨⟩
    have hm : Measurable (finitePrefix ([] : List (DecisionStage State Action))) := by
      change Measurable (fun _ : ℕ → Action × State ↦ (PUnit.unit : FinitePath State Action 0))
      exact measurable_const
    rw [Measure.map_apply hm (measurableSet_singleton _)]
    have hpre : (finitePrefix ([] : List (DecisionStage State Action))) ⁻¹'
        {(PUnit.unit : FinitePath State Action 0)} = Set.univ := by
      ext path
      simp [finitePrefix]
    rw [hpre, measure_univ, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
    simp [FiniteDistribution.toPMF_apply, DecisionStage.trajectoryLaw, DecisionStage.pathWeight]
  | cons stage tail =>
    have hs : stage = M.stationaryStage π := hstage stage (by simp)
    subst stage
    have ht : ∀ x ∈ tail, x = M.stationaryStage π := by
      intro x hx
      exact hstage x (by simp [hx])
    change (M.infiniteTrajectoryLaw π s).map
      ((historyToFinitePath tail) ∘ (Preorder.frestrictLe tail.length)) = _
    rw [← Measure.map_map (measurable_of_countable _) (by fun_prop)]
    exact M.infiniteTrajectoryLaw_map_historyFinitePath π tail ht s

/-- The explicit prefix encoding preserves the first action/next-state pair. -/
theorem finitePrefix_cons_head (stage : DecisionStage State Action)
    (stages : List (DecisionStage State Action)) (path : ℕ → Action × State) :
    ((finitePrefix (stage :: stages) path).1,
      (finitePrefix (stage :: stages) path).2.1) = path 0 := by
  cases stages with
  | nil => rfl
  | cons next tail => rfl

/-- The tail of the encoded prefix is the encoding of the shifted trajectory. -/
theorem finitePrefix_cons_tail (stage : DecisionStage State Action)
    (stages : List (DecisionStage State Action)) (path : ℕ → Action × State) :
    (finitePrefix (stage :: stages) path).2.2 =
      finitePrefix stages (fun n ↦ path (n + 1)) := by
  cases stages with
  | nil => rfl
  | cons next tail =>
    change historyToFinitePath tail
      (historyTail tail.length (Preorder.frestrictLe (tail.length + 1) path)) =
      historyToFinitePath tail (Preorder.frestrictLe tail.length (fun n ↦ path (n + 1)))
    congr 1

/-- In particular, for every natural n, the first n pairs of the actual
infinite law have the law of n repeated stationary stages. -/
theorem infiniteTrajectoryLaw_map_replicatePrefix (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (s : State) (n : ℕ) :
    (M.infiniteTrajectoryLaw π s).map (finitePrefix (List.replicate n (M.stationaryStage π))) =
      (DecisionStage.trajectoryLaw (List.replicate n (M.stationaryStage π)) s).toPMF.toMeasure := by
  apply M.infiniteTrajectoryLaw_map_finitePrefix π
  intro stage hmem
  exact (List.mem_replicate.mp hmem).2

end StatisticalRL.DiscountedMDP
