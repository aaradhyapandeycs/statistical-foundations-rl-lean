import Formalization.MDP.FiniteOptimal
import Formalization.Probability.EmpiricalRow
import Mathlib.Probability.Independence.Basic

/-! The actual finite-horizon stage/state/action generative experiment and
its strictly-future block independence. No policy-learning guarantee is claimed. -/
open MeasureTheory ProbabilityTheory
namespace StatisticalRL.FiniteHorizonGenerative
variable {State Action : Type*} [Fintype State] [Fintype Action]
local instance finiteStageStateMeasurable : MeasurableSpace State := ⊤
noncomputable local instance finiteStageStateDecidable : DecidableEq State := Classical.decEq State
noncomputable local instance finiteStageActionDecidable : DecidableEq Action := Classical.decEq Action

abbrev SampleIndex (State Action : Type*) (H N : ℕ) := (Fin H × State × Action) × Fin N
abbrev Samples (State Action : Type*) (H N : ℕ) := SampleIndex State Action H N → State

/-- The observation count is H·S·A·N, with N samples per tuple. -/
theorem sampleIndex_card (H N : ℕ) :
    Fintype.card (SampleIndex State Action H N) =
      H * Fintype.card State * Fintype.card Action * N := by
  simp [SampleIndex, Nat.mul_assoc]

/-- N actual independent next-state observations at every stage/state/action. -/
noncomputable def samplingLaw {H : ℕ} (E : Fin H → EnvironmentStage State Action) (N : ℕ) :
    Measure (Samples State Action H N) :=
  Measure.pi (fun i : SampleIndex State Action H N ↦
    ((E i.1.1).transition i.1.2.1 i.1.2.2).rowMeasure)

instance samplingLaw_probability {H : ℕ} (E : Fin H → EnvironmentStage State Action) (N : ℕ) :
    IsProbabilityMeasure (samplingLaw E N) := by unfold samplingLaw; infer_instance

theorem samplingLaw_marginal {H : ℕ} (E : Fin H → EnvironmentStage State Action)
    (N : ℕ) (i : SampleIndex State Action H N) :
    (samplingLaw E N).map (fun data ↦ data i) =
      ((E i.1.1).transition i.1.2.1 i.1.2.2).rowMeasure := by
  exact (measurePreserving_eval (fun i : SampleIndex State Action H N ↦
    ((E i.1.1).transition i.1.2.1 i.1.2.2).rowMeasure) i).map_eq

theorem samplingLaw_independent {H : ℕ} (E : Fin H → EnvironmentStage State Action) (N : ℕ) :
    iIndepFun (fun i (data : Samples State Action H N) ↦ data i) (samplingLaw E N) := by
  exact iIndepFun_pi (fun _ ↦ measurable_id.aemeasurable)

/-- Each complete row has precisely its true iid product law. -/
theorem samplingLaw_row {H : ℕ} (E : Fin H → EnvironmentStage State Action)
    (N : ℕ) (h : Fin H) (s : State) (a : Action) :
    (samplingLaw E N).map (fun data i ↦ data ((h,s,a),i)) =
      ((E h).transition s a).sampleMeasure N := by
  let j : Fin N → SampleIndex State Action H N := fun i ↦ ((h,s,a),i)
  have hj : Function.Injective j := by intro i k he; exact Prod.mk.inj he |>.2
  have hind := (samplingLaw_independent E N).precomp hj
  have hm : ∀ i : Fin N, AEMeasurable (fun data : Samples State Action H N ↦ data (j i))
      (samplingLaw E N) := fun i ↦ (measurable_pi_apply (j i)).aemeasurable
  rw [(iIndepFun_iff_map_fun_eq_pi_map hm).mp hind]
  unfold FiniteDistribution.sampleMeasure
  congr 1
  funext i
  exact samplingLaw_marginal E N (j i)

/-- The empirical stage keeps the original known reward exactly. -/
noncomputable def empiricalStage {H : ℕ} (E : Fin H → EnvironmentStage State Action)
    (N : ℕ) (hN : 0 < N) (data : Samples State Action H N) (h : Fin H) :
    EnvironmentStage State Action where
  state_nonempty := (E h).state_nonempty
  action_nonempty := (E h).action_nonempty
  transition := fun s a ↦ FiniteDistribution.empiricalRow N hN (fun i ↦ data ((h,s,a),i))
  reward := (E h).reward
  reward_nonneg := (E h).reward_nonneg
  reward_le_one := (E h).reward_le_one

theorem empiricalStage_reward {H : ℕ} (E : Fin H → EnvironmentStage State Action)
    (N : ℕ) (hN : 0 < N) (data : Samples State Action H N) (h : Fin H) :
    (empiricalStage E N hN data h).reward = (E h).reward := rfl

theorem empiricalStage_transition_expectation {H : ℕ} (E : Fin H → EnvironmentStage State Action)
    (N : ℕ) (hN : 0 < N) (data : Samples State Action H N) (h : Fin H)
    (s : State) (a : Action) (V : State → ℝ) :
    ((empiricalStage E N hN data h).transition s a).expectation V =
      (N : ℝ)⁻¹ * ∑ i : Fin N, V (data ((h,s,a),i)) :=
  FiniteDistribution.empiricalRow_expectation N hN (fun i ↦ data ((h,s,a),i)) V

/-- All observations strictly after stage h; no current-stage observation. -/
noncomputable def futureIndices {H : ℕ} (h : Fin H) (N : ℕ) :
    Finset (SampleIndex State Action H N) := Finset.univ.filter (fun i ↦ h < i.1.1)

noncomputable def rowIndices {H : ℕ} (h : Fin H) (s : State) (a : Action) (N : ℕ) :
    Finset (SampleIndex State Action H N) := Finset.univ.filter (fun i ↦ i.1 = (h,s,a))

abbrev FutureCode {H : ℕ} (h : Fin H) (N : ℕ) :=
  (i : futureIndices (State := State) (Action := Action) h N) → State

def futureData {H : ℕ} (h : Fin H) (N : ℕ) (data : Samples State Action H N) :
    FutureCode (State := State) (Action := Action) h N := fun i ↦ data i

theorem future_disjoint_row {H : ℕ} (h : Fin H) (s : State) (a : Action) (N : ℕ) :
    Disjoint (futureIndices (State := State) (Action := Action) h N) (rowIndices h s a N) := by
  apply Finset.disjoint_left.mpr
  intro i hi hj
  have ht := (Finset.mem_filter.mp hi).2
  have he := (Finset.mem_filter.mp hj).2
  have hh : i.1.1 = h := congrArg Prod.fst he
  exact (lt_irrefl h) (hh ▸ ht)

/-- The complete future-stage sample block is independent of a complete
current stage/state/action row under the actual product experiment. -/
theorem futureData_indep_row {H : ℕ} (E : Fin H → EnvironmentStage State Action)
    (N : ℕ) (h : Fin H) (s : State) (a : Action) :
    IndepFun (futureData (State := State) (Action := Action) h N)
      (fun data : Samples State Action H N ↦ fun i : Fin N ↦ data ((h,s,a),i))
      (samplingLaw E N) := by
  let S := futureIndices (State := State) (Action := Action) h N
  let T := rowIndices h s a N
  have hind := iIndepFun.indepFun_finset S T (future_disjoint_row h s a N)
    (samplingLaw_independent E N) (fun i ↦ measurable_pi_apply i)
  let getRow : ((i : T) → State) → Fin N → State := fun code i ↦
    code ⟨((h,s,a),i), by simp [T, rowIndices]⟩
  have hm : Measurable getRow := measurable_of_countable _
  exact hind.comp measurable_id hm

/-- Any statistic actually defined on strictly-future data is independent of
the current row. Factorization of a particular fitted value is a separate proof. -/
theorem futureStatistic_indep_row {H : ℕ} {β : Type*} [MeasurableSpace β]
    (E : Fin H → EnvironmentStage State Action) (N : ℕ) (h : Fin H)
    (s : State) (a : Action) (F : FutureCode (State := State) (Action := Action) h N → β) :
    IndepFun (fun data ↦ F (futureData h N data))
      (fun data : Samples State Action H N ↦ fun i : Fin N ↦ data ((h,s,a),i))
      (samplingLaw E N) := by
  exact (futureData_indep_row E N h s a).comp (measurable_of_countable F) measurable_id

end StatisticalRL.FiniteHorizonGenerative
