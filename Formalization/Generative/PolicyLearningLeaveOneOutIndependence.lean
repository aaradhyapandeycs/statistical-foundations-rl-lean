import Formalization.Generative.PolicyLearningAbsorbing
import Mathlib.Probability.Independence.Basic

/-! Fixed-parameter leave-one-out factorization and actual-law independence. -/

open MeasureTheory ProbabilityTheory

namespace StatisticalRL.ModelBasedPolicyLearning

variable {State Action : Type*} [Fintype State] [Fintype Action]
local instance looIndependenceStateMeasurable : MeasurableSpace State := ⊤
local instance looIndependenceRowMeasurable : MeasurableSpace (FiniteDistribution State) := ⊤
noncomputable local instance looIndependenceStateDecidable : DecidableEq State := Classical.decEq State
noncomputable local instance looIndependenceActionDecidable : DecidableEq Action := Classical.decEq Action

abbrev SampleIndex (State Action : Type*) (N : ℕ) := (State × Action) × Fin N

/-- All observations at states other than the removed state. -/
noncomputable def offStateIndices (x : State) (N : ℕ) : Finset (SampleIndex State Action N) :=
  Finset.univ.filter (fun i ↦ i.1.1 ≠ x)

/-- All observations in one removed state-action row. -/
noncomputable def removedRowIndices (x : State) (a : Action) (N : ℕ) : Finset (SampleIndex State Action N) :=
  Finset.univ.filter (fun i ↦ i.1 = (x,a))

abbrev OffStateCode (x : State) (N : ℕ) := (i : offStateIndices (Action := Action) x N) → State

/-- The actual data restricted to the off-state block. -/
def offStateData (x : State) (N : ℕ) (data : Samples State Action N) : OffStateCode (Action := Action) x N :=
  fun i ↦ data i

/-- The off-state code is measurable for the actual finite product sample space. -/
theorem offStateData_measurable (x : State) (N : ℕ) :
    Measurable (offStateData (Action := Action) x N) := by
  exact measurable_of_countable _

/-- Reconstruct a full table by filling every removed-state observation with x. -/
noncomputable def completeOffStateData (x : State) (N : ℕ)
    (code : OffStateCode (Action := Action) x N) : Samples State Action N := fun i ↦
  if h : i.1.1 ≠ x then code ⟨i, by simp [offStateIndices, h]⟩ else x

/-- The actual optimal trajectory value of the fixed-u absorbing empirical MDP. -/
noncomputable def fixedAbsorbingValue (M : DiscountedMDP State Action) (N : ℕ)
    (hN : 0 < N) (x : State) (u : ℝ) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / (1 - M.discount)) (data : Samples State Action N) : State → ℝ :=
  let H := stateAbsorbingModel (empiricalModel M N hN data) x u hu0 hu1
  H.trajectoryExpectedValue H.optimalGreedyPolicy

/-- The fixed-u value is a deterministic function of the off-state data. -/
theorem fixedAbsorbingValue_factors_offState (M : DiscountedMDP State Action) (N : ℕ)
    (hN : 0 < N) (x : State) (u : ℝ) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / (1 - M.discount)) (data : Samples State Action N) :
    fixedAbsorbingValue M N hN x u hu0 hu1 data =
      fixedAbsorbingValue M N hN x u hu0 hu1 (completeOffStateData x N (offStateData x N data)) := by
  funext s
  apply absorbingEmpirical_optimalValue_eq_of_data_eq_away M N hN data
    (completeOffStateData x N (offStateData x N data)) x u hu0 hu1
  intro t a i ht
  simp [completeOffStateData, offStateData, ht]

/-- The off-state and removed-row coordinate blocks are disjoint. -/
theorem offState_disjoint_removedRow (x : State) (a : Action) (N : ℕ) :
    Disjoint (offStateIndices (Action := Action) x N) (removedRowIndices x a N) := by
  apply Finset.disjoint_left.mpr
  intro i hi hj
  have hi' : i.1.1 ≠ x := (Finset.mem_filter.mp hi).2
  have hj' : i.1 = (x,a) := (Finset.mem_filter.mp hj).2
  exact hi' (congrArg Prod.fst hj')

/-- Under the actual product law, the off-state sample code is independent of
all N samples in the single removed state-action row. -/
theorem offStateData_indep_removedRow (M : DiscountedMDP State Action) (N : ℕ)
    (x : State) (a : Action) :
    IndepFun (offStateData (Action := Action) x N)
      (fun data : Samples State Action N ↦ fun i : Fin N ↦ data ((x,a),i)) (samplingLaw M N) := by
  let S := offStateIndices (Action := Action) x N
  let T := removedRowIndices x a N
  have hind := iIndepFun.indepFun_finset S T (offState_disjoint_removedRow x a N)
    (samplingLaw_independent M N) (fun i ↦ measurable_pi_apply i)
  let getRow : ((i : T) → State) → Fin N → State := fun code i ↦
    code ⟨((x,a),i), by simp [T, removedRowIndices]⟩
  have hm : Measurable getRow := by exact measurable_of_countable _
  have h := hind.comp measurable_id hm
  change IndepFun (offStateData (Action := Action) x N)
      (fun data : Samples State Action N ↦ fun i : Fin N ↦ data ((x,a),i)) (samplingLaw M N) at h
  exact h

/-- For a fixed u, the actual absorbing optimal trajectory-value vector is
independent of the full removed row samples under the genuine product law. -/
theorem fixedAbsorbingValue_indep_removedRow (M : DiscountedMDP State Action) (N : ℕ)
    (hN : 0 < N) (x : State) (a : Action) (u : ℝ) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / (1 - M.discount)) :
    IndepFun (fixedAbsorbingValue M N hN x u hu0 hu1)
      (fun data : Samples State Action N ↦ fun i : Fin N ↦ data ((x,a),i)) (samplingLaw M N) := by
  let F : OffStateCode (Action := Action) x N → State → ℝ := fun code ↦
    fixedAbsorbingValue M N hN x u hu0 hu1 (completeOffStateData x N code)
  have hm : Measurable F := measurable_of_countable _
  have h := (offStateData_indep_removedRow M N x a).comp hm measurable_id
  have heq : F ∘ offStateData (Action := Action) x N = fixedAbsorbingValue M N hN x u hu0 hu1 := by
    funext data
    exact (fixedAbsorbingValue_factors_offState M N hN x u hu0 hu1 data).symm
  rw [heq] at h
  exact h

/-- The off-state code is independent of the empirical frequency row; this
is the code-level input needed for random-family Bernstein. -/
theorem offStateData_indep_empiricalRow (M : DiscountedMDP State Action) (N : ℕ)
    (hN : 0 < N) (x : State) (a : Action) :
    IndepFun (offStateData (Action := Action) x N)
      (fun data : Samples State Action N ↦ empiricalRow N hN data x a) (samplingLaw M N) := by
  have hm : Measurable (fun ω : Fin N → State ↦ FiniteDistribution.empiricalRow N hN ω) :=
    measurable_of_countable _
  have h := (offStateData_indep_removedRow M N x a).comp measurable_id hm
  change IndepFun (offStateData (Action := Action) x N)
      (fun data : Samples State Action N ↦ empiricalRow N hN data x a) (samplingLaw M N) at h
  exact h

/-- Fixed-u optimal values are also independent of the empirical frequency
row itself, viewed with the discrete measurable structure. -/
theorem fixedAbsorbingValue_indep_empiricalRow (M : DiscountedMDP State Action) (N : ℕ)
    (hN : 0 < N) (x : State) (a : Action) (u : ℝ) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / (1 - M.discount)) :
    IndepFun (fixedAbsorbingValue M N hN x u hu0 hu1)
      (fun data : Samples State Action N ↦ empiricalRow N hN data x a) (samplingLaw M N) := by
  have hm : Measurable (fun ω : Fin N → State ↦ FiniteDistribution.empiricalRow N hN ω) := measurable_of_countable _
  have h := (fixedAbsorbingValue_indep_removedRow M N hN x a u hu0 hu1).comp measurable_id hm
  change IndepFun (fixedAbsorbingValue M N hN x u hu0 hu1)
      (fun data : Samples State Action N ↦ empiricalRow N hN data x a) (samplingLaw M N) at h
  exact h

/-- Every fixed finite indexed family of absorbing optimal values is jointly
independent of the removed empirical row. The parameters are fixed before
sampling; the index chosen after observing data is not asserted independent. -/
theorem fixedAbsorbingValue_family_indep_empiricalRow
    {ι : Type*} [Fintype ι] (M : DiscountedMDP State Action) (N : ℕ) (hN : 0 < N)
    (x : State) (a : Action) (u : ι → ℝ) (hu0 : ∀ j, 0 ≤ u j)
    (hu1 : ∀ j, u j ≤ 1 / (1 - M.discount)) :
    IndepFun (fun data : Samples State Action N ↦ fun j : ι ↦
      fixedAbsorbingValue M N hN x (u j) (hu0 j) (hu1 j) data)
      (fun data ↦ empiricalRow N hN data x a) (samplingLaw M N) := by
  let F : OffStateCode (Action := Action) x N → ι → State → ℝ := fun code j ↦
    fixedAbsorbingValue M N hN x (u j) (hu0 j) (hu1 j) (completeOffStateData x N code)
  have hF : Measurable F := measurable_of_countable _
  have hrow : Measurable (fun ω : Fin N → State ↦ FiniteDistribution.empiricalRow N hN ω) := measurable_of_countable _
  have h := (offStateData_indep_removedRow M N x a).comp hF hrow
  have heq : F ∘ offStateData (Action := Action) x N =
      (fun data : Samples State Action N ↦ fun j : ι ↦
        fixedAbsorbingValue M N hN x (u j) (hu0 j) (hu1 j) data) := by
    funext data j
    exact (fixedAbsorbingValue_factors_offState M N hN x (u j) (hu0 j) (hu1 j) data).symm
  rw [heq] at h
  change IndepFun (fun data : Samples State Action N ↦ fun j : ι ↦
      fixedAbsorbingValue M N hN x (u j) (hu0 j) (hu1 j) data)
      (fun data ↦ empiricalRow N hN data x a) (samplingLaw M N) at h
  exact h

end StatisticalRL.ModelBasedPolicyLearning
