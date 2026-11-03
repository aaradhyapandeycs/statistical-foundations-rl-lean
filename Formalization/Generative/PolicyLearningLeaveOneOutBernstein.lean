import Formalization.Generative.PolicyLearningLeaveOneOutIndependence
import Formalization.Generative.PolicyLearningHoeffding
import Formalization.Probability.BernsteinFamily

/-!
# Fixed auxiliary family Bernstein bound for a removed row

The parameter family is fixed before sampling. The event is simultaneous over
all indices, with the actual finite family cardinality in the radius. No
sample-selected parameter is declared independent.
-/

open MeasureTheory ProbabilityTheory

namespace StatisticalRL.ModelBasedPolicyLearning

variable {State Action : Type*} [Fintype State] [Fintype Action]
local instance looBernsteinStateMeasurable : MeasurableSpace State := ⊤
local instance looBernsteinRowMeasurable : MeasurableSpace (FiniteDistribution State) := ⊤
noncomputable local instance looBernsteinStateDecidable : DecidableEq State := Classical.decEq State
noncomputable local instance looBernsteinActionDecidable : DecidableEq Action := Classical.decEq Action

/-- Actual finite set of distinct auxiliary optimal-value vectors associated
with the fixed indexed parameter family and an off-state code. -/
noncomputable def fixedAbsorbingFamily {ι : Type*} [Fintype ι]
    (M : DiscountedMDP State Action) (N : ℕ) (hN : 0 < N) (x : State)
    (u : ι → ℝ) (hu0 : ∀ j, 0 ≤ u j) (hu1 : ∀ j, u j ≤ 1 / (1 - M.discount))
    (code : OffStateCode (Action := Action) x N) : Finset (State → ℝ) := by
  classical
  exact Finset.univ.image fun j ↦ fixedAbsorbingValue M N hN x (u j) (hu0 j) (hu1 j)
    (completeOffStateData x N code)

/-- Repeated value vectors are counted once: the image has at most as many
elements as parameter indices. -/
theorem fixedAbsorbingFamily_card_le {ι : Type*} [Fintype ι]
    (M : DiscountedMDP State Action) (N : ℕ) (hN : 0 < N) (x : State)
    (u : ι → ℝ) (hu0 : ∀ j, 0 ≤ u j) (hu1 : ∀ j, u j ≤ 1 / (1 - M.discount))
    (code : OffStateCode (Action := Action) x N) :
    (fixedAbsorbingFamily M N hN x u hu0 hu1 code).card ≤ Fintype.card ι := by
  classical
  exact (Finset.card_image_le).trans_eq Finset.card_univ

/-- Each member is an actual nonnegative infinite-trajectory policy value. -/
theorem fixedAbsorbingFamily_nonneg {ι : Type*} [Fintype ι]
    (M : DiscountedMDP State Action) (N : ℕ) (hN : 0 < N) (x : State)
    (u : ι → ℝ) (hu0 : ∀ j, 0 ≤ u j) (hu1 : ∀ j, u j ≤ 1 / (1 - M.discount))
    (code : OffStateCode (Action := Action) x N) (V : State → ℝ)
    (hV : V ∈ fixedAbsorbingFamily M N hN x u hu0 hu1 code) (s : State) : 0 ≤ V s := by
  classical
  obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hV
  exact ((stateAbsorbingModel (empiricalModel M N hN (completeOffStateData x N code))
    x (u j) (hu0 j) (hu1 j)).trajectoryExpectedValue_bounds _ s).1

/-- Under the actual joint sampling law, Bernstein controls every member of
the off-state-defined family for one removed row simultaneously. -/
theorem fixedAbsorbingFamily_row_bernstein {ι : Type*} [Fintype ι]
    (M : DiscountedMDP State Action) (N : ℕ) (hN : 0 < N) (x : State) (a : Action)
    (u : ι → ℝ) (hu0 : ∀ j, 0 ≤ u j) (hu1 : ∀ j, u j ≤ 1 / (1 - M.discount))
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    1 - δ < (samplingLaw M N).real {data | ∀ V ∈
        fixedAbsorbingFamily M N hN x u hu0 hu1 (offStateData x N data),
      |(empiricalRow N hN data x a).expectation V - (M.transition x a).expectation V| ≤
        FiniteDistribution.bernsteinRadius (M.transition x a) N
          (fixedAbsorbingFamily M N hN x u hu0 hu1 (offStateData x N data)).card δ V} := by
  classical
  let μ := samplingLaw M N
  let d := M.transition x a
  let draw : Samples State Action N → Fin N → State := fun data i ↦ data ((x,a),i)
  let code := offStateData (Action := Action) x N
  let family := fixedAbsorbingFamily M N hN x u hu0 hu1
  have hdraw : Measurable draw := measurable_of_countable _
  have hlaw : μ.map draw = d.sampleMeasure N := samplingLaw_stateActionRow M N x a
  have hcode : Measurable code := offStateData_measurable x N
  have hindep : IndepFun code (fun data ↦ FiniteDistribution.empiricalRow N hN (draw data)) μ := by
    exact offStateData_indep_empiricalRow M N hN x a
  have hV : ∀ᵐ data ∂μ, ∀ V ∈ family (code data), ∀ s, 0 ≤ V s := by
    exact Filter.Eventually.of_forall (fun data V hV s ↦
      fixedAbsorbingFamily_nonneg M N hN x u hu0 hu1 (code data) V hV s)
  have hVmeas : MeasurableSet {c | ∀ V ∈ family c, ∀ s, 0 ≤ V s} :=
    (Set.to_countable _).measurableSet
  have hbad : ∀ row ∈ FiniteDistribution.empiricalRows N hN,
      MeasurableSet {c | FiniteDistribution.bernsteinFamilyBadAt d N δ (family c) row} := by
    intro row hr
    exact (Set.to_countable _).measurableSet
  exact d.randomFamily_bernstein_success_gt μ N hN δ hδ hδ1 draw hdraw hlaw code hcode family
    hindep hV hVmeas hbad

/-- The same good event is simultaneous over every fixed parameter index;
indices may be selected only after the event is established. -/
theorem fixedAbsorbingValues_row_bernstein {ι : Type*} [Fintype ι]
    (M : DiscountedMDP State Action) (N : ℕ) (hN : 0 < N) (x : State) (a : Action)
    (u : ι → ℝ) (hu0 : ∀ j, 0 ≤ u j) (hu1 : ∀ j, u j ≤ 1 / (1 - M.discount))
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    1 - δ < (samplingLaw M N).real {data | ∀ j : ι,
      |(empiricalRow N hN data x a).expectation (fixedAbsorbingValue M N hN x (u j) (hu0 j) (hu1 j) data) -
        (M.transition x a).expectation (fixedAbsorbingValue M N hN x (u j) (hu0 j) (hu1 j) data)| ≤
      FiniteDistribution.bernsteinRadius (M.transition x a) N
        (fixedAbsorbingFamily M N hN x u hu0 hu1 (offStateData x N data)).card δ
          (fixedAbsorbingValue M N hN x (u j) (hu0 j) (hu1 j) data)} := by
  classical
  let μ := samplingLaw M N
  let good : Set (Samples State Action N) := {data | ∀ V ∈
      fixedAbsorbingFamily M N hN x u hu0 hu1 (offStateData x N data),
      |(empiricalRow N hN data x a).expectation V - (M.transition x a).expectation V| ≤
        FiniteDistribution.bernsteinRadius (M.transition x a) N
          (fixedAbsorbingFamily M N hN x u hu0 hu1 (offStateData x N data)).card δ V}
  let target : Set (Samples State Action N) := {data | ∀ j : ι,
      |(empiricalRow N hN data x a).expectation (fixedAbsorbingValue M N hN x (u j) (hu0 j) (hu1 j) data) -
        (M.transition x a).expectation (fixedAbsorbingValue M N hN x (u j) (hu0 j) (hu1 j) data)| ≤
      FiniteDistribution.bernsteinRadius (M.transition x a) N
        (fixedAbsorbingFamily M N hN x u hu0 hu1 (offStateData x N data)).card δ
          (fixedAbsorbingValue M N hN x (u j) (hu0 j) (hu1 j) data)}
  have hs : 1 - δ < μ.real good := fixedAbsorbingFamily_row_bernstein M N hN x a u hu0 hu1 δ hδ hδ1
  have hsub : good ⊆ target := by
    intro data hd j
    have hmem : fixedAbsorbingValue M N hN x (u j) (hu0 j) (hu1 j) data ∈
        fixedAbsorbingFamily M N hN x u hu0 hu1 (offStateData x N data) := by
      unfold fixedAbsorbingFamily
      apply Finset.mem_image.mpr
      refine ⟨j, Finset.mem_univ j, ?_⟩
      exact (fixedAbsorbingValue_factors_offState M N hN x (u j) (hu0 j) (hu1 j) data).symm
    exact hd _ hmem
  exact hs.trans_le (measureReal_mono hsub (measure_ne_top μ target))

end StatisticalRL.ModelBasedPolicyLearning
