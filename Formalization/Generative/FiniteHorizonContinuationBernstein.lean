import Formalization.Generative.FiniteHorizonEmpiricalContinuation
import Formalization.Probability.BernsteinFamily

/-! Actual-law Bernstein concentration for empirical optimal next-stage values.
Future-code independence is proved from the sampling experiment, not assumed. -/
open MeasureTheory ProbabilityTheory
namespace StatisticalRL.FiniteHorizonGenerative
variable {State Action : Type*} [Fintype State] [Fintype Action]
local instance finiteBernsteinStateMeasurable : MeasurableSpace State := ⊤
local instance finiteBernsteinRowMeasurable : MeasurableSpace (FiniteDistribution State) := ⊤

/-- Backward-optimal planning keeps precisely the given finite episode length. -/
theorem greedyStages_length (es : List (EnvironmentStage State Action)) :
    (EnvironmentStage.greedyStages es).length = es.length := by
  induction es with
  | nil => rfl
  | cons e es ih => simpa only [EnvironmentStage.greedyStages, List.length_cons] using congrArg Nat.succ ih

/-- Actual empirical next-stage trajectory values lie in the remaining horizon. -/
theorem empiricalContinuationValue_bounds {H : ℕ} (E : Fin H → EnvironmentStage State Action)
    (N : ℕ) (hN : 0 < N) (h : Fin H) (data : Samples State Action H N) (s : State) :
    0 ≤ empiricalContinuationValue E N hN h data s ∧
      empiricalContinuationValue E N hN h data s ≤ (H - (h.val + 1) : ℕ) := by
  unfold empiricalContinuationValue
  rw [DecisionStage.trajectoryValue_eq_backwardValue]
  exact ⟨DecisionStage.backwardValue_nonneg _ s,
    (DecisionStage.backwardValue_le_length _ s).trans_eq (by
      rw [greedyStages_length, List.length_drop, empiricalStages_length])⟩

theorem empiricalContinuationValue_norm_le {H : ℕ} (E : Fin H → EnvironmentStage State Action)
    (N : ℕ) (hN : 0 < N) (h : Fin H) (data : Samples State Action H N) :
    ‖empiricalContinuationValue E N hN h data‖ ≤ (H - (h.val + 1) : ℕ) := by
  apply (pi_norm_le_iff_of_nonneg (by positivity)).2
  intro s
  rw [Real.norm_eq_abs, abs_of_nonneg (empiricalContinuationValue_bounds E N hN h data s).1]
  exact (empiricalContinuationValue_bounds E N hN h data s).2

/-- Every fixed future-data code has the same row concentration guarantee
under the genuine true-row product law. This is the conditional slice before
mixing it with the actual independent future block. -/
theorem empiricalContinuationValue_code_row_bernstein {H : ℕ}
    (E : Fin H → EnvironmentStage State Action) (N : ℕ) (hN : 0 < N)
    (h : Fin H) (s : State) (a : Action) (x : State)
    (code : FutureCode (State := State) (Action := Action) h N)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    let V := empiricalContinuationValue E N hN h (completeFutureData h N x code)
    1 - δ < (((E h).transition s a).sampleMeasure N).real {row |
      |(FiniteDistribution.empiricalRow N hN row).expectation V -
        ((E h).transition s a).expectation V| ≤
      FiniteDistribution.bernsteinRadius ((E h).transition s a) N 1 δ V} := by
  classical
  let V := empiricalContinuationValue E N hN h (completeFutureData h N x code)
  have hv : ∀ W ∈ ({V} : Finset (State → ℝ)), ∀ t, 0 ≤ W t := by
    intro W hW t
    have he : W = V := Finset.mem_singleton.mp hW
    rw [he]
    exact (empiricalContinuationValue_bounds E N hN h _ t).1
  have hp := ((E h).transition s a).empiricalRow_bernsteinFamily_success_gt N hN {V} δ hδ hδ1 hv
  simpa only [Finset.mem_singleton, forall_eq, Finset.card_singleton] using hp

/-- Actual-law row Bernstein guarantee for the empirical optimal continuation
vector. It is a random function of future samples, not a fixed true value. -/
theorem empiricalContinuationValue_row_bernstein {H : ℕ}
    (E : Fin H → EnvironmentStage State Action) (N : ℕ) (hN : 0 < N)
    (h : Fin H) (s : State) (a : Action) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    1 - δ < (samplingLaw E N).real {data |
      |((empiricalStage E N hN data h).transition s a).expectation
          (empiricalContinuationValue E N hN h data) -
        ((E h).transition s a).expectation (empiricalContinuationValue E N hN h data)| ≤
      FiniteDistribution.bernsteinRadius ((E h).transition s a) N 1 δ
        (empiricalContinuationValue E N hN h data)} := by
  classical
  let μ := samplingLaw E N
  let d := (E h).transition s a
  let x := Classical.choice (E h).state_nonempty
  let code := futureData (State := State) (Action := Action) h N
  let value : FutureCode (State := State) (Action := Action) h N → State → ℝ :=
    fun c ↦ empiricalContinuationValue E N hN h (completeFutureData h N x c)
  let family : FutureCode (State := State) (Action := Action) h N → Finset (State → ℝ) :=
    fun c ↦ {value c}
  let draw : Samples State Action H N → Fin N → State := fun data i ↦ data ((h,s,a),i)
  have hdraw : Measurable draw := measurable_of_countable _
  have hlaw : μ.map draw = d.sampleMeasure N := samplingLaw_row E N h s a
  have hcode : Measurable code := measurable_of_countable _
  have hrow : Measurable (fun row : Fin N → State ↦ FiniteDistribution.empiricalRow N hN row) :=
    measurable_of_countable _
  have hi : IndepFun code (fun data ↦ FiniteDistribution.empiricalRow N hN (draw data)) μ :=
    (futureData_indep_row E N h s a).comp measurable_id hrow
  have hv : ∀ᵐ data ∂μ, ∀ V ∈ family (code data), ∀ t, 0 ≤ V t := by
    apply Filter.Eventually.of_forall
    intro data V hV t
    have he : V = value (code data) := Finset.mem_singleton.mp hV
    rw [he]
    exact (empiricalContinuationValue_bounds E N hN h _ t).1
  have hvmeas : MeasurableSet {c | ∀ V ∈ family c, ∀ t, 0 ≤ V t} :=
    (Set.to_countable _).measurableSet
  have hbad : ∀ row ∈ FiniteDistribution.empiricalRows N hN,
      MeasurableSet {c | FiniteDistribution.bernsteinFamilyBadAt d N δ (family c) row} :=
    fun row hrow ↦ (Set.to_countable _).measurableSet
  have hs := d.randomFamily_bernstein_success_gt μ N hN δ hδ hδ1 draw hdraw hlaw code hcode family
    hi hv hvmeas hbad
  have he (data : Samples State Action H N) : value (code data) = empiricalContinuationValue E N hN h data :=
    (empiricalContinuationValue_factors_future E N hN h x data).symm
  let good : Set (Samples State Action H N) := {data | ∀ V ∈ family (code data),
      |(FiniteDistribution.empiricalRow N hN (draw data)).expectation V - d.expectation V| ≤
        FiniteDistribution.bernsteinRadius d N (family (code data)).card δ V}
  let target : Set (Samples State Action H N) := {data |
      |((empiricalStage E N hN data h).transition s a).expectation (empiricalContinuationValue E N hN h data) -
        d.expectation (empiricalContinuationValue E N hN h data)| ≤
        FiniteDistribution.bernsteinRadius d N 1 δ (empiricalContinuationValue E N hN h data)}
  have hsub : good ⊆ target := by
    intro data hd
    have hh := hd (value (code data)) (Finset.mem_singleton_self _)
    have hcard : (family (code data)).card = 1 := Finset.card_singleton _
    rw [hcard, he data] at hh
    exact hh
  exact hs.trans_le (measureReal_mono hsub (measure_ne_top μ target))

/-- A remaining-horizon radius corollary retains the true-row variance of
the actual random continuation and bounds only its linear Bernstein term. -/
theorem empiricalContinuationValue_row_bernstein_remaining {H : ℕ}
    (E : Fin H → EnvironmentStage State Action) (N : ℕ) (hN : 0 < N)
    (h : Fin H) (s : State) (a : Action) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    1 - δ < (samplingLaw E N).real {data |
      |((empiricalStage E N hN data h).transition s a).expectation
          (empiricalContinuationValue E N hN h data) -
        ((E h).transition s a).expectation (empiricalContinuationValue E N hN h data)| ≤
      Real.sqrt (2 * Real.log (4 / δ) / N) *
        Real.sqrt (((E h).transition s a).variance (empiricalContinuationValue E N hN h data)) +
      2 * (H - (h.val + 1) : ℕ) * Real.log (4 / δ) / (3 * N)} := by
  let good : Set (Samples State Action H N) := {data |
      |((empiricalStage E N hN data h).transition s a).expectation (empiricalContinuationValue E N hN h data) -
        ((E h).transition s a).expectation (empiricalContinuationValue E N hN h data)| ≤
      FiniteDistribution.bernsteinRadius ((E h).transition s a) N 1 δ
        (empiricalContinuationValue E N hN h data)}
  have hp : 1 - δ < (samplingLaw E N).real good := empiricalContinuationValue_row_bernstein E N hN h s a δ hδ hδ1
  apply hp.trans_le
  apply measureReal_mono _ (measure_ne_top (samplingLaw E N) _)
  intro data hd
  have hr := FiniteDistribution.bernsteinRadius_eq_source ((E h).transition s a) N 1 δ
    (empiricalContinuationValue E N hN h data)
  norm_num only [Nat.cast_one, mul_one] at hr
  change _ ≤ FiniteDistribution.bernsteinRadius _ N 1 δ _ at hd
  rw [hr] at hd
  have hlog : 0 ≤ Real.log (4 / δ) := Real.log_nonneg ((le_div_iff₀ hδ).2 (by linarith))
  apply hd.trans
  apply add_le_add le_rfl
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (empiricalContinuationValue_norm_le E N hN h data) (by norm_num)) hlog) (by positivity)

end StatisticalRL.FiniteHorizonGenerative
