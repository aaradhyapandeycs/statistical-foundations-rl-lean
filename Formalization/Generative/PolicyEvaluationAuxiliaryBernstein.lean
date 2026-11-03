import Formalization.Generative.PolicyEvaluationAuxiliary
import Formalization.Generative.PolicyEvaluationHoeffding
import Formalization.Probability.BernsteinFamily

/-! Simultaneous Bernstein control of the source's deterministic auxiliary values. -/

open scoped BigOperators
open MeasureTheory ProbabilityTheory

namespace StatisticalRL.ModelBasedPolicyEvaluation

variable {State Action : Type*} [Fintype State] [Fintype Action]
local instance auxBernsteinStateMeasurable : MeasurableSpace State := ⊤

/-- The genuine joint policy-row sampling law simultaneously controls every
true auxiliary vector at levels 0 through m, for every state. -/
theorem auxiliaryValues_bernstein (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (N : ℕ) (hN : 0 < N)
    (m : ℕ) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    1 - δ < (samplingLaw M π N).real {data | ∀ (s : State) (l : Fin (m + 1)),
      |(empiricalPolicyRow N hN data s).expectation (auxiliaryValue M π l) -
        (M.policyTransition π s).expectation (auxiliaryValue M π l)| ≤
      FiniteDistribution.bernsteinRadius (M.policyTransition π s) N (m + 1)
        (δ / Fintype.card State) (auxiliaryValue M π l)} := by
  classical
  letI : Nonempty State := M.state_nonempty
  let I := State × Fin (m + 1)
  let S : ℝ := Fintype.card State
  let K : ℝ := m + 1
  let η : ℝ := δ / S
  let μ := samplingLaw M π N
  have hS : 0 < S := by dsimp [S]; exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
  have hS1 : 1 ≤ S := by dsimp [S]; exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
  have hK : 0 < K := by dsimp [K]; positivity
  have hη : 0 < η := div_pos hδ hS
  have hη1 : η < 1 := by dsimp [η]; rw [div_lt_iff₀ hS]; linarith
  let bad (i : I) : Set (Samples State N) := {data |
    FiniteDistribution.bernsteinRadius (M.policyTransition π i.1) N (m + 1) η
      (auxiliaryValue M π i.2) <
    |(empiricalPolicyRow N hN data i.1).expectation (auxiliaryValue M π i.2) -
      (M.policyTransition π i.1).expectation (auxiliaryValue M π i.2)|}
  have hbad (i : I) : μ.real (bad i) ≤ η / (2 * K) := by
    let d := M.policyTransition π i.1
    have ht := d.bernsteinViolation_le N (m + 1) hN (by omega) η hη hη1
      (auxiliaryValue M π i.2) (auxiliaryValue_nonneg M π i.2)
    have hmeas : MeasurableSet (d.bernsteinViolation N hN (m + 1) η
        (auxiliaryValue M π i.2)) := (Set.to_countable _).measurableSet
    rw [← samplingLaw_stateRow M π N i.1, measureReal_def,
      Measure.map_apply (measurable_of_countable _) hmeas] at ht
    simp only [Nat.cast_add, Nat.cast_one] at ht
    change μ.real (bad i) ≤ η / (2 * K) at ht
    exact ht
  have hbadall : μ.real (⋃ i : I, bad i) ≤ δ / 2 := by
    calc
      _ ≤ ∑ i : I, μ.real (bad i) := measureReal_iUnion_fintype_le _
      _ ≤ ∑ _i : I, η / (2 * K) := Finset.sum_le_sum (fun i _ ↦ hbad i)
      _ = δ / 2 := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        dsimp [I, η, S, K]
        simp only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
        field_simp
  let good : Set (Samples State N) := {data | ∀ (s : State) (l : Fin (m + 1)),
      |(empiricalPolicyRow N hN data s).expectation (auxiliaryValue M π l) -
        (M.policyTransition π s).expectation (auxiliaryValue M π l)| ≤
      FiniteDistribution.bernsteinRadius (M.policyTransition π s) N (m + 1)
        η (auxiliaryValue M π l)}
  have hsub : (⋃ i : I, bad i)ᶜ ⊆ good := by
    intro data hd s l
    exact not_lt.mp (fun h ↦ hd (Set.mem_iUnion.mpr ⟨(s,l), h⟩))
  have hmono := measureReal_mono hsub (measure_ne_top μ good)
  have hc := measureReal_compl (μ := μ) ((Set.to_countable (⋃ i : I, bad i)).measurableSet)
  rw [probReal_univ] at hc
  change 1 - δ < μ.real good
  linarith

/-- The simultaneous event with the Bernstein radius expanded into the
variance and logarithmic terms, uniformly through level m inclusive. -/
theorem auxiliaryValues_bernstein_explicit (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (N : ℕ) (hN : 0 < N)
    (m : ℕ) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    1 - δ < (samplingLaw M π N).real {data | ∀ (s : State) (l : Fin (m + 1)),
      |(empiricalPolicyRow N hN data s).expectation (auxiliaryValue M π l) -
        (M.policyTransition π s).expectation (auxiliaryValue M π l)| ≤
      Real.sqrt (2 * Real.log (4 * Fintype.card State * (m + 1) / δ) / N) *
        Real.sqrt ((M.policyTransition π s).variance (auxiliaryValue M π l)) +
      2 * ‖auxiliaryValue M π l‖ * Real.log (4 * Fintype.card State * (m + 1) / δ) / (3 * N)} := by
  letI : Nonempty State := M.state_nonempty
  have hs : (Fintype.card State : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hlog : 4 * ((m + 1 : ℕ) : ℝ) / (δ / Fintype.card State) =
      4 * Fintype.card State * ((m : ℝ) + 1) / δ := by
    push_cast
    field_simp
  simp only [Nat.cast_add, Nat.cast_one] at hlog
  have h := auxiliaryValues_bernstein M π N hN m δ hδ hδ1
  simp only [FiniteDistribution.bernsteinRadius_eq_source, Nat.cast_add, Nat.cast_one, hlog] at h
  exact h

end StatisticalRL.ModelBasedPolicyEvaluation
