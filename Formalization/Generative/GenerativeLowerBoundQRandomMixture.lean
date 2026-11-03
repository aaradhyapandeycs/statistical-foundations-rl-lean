import Formalization.Generative.GenerativeLowerBoundQRandomRiskSelection

/-! Averaging arbitrary-output risk over actual uniform mixture laws. -/
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators
namespace StatisticalRL.GenerativeLowerBound

/-- Actual joint output-event probability as a finite sum of conditional
probabilities; the output space can be arbitrary measurable. -/
theorem finiteDataRandomOutputLaw_real_event {X Y : Type*} [Fintype X]
    [MeasurableSpace X] [MeasurableSingletonClass X] [MeasurableSpace Y]
    (μ : Measure X) (κ : X → Measure Y) [IsProbabilityMeasure μ]
    [∀ x, IsProbabilityMeasure (κ x)] (E : Set Y) (hE : MeasurableSet E) :
    (finiteDataRandomOutputLaw μ κ).real (Set.univ ×ˢ E) =
      ∑ x, μ.real {x} * (κ x).real E := by
  rw [measureReal_def, finiteDataRandomOutputLaw_event μ κ E hE,
    ENNReal.toReal_sum]
  · simp [measureReal_def, ENNReal.toReal_mul]
  · intro x _
    exact ENNReal.mul_ne_top (measure_ne_top μ _) (measure_ne_top (κ x) _)

/-- One common output kernel commutes with actual uniform model mixing, for
every measurable output event. -/
theorem finiteDataRandomOutputLaw_mix_event {ι X Y : Type*} [Fintype ι] [Nonempty ι]
    [Fintype X] [MeasurableSpace X] [MeasurableSingletonClass X] [MeasurableSpace Y]
    (P : ι → Measure X) (mix : Measure X) (κ : X → Measure Y)
    [∀ i, IsProbabilityMeasure (P i)] [IsProbabilityMeasure mix]
    [∀ x, IsProbabilityMeasure (κ x)]
    (hmix : ∀ s : Set X, mix.real s = (∑ i, (P i).real s) / Fintype.card ι)
    (E : Set Y) (hE : MeasurableSet E) :
    (finiteDataRandomOutputLaw mix κ).real (Set.univ ×ˢ E) =
      (∑ i, (finiteDataRandomOutputLaw (P i) κ).real (Set.univ ×ˢ E)) / Fintype.card ι := by
  classical
  rw [finiteDataRandomOutputLaw_real_event mix κ E hE]
  simp_rw [finiteDataRandomOutputLaw_real_event _ κ E hE, hmix]
  simp only [Finset.sum_div, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro i _
  ring

end StatisticalRL.GenerativeLowerBound

namespace StatisticalRL.GenerativeLowerBound

/-- A common arbitrary-output randomized estimator has one fixed model of
risk at least 1/4 after both estimator and alternative averaging. -/
theorem finiteRandomOutput_mixture_risk_selection {ι X Y : Type*}
    [Fintype ι] [Nonempty ι] [Fintype X] [MeasurableSpace X] [MeasurableSingletonClass X]
    [NormedAddCommGroup Y] [MeasurableSpace Y]
    (μ₀ : Measure X) (P : ι → Measure X) (mix : Measure X) (κ : X → Measure Y)
    [IsProbabilityMeasure μ₀] [∀ i, IsProbabilityMeasure (P i)] [IsProbabilityMeasure mix]
    [∀ x, IsProbabilityMeasure (κ x)]
    (hmix : ∀ s : Set X, mix.real s = (∑ i, (P i).real s) / Fintype.card ι)
    (hover : (1 : ℝ) / 2 ≤ finiteOverlap μ₀ mix)
    (v₀ : Y) (v : ι → Y) (ε : ℝ)
    (hE : MeasurableSet {y : Y | ε < ‖y - v₀‖})
    (hsep : ∀ i, 2 * ε < ‖v i - v₀‖) :
    (1 : ℝ) / 4 ≤ (finiteDataRandomOutputLaw μ₀ κ).real
        (Set.univ ×ˢ {y | ε < ‖y - v₀‖}) ∨
      ∃ i, (1 : ℝ) / 4 ≤ (finiteDataRandomOutputLaw (P i) κ).real
        (Set.univ ×ˢ {y | ε < ‖y - v i‖}) := by
  classical
  let E : Set Y := {y | ε < ‖y - v₀‖}
  let test := outputEventBinaryKernel κ E
  have ht := finiteBinaryKernel_overlap_le_error_sum μ₀ mix test
  have hsTrue : {z : X × Bool | z.2 = true} = Set.univ ×ˢ {true} := by ext z; simp
  have hsFalse : {z : X × Bool | z.2 = false} = Set.univ ×ˢ {false} := by ext z; simp
  have htrue : (finiteKernelJointLaw μ₀ test).real {z | z.2 = true} =
      (finiteDataRandomOutputLaw μ₀ κ).real (Set.univ ×ˢ E) := by
    rw [hsTrue]
    change (outputEventBinaryJointLaw μ₀ κ E).real (Set.univ ×ˢ {true}) = _
    simp only [measureReal_def, finiteDataRandomOutputLaw_binary_true μ₀ κ E hE]
  have hfalse : (finiteKernelJointLaw mix test).real {z | z.2 = false} =
      (∑ i, (finiteDataRandomOutputLaw (P i) κ).real (Set.univ ×ˢ Eᶜ)) / Fintype.card ι := by
    rw [hsFalse]
    change (outputEventBinaryJointLaw mix κ E).real (Set.univ ×ˢ {false}) = _
    rw [show (outputEventBinaryJointLaw mix κ E).real (Set.univ ×ˢ {false}) =
      (finiteDataRandomOutputLaw mix κ).real (Set.univ ×ˢ Eᶜ) by
        simp only [measureReal_def, outputEventBinaryJointLaw_false mix κ E hE]]
    exact finiteDataRandomOutputLaw_mix_event P mix κ hmix Eᶜ hE.compl
  have hle (i : ι) : (finiteDataRandomOutputLaw (P i) κ).real (Set.univ ×ˢ Eᶜ) ≤
      (finiteDataRandomOutputLaw (P i) κ).real (Set.univ ×ˢ {y | ε < ‖y - v i‖}) := by
    have h := randomOutput_binary_false_le_risk (P i) κ v₀ (v i) ε (hsep i) hE
    simpa only [E, measureReal_def, outputEventBinaryJointLaw_false (P i) κ E hE] using h
  have havg : (finiteKernelJointLaw mix test).real {z | z.2 = false} ≤
      (∑ i, (finiteDataRandomOutputLaw (P i) κ).real (Set.univ ×ˢ {y | ε < ‖y - v i‖})) /
        Fintype.card ι := by
    rw [hfalse]
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact Finset.sum_le_sum (fun i _ ↦ hle i)
  by_cases hb : (1 : ℝ) / 4 ≤ (finiteDataRandomOutputLaw μ₀ κ).real (Set.univ ×ˢ E)
  · exact Or.inl hb
  · right
    have ha : (1 : ℝ) / 4 ≤
        (∑ i, (finiteDataRandomOutputLaw (P i) κ).real (Set.univ ×ˢ {y | ε < ‖y - v i‖})) /
          Fintype.card ι := by rw [htrue] at ht; linarith
    by_contra hn
    push_neg at hn
    have hk : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
    have hs : (∑ i, (finiteDataRandomOutputLaw (P i) κ).real (Set.univ ×ˢ {y | ε < ‖y - v i‖})) <
        ∑ _i : ι, (1 : ℝ) / 4 :=
      Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun i _ ↦ hn i)
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hs
    have hh := (le_div_iff₀ hk).1 ha
    linarith

end StatisticalRL.GenerativeLowerBound
