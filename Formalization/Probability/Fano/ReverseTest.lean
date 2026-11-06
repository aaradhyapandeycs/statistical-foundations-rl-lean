import Formalization.Probability.Fano.ReverseTestDefinitions
import Formalization.Probability.Fano.BernoulliPinskerLaw
import Formalization.Probability.Fano.FinitePartitionKL

/-! Canonical Chapter 2 Fano testing foundations. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace StatisticalRL.PrelimFano

theorem measurable_eventIndicatorBool {Ω : Type*} [MeasurableSpace Ω] {A : Set Ω}
    (hA : MeasurableSet A) : Measurable (eventIndicatorBool A) := by
  classical
  refine measurable_to_countable' fun b => ?_
  cases b
  · have : eventIndicatorBool A ⁻¹' {false} = Aᶜ := by
      ext ω; simp [eventIndicatorBool]
    rw [this]; exact hA.compl
  · have : eventIndicatorBool A ⁻¹' {true} = A := by
      ext ω; simp [eventIndicatorBool]
    rw [this]; exact hA

theorem eventParam_le_one {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (A : Set Ω) : eventParam P A ≤ 1 := by
  unfold eventParam
  have h : P A ≤ 1 := prob_le_one
  simpa using ENNReal.toNNReal_mono ENNReal.one_ne_top h

theorem eventParam_coe {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (A : Set Ω) : ((eventParam P A : ℝ≥0) : ℝ) = P.real A := by
  unfold eventParam
  rw [ENNReal.coe_toNNReal_eq_toReal]
  rfl

/-- The law of the indicator of a measurable event is the actual Bernoulli law
with parameter the event's probability. -/
theorem map_eventIndicatorBool {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {A : Set Ω} (hA : MeasurableSet A) :
    P.map (eventIndicatorBool A) =
      (PMF.bernoulli (eventParam P A) (eventParam_le_one P A)).toMeasure := by
  classical
  have hm := measurable_eventIndicatorBool hA
  have hfin : P A ≠ ∞ := measure_ne_top P A
  rw [Measure.ext_iff_singleton]
  intro b
  rw [Measure.map_apply hm (measurableSet_singleton b),
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton b), PMF.bernoulli_apply]
  cases b
  · have : eventIndicatorBool A ⁻¹' {false} = Aᶜ := by
      ext ω; simp [eventIndicatorBool]
    rw [this, prob_compl_eq_one_sub hA]
    simp only [cond_false]
    rw [ENNReal.coe_sub, ENNReal.coe_one]
    unfold eventParam
    rw [ENNReal.coe_toNNReal hfin]
  · have : eventIndicatorBool A ⁻¹' {true} = A := by
      ext ω; simp [eventIndicatorBool]
    rw [this]
    simp only [cond_true]
    unfold eventParam
    rw [ENNReal.coe_toNNReal hfin]

/-- Event-level Pinsker inequality for arbitrary probability laws: the squared
probability gap of any measurable event is controlled by the KL divergence. -/
theorem event_sq_gap_le_klDiv {Ω : Type*} [MeasurableSpace Ω] (P Q : Measure Ω)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] {A : Set Ω} (hA : MeasurableSet A) :
    ENNReal.ofReal (2 * (P.real A - Q.real A) ^ 2) ≤ InformationTheory.klDiv P Q := by
  have hm := measurable_eventIndicatorBool hA
  have hdpi := finiteValued_klDiv_map_le P Q (eventIndicatorBool A) hm
  rw [map_eventIndicatorBool P hA, map_eventIndicatorBool Q hA] at hdpi
  have hpin := StatisticalRL.GenerativeLowerBound.bernoulli_klDiv_quadratic_lower
    (eventParam P A) (eventParam Q A) (eventParam_le_one P A) (eventParam_le_one Q A)
  rw [eventParam_coe, eventParam_coe] at hpin
  exact hpin.trans hdpi

/-- Reverse-Fano per-test bound (frozen signature). -/
theorem reverseFano_test_error_lower
    {Ω : Type*} [MeasurableSpace Ω]
    (M : ℕ) (P : Fin (M+1) → Measure Ω)
    [∀ j, IsProbabilityMeasure (P j)]
    (ψ : Ω → Fin (M+1)) (hψ : Measurable ψ)
    (B : ℝ) (hB : 0 ≤ B)
    (hKL : (∑ j : Fin M, InformationTheory.klDiv (P 0) (P j.succ)) ≤
      ENNReal.ofReal B) :
    1 - 1 / ((M : ℝ)+1) -
      Real.sqrt ((M : ℝ) * B / (2 * ((M : ℝ)+1)^2)) ≤
      (1 / ((M : ℝ)+1)) *
        ∑ j : Fin (M+1), (P j).real {ω | ψ ω ≠ j} := by
  classical
  -- Decision cells of the test.
  let A : Fin (M+1) → Set Ω := fun j => ψ ⁻¹' ({j} : Set (Fin (M+1)))
  have hA : ∀ j, MeasurableSet (A j) := fun j => hψ (measurableSet_singleton j)
  -- Per-alternative probability gaps on the alternative's own cell.
  let d : Fin M → ℝ := fun j => (P j.succ).real (A j.succ) - (P 0).real (A j.succ)
  -- Squared gaps are within the KL budget.
  have hgap : ∀ j : Fin M,
      ENNReal.ofReal (2 * d j ^ 2) ≤ InformationTheory.klDiv (P 0) (P j.succ) := by
    intro j
    have h := event_sq_gap_le_klDiv (P 0) (P j.succ) (hA j.succ)
    have hsq : (2 * d j ^ 2) = 2 * ((P 0).real (A j.succ) - (P j.succ).real (A j.succ)) ^ 2 := by
      simp only [d]; ring
    rw [hsq]; exact h
  have hsumsq : ∑ j : Fin M, 2 * d j ^ 2 ≤ B := by
    have h1 : ENNReal.ofReal (∑ j : Fin M, 2 * d j ^ 2) ≤ ENNReal.ofReal B := by
      rw [ENNReal.ofReal_sum_of_nonneg (fun j _ => by positivity)]
      exact (Finset.sum_le_sum fun j _ => hgap j).trans hKL
    exact (ENNReal.ofReal_le_ofReal_iff hB).1 h1
  -- Cauchy–Schwarz: ∑ d ≤ √(M · B / 2).
  have hcs : ∑ j : Fin M, d j ≤ Real.sqrt ((M : ℝ) * B / 2) := by
    have hcs0 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ : Fin M => (1 : ℝ)) d
    simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one] at hcs0
    have hsq : (∑ j : Fin M, d j) ^ 2 ≤ (M : ℝ) * B / 2 := by
      have hM : (0 : ℝ) ≤ M := Nat.cast_nonneg M
      have h2 : ∑ j : Fin M, d j ^ 2 ≤ B / 2 := by
        have : ∑ j : Fin M, 2 * d j ^ 2 = 2 * ∑ j : Fin M, d j ^ 2 := by
          rw [Finset.mul_sum]
        linarith
      calc (∑ j : Fin M, d j) ^ 2 ≤ (M : ℝ) * ∑ j : Fin M, d j ^ 2 := hcs0
        _ ≤ (M : ℝ) * (B / 2) := mul_le_mul_of_nonneg_left h2 hM
        _ = (M : ℝ) * B / 2 := by ring
    exact Real.le_sqrt_of_sq_le hsq
  -- Total success probability.
  have hP0cells : ∑ j : Fin (M+1), (P 0).real (A j) = 1 := by
    have h := sum_measureReal_preimage_singleton (μ := P 0) (Finset.univ : Finset (Fin (M+1)))
      (f := ψ) (fun y _ => hA y)
    simpa [A, probReal_univ] using h
  have hsucc : ∑ j : Fin (M+1), (P j).real (A j) = 1 + ∑ j : Fin M, d j := by
    rw [Fin.sum_univ_succ] at hP0cells ⊢
    simp only [d, Finset.sum_sub_distrib]
    linarith
  -- Errors are complements of successes.
  have herr : ∀ j : Fin (M+1), (P j).real {ω | ψ ω ≠ j} = 1 - (P j).real (A j) := by
    intro j
    have hset : {ω | ψ ω ≠ j} = (A j)ᶜ := by
      ext ω; simp [A]
    rw [hset, probReal_compl_eq_one_sub (hA j)]
  have hsumErr : ∑ j : Fin (M+1), (P j).real {ω | ψ ω ≠ j} =
      ((M : ℝ) + 1) - (1 + ∑ j : Fin M, d j) := by
    simp_rw [herr]
    rw [Finset.sum_sub_distrib, hsucc]
    simp
  -- Final arithmetic.
  have hM1 : (0 : ℝ) < (M : ℝ) + 1 := by positivity
  have hsqrt : Real.sqrt ((M : ℝ) * B / (2 * ((M : ℝ) + 1) ^ 2)) =
      Real.sqrt ((M : ℝ) * B / 2) / ((M : ℝ) + 1) := by
    rw [show (M : ℝ) * B / (2 * ((M : ℝ) + 1) ^ 2) = ((M : ℝ) * B / 2) / ((M : ℝ) + 1) ^ 2 by
      field_simp]
    rw [Real.sqrt_div' _ (by positivity), Real.sqrt_sq hM1.le]
  rw [hsumErr, hsqrt]
  have key : 1 - 1 / ((M : ℝ) + 1) - Real.sqrt ((M : ℝ) * B / 2) / ((M : ℝ) + 1) ≤
      (1 / ((M : ℝ) + 1)) * (((M : ℝ) + 1) - (1 + ∑ j : Fin M, d j)) := by
    have e : (1 / ((M : ℝ) + 1)) * (((M : ℝ) + 1) - (1 + ∑ j : Fin M, d j)) =
        1 - 1 / ((M : ℝ) + 1) - (∑ j : Fin M, d j) / ((M : ℝ) + 1) := by
      field_simp
      ring
    rw [e]
    have : (∑ j : Fin M, d j) / ((M : ℝ) + 1) ≤ Real.sqrt ((M : ℝ) * B / 2) / ((M : ℝ) + 1) :=
      div_le_div_of_nonneg_right hcs hM1.le
    linarith
  exact key


end StatisticalRL.PrelimFano
