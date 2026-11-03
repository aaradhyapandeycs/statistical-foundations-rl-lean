import Formalization.Probability.EmpiricalHoeffding
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Measure.Real

/-!
# Simultaneous empirical-row bounds for a fixed finite family

A deterministic family is independent of the sample law. This module applies
the fixed-vector Hoeffding estimate to that family and handles zero vectors.
Source: arXiv:2610.41903v1, preliminary Lemma `lem:Hoeffding-prelim`.
-/

open scoped BigOperators
open MeasureTheory

namespace StatisticalRL.FiniteDistribution

variable {State : Type*} [Fintype State]
local instance hoeffdingFamilyStateMeasurable : MeasurableSpace State := ⊤

/-- The logarithmic radius for a given vector in a finite family. -/
noncomputable def familyRadius (N k : ℕ) (δ : ℝ) (V : State → ℝ) : ℝ :=
  ‖V‖ * Real.sqrt (Real.log (2 * k / δ) / (2 * N))

/-- The radius has exactly the square-root form used in the source. -/
theorem familyRadius_eq_source (N k : ℕ) (δ : ℝ) (V : State → ℝ) :
    familyRadius N k δ V =
      Real.sqrt (‖V‖ ^ 2 * Real.log (2 * k / δ) / (2 * N)) := by
  unfold familyRadius
  have h : ‖V‖ ^ 2 * Real.log (2 * k / δ) / (2 * N) =
      ‖V‖ ^ 2 * (Real.log (2 * k / δ) / (2 * N)) := by ring
  rw [h, Real.sqrt_mul (sq_nonneg ‖V‖), Real.sqrt_sq (norm_nonneg _)]

/-- A given vector violates its simultaneous family radius. -/
noncomputable def familyViolation (d : FiniteDistribution State) (N : ℕ) (hN : 0 < N)
    (k : ℕ) (δ : ℝ) (V : State → ℝ) : Set (Fin N → State) :=
  {ω | familyRadius N k δ V < |(empiricalRow N hN ω).expectation V - d.expectation V|}

theorem familyRadius_nonneg (N k : ℕ) (δ : ℝ) (V : State → ℝ) :
    0 ≤ familyRadius N k δ V := mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)

/-- For a positive family size, each fixed vector violates its radius with
probability at most δ divided by that size. -/
theorem familyViolation_le (d : FiniteDistribution State) (N k : ℕ) (hN : 0 < N)
    (hk : 0 < k) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1)
    (V : State → ℝ) (hV : ∀ s, 0 ≤ V s) :
    (d.sampleMeasure N).real (d.familyViolation N hN k δ V) ≤ δ / k := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hkr : (0 : ℝ) < k := by exact_mod_cast hk
  have hx : 1 < 2 * (k : ℝ) / δ := by
    apply (lt_div_iff₀ hδ).2
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
    nlinarith
  have hl : 0 < Real.log (2 * (k : ℝ) / δ) := Real.log_pos hx
  by_cases hz : ‖V‖ = 0
  · have hbad : d.familyViolation N hN k δ V = ∅ := by
      ext ω
      simp only [familyViolation, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      rw [d.empiricalRow_norm_zero_deviation V N hN hz ω, abs_zero]
      exact not_lt_of_ge (familyRadius_nonneg N k δ V)
    rw [hbad, measureReal_empty]
    exact div_nonneg hδ.le hkr.le
  · have hv : 0 < ‖V‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    have ht := d.empiricalRow_hoeffding_norm V N hN (familyRadius N k δ V)
      (familyRadius_nonneg N k δ V) hV hv
    have hset : d.familyViolation N hN k δ V ⊆
        {ω | familyRadius N k δ V ≤ |(empiricalRow N hN ω).expectation V - d.expectation V|} :=
      by
        intro ω h
        change familyRadius N k δ V < |(empiricalRow N hN ω).expectation V - d.expectation V| at h
        exact le_of_lt h
    calc
      (d.sampleMeasure N).real (d.familyViolation N hN k δ V) ≤
          (d.sampleMeasure N).real
            {ω | familyRadius N k δ V ≤ |(empiricalRow N hN ω).expectation V - d.expectation V|} :=
        measureReal_mono hset (measure_ne_top _ _)
      _ ≤ 2 * Real.exp (-2 * (N : ℝ) * (familyRadius N k δ V) ^ 2 / ‖V‖ ^ 2) := ht
      _ = δ / k := by
        have hsq : 0 ≤ Real.log (2 * (k : ℝ) / δ) / (2 * N) :=
          div_nonneg hl.le (by positivity)
        have hvne : ‖V‖ ≠ 0 := ne_of_gt hv
        have hnne : (N : ℝ) ≠ 0 := ne_of_gt hn
        have harg : 0 < 2 * (k : ℝ) / δ := by positivity
        have he : -2 * (N : ℝ) * (familyRadius N k δ V) ^ 2 / ‖V‖ ^ 2 =
            -Real.log (2 * (k : ℝ) / δ) := by
          unfold familyRadius
          rw [mul_pow, Real.sq_sqrt hsq]
          field_simp
        rw [he, Real.exp_neg, Real.exp_log harg]
        field_simp

/-- A deterministic nonempty finite family has failure probability at most δ. -/
theorem empiricalRow_family_failure_le (d : FiniteDistribution State)
    (N : ℕ) (hN : 0 < N) (family : Finset (State → ℝ)) (hne : family.Nonempty)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hV : ∀ V ∈ family, ∀ s, 0 ≤ V s) :
    (d.sampleMeasure N).real (⋃ V ∈ family, d.familyViolation N hN family.card δ V) ≤ δ := by
  classical
  have hk : 0 < family.card := Finset.card_pos.mpr hne
  have hkr : (0 : ℝ) < family.card := by exact_mod_cast hk
  calc
    (d.sampleMeasure N).real (⋃ V ∈ family, d.familyViolation N hN family.card δ V) ≤
        ∑ V ∈ family, (d.sampleMeasure N).real (d.familyViolation N hN family.card δ V) :=
      measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _V ∈ family, δ / family.card := Finset.sum_le_sum (fun V h ↦
      d.familyViolation_le N family.card hN hk δ hδ hδ1 V (hV V h))
    _ = δ := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      field_simp

/-- The fixed-family simultaneous source-radius event has probability at least
`1 − δ`, including all zero vectors. -/
theorem empiricalRow_family_success_ge (d : FiniteDistribution State)
    (N : ℕ) (hN : 0 < N) (family : Finset (State → ℝ)) (hne : family.Nonempty)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hV : ∀ V ∈ family, ∀ s, 0 ≤ V s) :
    1 - δ ≤ (d.sampleMeasure N).real
      {ω | ∀ V ∈ family,
        |(empiricalRow N hN ω).expectation V - d.expectation V| ≤
          Real.sqrt (‖V‖ ^ 2 * Real.log (2 * family.card / δ) / (2 * N))} := by
  classical
  let bad : Set (Fin N → State) := ⋃ V ∈ family, d.familyViolation N hN family.card δ V
  have hb : (d.sampleMeasure N).real bad ≤ δ :=
    d.empiricalRow_family_failure_le N hN family hne δ hδ hδ1 hV
  have hm : MeasurableSet bad := (Set.to_countable bad).measurableSet
  have heq : badᶜ = {ω | ∀ V ∈ family,
      |(empiricalRow N hN ω).expectation V - d.expectation V| ≤
        Real.sqrt (‖V‖ ^ 2 * Real.log (2 * family.card / δ) / (2 * N))} := by
    ext ω
    simp [bad, familyViolation, familyRadius_eq_source, not_lt]
  have hc := measureReal_compl (μ := d.sampleMeasure N) hm
  rw [heq, probReal_univ] at hc
  exact (sub_le_sub_left hb 1).trans_eq hc.symm

/-- With a finite sample space, a strict violation has a positive gap from the
radius, so the fixed-vector violation probability is strictly below δ/k. -/
theorem familyViolation_lt (d : FiniteDistribution State) (N k : ℕ) (hN : 0 < N)
    (hk : 0 < k) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1)
    (V : State → ℝ) (hV : ∀ s, 0 ≤ V s) :
    (d.sampleMeasure N).real (d.familyViolation N hN k δ V) < δ / k := by
  classical
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hkr : (0 : ℝ) < k := by exact_mod_cast hk
  have hdelta : 0 < δ / k := div_pos hδ hkr
  by_cases hnon : (d.familyViolation N hN k δ V).Nonempty
  · have hv : 0 < ‖V‖ := by
      by_contra h
      have hz : ‖V‖ = 0 := le_antisymm (not_lt.mp h) (norm_nonneg _)
      obtain ⟨ω, hw⟩ := hnon
      change familyRadius N k δ V <
        |(empiricalRow N hN ω).expectation V - d.expectation V| at hw
      rw [d.empiricalRow_norm_zero_deviation V N hN hz ω, abs_zero] at hw
      exact (not_lt_of_ge (familyRadius_nonneg N k δ V)) hw
    let hits : Finset (Fin N → State) := Finset.univ.filter
      (fun ω ↦ ω ∈ d.familyViolation N hN k δ V)
    have hhits : hits.Nonempty := by
      obtain ⟨ω, hw⟩ := hnon
      exact ⟨ω, by simp [hits, hw]⟩
    let deviation : (Fin N → State) → ℝ := fun ω ↦
      |(empiricalRow N hN ω).expectation V - d.expectation V|
    let m : ℝ := hits.inf' hhits deviation
    have hgap : familyRadius N k δ V < m := by
      apply (Finset.lt_inf'_iff hhits).2
      intro ω hω
      have hw := (Finset.mem_filter.mp hω).2
      exact hw
    have hmpos : 0 ≤ m := (familyRadius_nonneg N k δ V).trans hgap.le
    have hset : d.familyViolation N hN k δ V ⊆ {ω | m ≤ deviation ω} := by
      intro ω hw
      have hω : ω ∈ hits := by simp [hits, hw]
      exact Finset.inf'_le deviation hω
    have ht := d.empiricalRow_hoeffding_norm V N hN m hmpos hV hv
    have hx : 1 < 2 * (k : ℝ) / δ := by
      apply (lt_div_iff₀ hδ).2
      have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
      nlinarith
    have hl : 0 < Real.log (2 * (k : ℝ) / δ) := Real.log_pos hx
    have hsq : 0 ≤ Real.log (2 * (k : ℝ) / δ) / (2 * N) :=
      div_nonneg hl.le (by positivity)
    have hvne : ‖V‖ ≠ 0 := ne_of_gt hv
    have hnne : (N : ℝ) ≠ 0 := ne_of_gt hn
    have harg : 0 < 2 * (k : ℝ) / δ := by positivity
    have he : -2 * (N : ℝ) * (familyRadius N k δ V) ^ 2 / ‖V‖ ^ 2 =
        -Real.log (2 * (k : ℝ) / δ) := by
      unfold familyRadius
      rw [mul_pow, Real.sq_sqrt hsq]
      field_simp
    have hsqgap : (familyRadius N k δ V) ^ 2 < m ^ 2 := by
      nlinarith [familyRadius_nonneg N k δ V]
    have hexp : -2 * (N : ℝ) * m ^ 2 / ‖V‖ ^ 2 <
        -2 * (N : ℝ) * (familyRadius N k δ V) ^ 2 / ‖V‖ ^ 2 := by
      apply (div_lt_div_iff_of_pos_right (sq_pos_of_pos hv)).2
      nlinarith
    calc
      (d.sampleMeasure N).real (d.familyViolation N hN k δ V) ≤
          (d.sampleMeasure N).real {ω | m ≤ deviation ω} :=
        measureReal_mono hset (measure_ne_top _ _)
      _ ≤ 2 * Real.exp (-2 * (N : ℝ) * m ^ 2 / ‖V‖ ^ 2) := ht
      _ < 2 * Real.exp (-2 * (N : ℝ) * (familyRadius N k δ V) ^ 2 / ‖V‖ ^ 2) := by
        exact mul_lt_mul_of_pos_left (Real.exp_lt_exp.mpr hexp) (by norm_num)
      _ = δ / k := by
        rw [he, Real.exp_neg, Real.exp_log harg]
        field_simp
  · have hempty : d.familyViolation N hN k δ V = ∅ := Set.not_nonempty_iff_eq_empty.mp hnon
    rw [hempty, measureReal_empty]
    exact hdelta

/-- For a fixed nonempty finite deterministic family, the source-radius event
has probability strictly greater than `1 − δ`. -/
theorem empiricalRow_family_success_gt (d : FiniteDistribution State)
    (N : ℕ) (hN : 0 < N) (family : Finset (State → ℝ)) (hne : family.Nonempty)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hV : ∀ V ∈ family, ∀ s, 0 ≤ V s) :
    1 - δ < (d.sampleMeasure N).real
      {ω | ∀ V ∈ family,
        |(empiricalRow N hN ω).expectation V - d.expectation V| ≤
          Real.sqrt (‖V‖ ^ 2 * Real.log (2 * family.card / δ) / (2 * N))} := by
  classical
  let bad : Set (Fin N → State) := ⋃ V ∈ family, d.familyViolation N hN family.card δ V
  have hk : 0 < family.card := Finset.card_pos.mpr hne
  have hkr : (0 : ℝ) < family.card := by exact_mod_cast hk
  have hb : (d.sampleMeasure N).real bad < δ := by
    calc
      (d.sampleMeasure N).real bad ≤
          ∑ V ∈ family, (d.sampleMeasure N).real (d.familyViolation N hN family.card δ V) :=
        measureReal_biUnion_finset_le _ _
      _ < ∑ _V ∈ family, δ / family.card :=
        Finset.sum_lt_sum_of_nonempty hne (fun V h ↦
          d.familyViolation_lt N family.card hN hk δ hδ hδ1 V (hV V h))
      _ = δ := by
        simp only [Finset.sum_const, nsmul_eq_mul]
        field_simp
  have hm : MeasurableSet bad := (Set.to_countable bad).measurableSet
  have heq : badᶜ = {ω | ∀ V ∈ family,
      |(empiricalRow N hN ω).expectation V - d.expectation V| ≤
        Real.sqrt (‖V‖ ^ 2 * Real.log (2 * family.card / δ) / (2 * N))} := by
    ext ω
    simp [bad, familyViolation, familyRadius_eq_source, not_lt]
  have hc := measureReal_compl (μ := d.sampleMeasure N) hm
  rw [heq, probReal_univ] at hc
  exact (sub_lt_sub_left hb 1).trans_eq hc.symm

/-- An empty deterministic family satisfies the simultaneous condition
vacuously with probability one. -/
theorem empiricalRow_empty_family_success (d : FiniteDistribution State)
    (N : ℕ) (hN : 0 < N) (δ : ℝ) :
    (d.sampleMeasure N).real
      {ω | ∀ V ∈ (∅ : Finset (State → ℝ)),
        |(empiricalRow N hN ω).expectation V - d.expectation V| ≤
          Real.sqrt (‖V‖ ^ 2 * Real.log (2 * (0 : ℕ) / δ) / (2 * N))} = 1 := by
  simp [probReal_univ]

end StatisticalRL.FiniteDistribution
