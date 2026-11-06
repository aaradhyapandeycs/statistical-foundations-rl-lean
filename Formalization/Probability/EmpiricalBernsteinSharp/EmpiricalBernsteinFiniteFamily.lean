import Formalization.Probability.EmpiricalBernsteinSharp.EmpiricalBernsteinSharpFixedVector
import Formalization.Probability.EmpiricalBernsteinSharp.EmpiricalBernsteinFamilyMeasurable

/-! Private uncompiled fixed-family union for the literal 7/3 radius. -/
open scoped BigOperators
open MeasureTheory
namespace StatisticalRL.FiniteDistribution

variable {State : Type*} [Fintype State]
local instance empiricalBernsteinFamilyStateMeasurable : MeasurableSpace State := ⊤

theorem empiricalBernstein_fixedFamily_success_gt (d : FiniteDistribution State)
    (N : ℕ) (hN2 : 2 ≤ N) (family : Finset (State → ℝ))
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hV : ∀ V ∈ family, ∀ s, 0 ≤ V s) :
    let hN : 0 < N := by omega
    1-δ < (d.sampleMeasure N).real {ω | ∀ V ∈ family,
      |(empiricalRow N hN ω).expectation V-d.expectation V| ≤
        empiricalBernsteinFamilyRadius (empiricalRow N hN ω) N family.card δ V} := by
  classical
  let hN : 0 < N := by omega
  by_cases hne : family.Nonempty
  · let k := family.card
    let t : ℝ := Real.log (4*(k : ℝ)/δ)
    have hk : 0 < k := Finset.card_pos.mpr hne
    have hkr : (0 : ℝ) < k := by exact_mod_cast hk
    have hx : 1 < 4*(k : ℝ)/δ := by
      apply (lt_div_iff₀ hδ).2
      have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
      nlinarith
    have ht : 0 < t := Real.log_pos hx
    let bad : Set (Fin N → State) := ⋃ V ∈ family, {ω |
      empiricalBernsteinFamilyRadius (empiricalRow N hN ω) N k δ V <
        |(empiricalRow N hN ω).expectation V-d.expectation V|}
    have hone (V : State → ℝ) (hmem : V ∈ family) :
        (d.sampleMeasure N).real {ω |
          empiricalBernsteinFamilyRadius (empiricalRow N hN ω) N k δ V <
            |(empiricalRow N hN ω).expectation V-d.expectation V|} ≤
          3*δ/(4*k) := by
      have hupper (s : State) : V s ∈ Set.Icc 0 ‖V‖ := by
        refine ⟨hV V hmem s, ?_⟩
        exact (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using norm_le_pi_norm V s)
      have h := d.empiricalRow_empiricalBernstein_fixed_failure N hN2 V ‖V‖ t
        (norm_nonneg _) ht hupper
      change (d.sampleMeasure N).real {ω |
        empiricalBernsteinFamilyRadius (empiricalRow N hN ω) N k δ V <
          |(empiricalRow N hN ω).expectation V-d.expectation V|} ≤ 3*Real.exp (-t) at h
      calc
        _ ≤ 3*Real.exp (-t) := h
        _ = 3*δ/(4*k) := by
          dsimp [t]
          rw [Real.exp_neg, Real.exp_log (by positivity : 0 < 4*(k : ℝ)/δ)]
          field_simp
    have hb : (d.sampleMeasure N).real bad ≤ 3*δ/4 := by
      calc
        _ ≤ ∑ V ∈ family, (d.sampleMeasure N).real {ω |
          empiricalBernsteinFamilyRadius (empiricalRow N hN ω) N k δ V <
            |(empiricalRow N hN ω).expectation V-d.expectation V|} := measureReal_biUnion_finset_le _ _
        _ ≤ ∑ _V ∈ family, 3*δ/(4*k) := Finset.sum_le_sum (fun V hV ↦ hone V hV)
        _ = 3*δ/4 := by
          simp only [Finset.sum_const, nsmul_eq_mul]
          dsimp [k]
          field_simp
    have hm : MeasurableSet bad := (Set.to_countable bad).measurableSet
    have heq : badᶜ = {ω | ∀ V ∈ family,
        |(empiricalRow N hN ω).expectation V-d.expectation V| ≤
          empiricalBernsteinFamilyRadius (empiricalRow N hN ω) N family.card δ V} := by
      ext ω
      simp [bad, k, not_lt]
    have hc := measureReal_compl (μ := d.sampleMeasure N) hm
    rw [heq, probReal_univ] at hc
    linarith
  · have hzero : family = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    subst family
    simp [probReal_univ, hδ]

end StatisticalRL.FiniteDistribution
