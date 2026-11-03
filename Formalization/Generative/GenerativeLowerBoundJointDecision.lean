import Formalization.Generative.GenerativeLowerBoundJointKL
import Formalization.Generative.GenerativeLowerBoundBinaryDecision

/-! Common-decoder probabilities for actual finite joint experiments. -/
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators
namespace StatisticalRL.GenerativeLowerBound
section
variable {I Ω : Type*} [Fintype I] [Nonempty I] [Fintype Ω]
  [MeasurableSpace I] [MeasurableSingletonClass I]
  [MeasurableSpace Ω] [MeasurableSingletonClass Ω]

/-- Uniform-prior joint success probability equals the average individual
success probability for one common decoder. -/
theorem finiteJointLaw_success (P : I → Measure Ω) [∀ i, IsProbabilityMeasure (P i)]
    (d : Ω → I) :
    (finiteJointLaw P).real {z | d z.2 = z.1} =
      (∑ i, (P i).real {x | d x = i}) / Fintype.card I := by
  classical
  let s : Finset (I × Ω) := Finset.univ.filter (fun z ↦ d z.2 = z.1)
  have hs : (s : Set (I × Ω)) = {z | d z.2 = z.1} := by ext z; simp [s]
  rw [← hs, ← sum_measureReal_singleton]
  dsimp [s]
  rw [Finset.sum_filter, Fintype.sum_prod_type, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  simp only [measureReal_def, finiteJointLaw_singleton, ENNReal.toReal_mul,
    ENNReal.toReal_inv, ENNReal.toReal_natCast]
  rw [← Finset.sum_filter]
  have hset : ((Finset.univ.filter (fun x ↦ d x = i) : Finset Ω) : Set Ω) =
      {x | d x = i} := by ext x; simp
  rw [← hset]
  change (∑ x ∈ Finset.univ.filter (fun x ↦ d x = i),
    (Fintype.card I : ℝ)⁻¹ * (P i).real {x}) =
      (P i).real (↑(Finset.univ.filter (fun x ↦ d x = i)) : Set Ω) / _
  rw [← sum_measureReal_singleton]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro x _
  ring

end
end StatisticalRL.GenerativeLowerBound

namespace StatisticalRL.GenerativeLowerBound

/-- Actual finite-law binary decision inequality, including constant tests. -/
theorem finite_binary_decision_kl {Ω : Type*} [Fintype Ω]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω] (μ ν : Measure Ω)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : ∀ x, μ {x} ≠ 0) (hν : ∀ x, ν {x} ≠ 0)
    (test : Ω → Bool) (hq : 0 < ν.real {x | test x = true})
    (hq1 : ν.real {x | test x = true} < 1) :
    μ.real {x | test x = true} * Real.log (1 / ν.real {x | test x = true}) - Real.log 2 ≤
      (InformationTheory.klDiv μ ν).toReal := by
  classical
  let u := μ.map test
  let v := ν.map test
  have ht : 0 ≤ μ.real {x | test x = true} := measureReal_nonneg
  have ht1 : μ.real {x | test x = true} ≤ 1 := by
    have hh := measureReal_nonneg (μ := μ) (s := {x | test x = true}ᶜ)
    rw [probReal_compl_eq_one_sub (Set.to_countable _).measurableSet] at hh
    linarith
  have hd := finite_klDiv_map_le μ ν hμ hν test
  letI : IsProbabilityMeasure u := Measure.isProbabilityMeasure_map (measurable_of_countable test).aemeasurable
  letI : IsProbabilityMeasure v := Measure.isProbabilityMeasure_map (measurable_of_countable test).aemeasurable
  have hac : u ≪ v := by
    intro s hs
    rw [Measure.map_apply (measurable_of_countable test) (Set.to_countable s).measurableSet] at hs ⊢
    exact finite_fullSupport_ac μ ν hν hs
  have hm (ρ : Measure Ω) [IsProbabilityMeasure ρ] :
      (ρ.map test).real {true} = ρ.real {x | test x = true} := by
    rw [measureReal_def, Measure.map_apply (measurable_of_countable test) (measurableSet_singleton _)]
    rfl
  have hmf (ρ : Measure Bool) [IsProbabilityMeasure ρ] : ρ.real {false} = 1 - ρ.real {true} := by
    have hc := probReal_compl_eq_one_sub (μ := ρ) (measurableSet_singleton true)
    simpa using hc
  rw [finite_klDiv_eq_expression_of_ac u v hac] at hd
  unfold finiteKLExpression at hd
  simp only [Fintype.sum_bool] at hd
  rw [hmf u, hmf v] at hd
  change _ ≤ (InformationTheory.klDiv μ ν).toReal at hd
  rw [hm μ, hm ν] at hd
  have hb := binary_relative_entropy_lower _ _ ht ht1 hq hq1
  linarith

end StatisticalRL.GenerativeLowerBound

namespace StatisticalRL.GenerativeLowerBound
section
variable {I Ω : Type*} [Fintype I] [Nonempty I] [Fintype Ω]
  [MeasurableSpace I] [MeasurableSingletonClass I]
  [MeasurableSpace Ω] [MeasurableSingletonClass Ω]

/-- Actual common-decoder Fano success inequality with exact cardinality K. -/
theorem finite_joint_decoding_success_bound (P : I → Measure Ω)
    [∀ i, IsProbabilityMeasure (P i)] (Q : Measure Ω) [IsProbabilityMeasure Q]
    (hP : ∀ i x, P i {x} ≠ 0) (hQ : ∀ x, Q {x} ≠ 0)
    (hK : 2 ≤ Fintype.card I) (d : Ω → I) :
    ((∑ i, (P i).real {x | d x = i}) / Fintype.card I) * Real.log (Fintype.card I) ≤
      (∑ i, (InformationTheory.klDiv (P i) Q).toReal) / Fintype.card I + Real.log 2 := by
  classical
  let J := finiteJointLaw P
  let R := finiteBaselineJointLaw (I := I) Q
  let f : I × Ω → Bool := fun z ↦ decide (d z.2 = z.1)
  have hJ : ∀ z, J {z} ≠ 0 := finiteJointLaw_atom_ne_zero P hP
  have hR : ∀ z, R {z} ≠ 0 := finiteJointLaw_atom_ne_zero (fun _ ↦ Q) (fun _ x ↦ hQ x)
  have hk : (1 : ℝ) < Fintype.card I := by exact_mod_cast hK
  have hbase : R.real {z | f z = true} = (Fintype.card I : ℝ)⁻¹ := by
    simpa [R, f] using finiteBaselineJointLaw_success Q d
  have hj : J.real {z | f z = true} = (∑ i, (P i).real {x | d x = i}) / Fintype.card I := by
    simpa [J, f] using finiteJointLaw_success P d
  have hb := finite_binary_decision_kl J R hJ hR f
    (by rw [hbase]; positivity) (by rw [hbase]; exact (inv_lt_one₀ (by linarith)).mpr hk)
  rw [hbase, hj] at hb
  have hlog : Real.log (1 / (Fintype.card I : ℝ)⁻¹) = Real.log (Fintype.card I) := by
    simp
  rw [hlog, finiteJointLaw_klDiv_eq_mean P Q hQ] at hb
  linarith

/-- Actual mean decoder error is bounded below by the Fano expression. -/
theorem finite_joint_decoding_error_bound (P : I → Measure Ω)
    [∀ i, IsProbabilityMeasure (P i)] (Q : Measure Ω) [IsProbabilityMeasure Q]
    (hP : ∀ i x, P i {x} ≠ 0) (hQ : ∀ x, Q {x} ≠ 0)
    (hK : 2 ≤ Fintype.card I) (d : Ω → I) :
    1 - (((∑ i, (InformationTheory.klDiv (P i) Q).toReal) / Fintype.card I + Real.log 2) /
      Real.log (Fintype.card I)) ≤
      (∑ i, (P i).real {x | d x ≠ i}) / Fintype.card I := by
  classical
  have hk : (1 : ℝ) < Fintype.card I := by exact_mod_cast hK
  have hlog : 0 < Real.log (Fintype.card I) := Real.log_pos hk
  have hc : (Fintype.card I : ℝ) ≠ 0 := by linarith
  have hcomp (i : I) : (P i).real {x | d x ≠ i} = 1 - (P i).real {x | d x = i} := by
    have hh := probReal_compl_eq_one_sub (μ := P i)
      ((Set.to_countable {x | d x = i}).measurableSet)
    simpa using hh
  have hsum : (∑ i, (P i).real {x | d x ≠ i}) / Fintype.card I =
      1 - (∑ i, (P i).real {x | d x = i}) / Fintype.card I := by
    simp_rw [hcomp]
    simp [Finset.sum_sub_distrib, Finset.sum_const, hc, sub_div]
  rw [hsum]
  have h := finite_joint_decoding_success_bound P Q hP hQ hK d
  have hdiv := (le_div_iff₀ hlog).mpr h
  linarith

end
end StatisticalRL.GenerativeLowerBound
