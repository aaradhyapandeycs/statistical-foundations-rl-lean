import Formalization.Generative.GenerativeLowerBoundJointLaw

/-! Joint finite experiment KL and common-decoder baseline mass. -/
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators
namespace StatisticalRL.GenerativeLowerBound

section
variable {I Ω : Type*} [Fintype I] [Nonempty I] [Fintype Ω]
  [MeasurableSpace I] [MeasurableSingletonClass I]
  [MeasurableSpace Ω] [MeasurableSingletonClass Ω]

/-- KL of the actual uniform-prior joint experiment against a common baseline
is the mean of the oriented per-hypothesis KLs. -/
theorem finiteJointLaw_klDiv_eq_mean (P : I → Measure Ω)
    [∀ i, IsProbabilityMeasure (P i)] (Q : Measure Ω) [IsProbabilityMeasure Q]
    (hQ : ∀ x, Q {x} ≠ 0) :
    (InformationTheory.klDiv (finiteJointLaw P) (finiteBaselineJointLaw (I := I) Q)).toReal =
      (∑ i, (InformationTheory.klDiv (P i) Q).toReal) / Fintype.card I := by
  classical
  let R := finiteBaselineJointLaw (I := I) Q
  have hR : ∀ z, R {z} ≠ 0 :=
    finiteJointLaw_atom_ne_zero (fun _ ↦ Q) (fun _ x ↦ hQ x)
  have hac : finiteJointLaw P ≪ R := finite_fullSupport_ac _ _ hR
  rw [finite_klDiv_eq_expression_of_ac _ _ hac]
  simp_rw [finite_klDiv_eq_expression_of_ac _ _ (finite_fullSupport_ac _ _ hQ)]
  unfold finiteKLExpression
  rw [Fintype.sum_prod_type]
  have hk : (Fintype.card I : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hatom (i : I) (x : Ω) : (finiteJointLaw P).real {(i,x)} =
      (Fintype.card I : ℝ)⁻¹ * (P i).real {x} := by
    simp [measureReal_def, finiteJointLaw_singleton, ENNReal.toReal_mul]
  have hratom (i : I) (x : Ω) : R.real {(i,x)} =
      (Fintype.card I : ℝ)⁻¹ * Q.real {x} := by
    simp [R, finiteBaselineJointLaw, measureReal_def, finiteJointLaw_singleton, ENNReal.toReal_mul]
  simp_rw [hatom, hratom]
  simp_rw [mul_div_mul_left _ _ (inv_ne_zero hk)]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro x _
  ring

/-- Under a uniform independent hypothesis and common baseline observations,
a common decoder succeeds with probability exactly 1/K. -/
theorem finiteBaselineJointLaw_success (Q : Measure Ω) [IsProbabilityMeasure Q]
    (d : Ω → I) :
    (finiteBaselineJointLaw (I := I) Q).real {z | d z.2 = z.1} =
      (Fintype.card I : ℝ)⁻¹ := by
  classical
  let R := finiteBaselineJointLaw (I := I) Q
  let s : Finset (I × Ω) := Finset.univ.filter (fun z ↦ d z.2 = z.1)
  have hs : (s : Set (I × Ω)) = {z | d z.2 = z.1} := by ext z; simp [s]
  rw [← hs, ← sum_measureReal_singleton]
  dsimp [s]
  rw [Finset.sum_filter, Fintype.sum_prod_type, Finset.sum_comm]
  simp only [measureReal_def, R, finiteBaselineJointLaw, finiteJointLaw_singleton,
    ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [← Finset.mul_sum]
  change (Fintype.card I : ℝ)⁻¹ * (∑ x, Q.real {x}) = _
  rw [sum_measureReal_singleton, Finset.coe_univ, probReal_univ]
  ring

end
end StatisticalRL.GenerativeLowerBound
