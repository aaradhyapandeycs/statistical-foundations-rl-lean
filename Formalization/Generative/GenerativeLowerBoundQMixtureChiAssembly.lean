import Formalization.Generative.GenerativeLowerBoundQMixtureChiIntegral

/-! Finite-mixture variance assembly from independently proved moments. -/
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace StatisticalRL.GenerativeLowerBound

/-- For a finite probability space and finite family of likelihood functions,
the diagonal/cross and first-moment identities imply the exact variance of
their normalized mixture. The moment premises are consumed explicitly; the
Q-mixture application must prove them from its actual product law. -/
theorem finite_mixture_centered_sq_integral {ι Ω : Type*}
    [Fintype ι] [Nonempty ι] [DecidableEq ι] [Fintype Ω]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (L : ι → Ω → ℝ) (d : ℝ)
    (hmean : ∀ i, ∫ x, L i x ∂μ = 1)
    (hpair : ∀ i j, ∫ x, L i x * L j x ∂μ = if i = j then d else 1) :
    ∫ x, ((∑ i, L i x) / Fintype.card ι - 1) ^ 2 ∂μ =
      (d - 1) / Fintype.card ι := by
  classical
  let K : ℝ := Fintype.card ι
  have hK : K ≠ 0 := by
    dsimp [K]
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card ι ≠ 0)
  have hL : ∀ i, Integrable (L i) μ := fun _ ↦ Integrable.of_finite
  have hLL : ∀ i j, Integrable (fun x ↦ L i x * L j x) μ :=
    fun _ _ ↦ Integrable.of_finite
  have hsum : ∫ x, (∑ i, L i x) ∂μ = K := by
    rw [integral_finset_sum _ (fun i _ ↦ hL i)]
    simp [hmean, K]
  have hsq : ∫ x, (∑ i, L i x) ^ 2 ∂μ = K * d + K * (K - 1) := by
    have hpoint (x : Ω) : (∑ i, L i x) ^ 2 = ∑ i, ∑ j, L i x * L j x := by
      rw [pow_two, Finset.sum_mul_sum]
    simp_rw [hpoint]
    rw [integral_finset_sum _ (fun i _ ↦ Integrable.of_finite)]
    apply Eq.trans ?_ (finite_diagonal_cross_sum d)
    apply Finset.sum_congr rfl
    intro i _
    rw [integral_finset_sum _ (fun j _ ↦ hLL i j)]
    simp_rw [hpair]
  have hpoint (x : Ω) : ((∑ i, L i x) / K - 1) ^ 2 =
      (∑ i, L i x) ^ 2 / K ^ 2 - 2 * (∑ i, L i x) / K + 1 := by ring
  change (∫ x, ((∑ i, L i x) / K - 1) ^ 2 ∂μ) = (d - 1) / K
  simp_rw [hpoint]
  rw [integral_add, integral_sub, integral_div, integral_div, integral_const_mul, hsq, hsum]
  · simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
    field_simp
    ring
  · exact Integrable.of_finite
  · exact Integrable.of_finite
  · exact Integrable.of_finite
  · exact Integrable.of_finite

end StatisticalRL.GenerativeLowerBound
