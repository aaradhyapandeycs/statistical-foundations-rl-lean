import Formalization.OfflineRL.OfflineCountChernoff

/-! Optimal-arm count event for `thm:MAB_LCB_upper`.

Source: `chapters/offlineRL.tex:28–57, 280, 524–578`. For iid behavior actions,
positive optimal-arm mass, and the printed sample threshold, this proves the
failure bound for the optimal-arm count from the Bernoulli lower-tail result.
-/

open MeasureTheory ProbabilityTheory

namespace StatisticalRL.OfflineRL

theorem optimalArm_count_failure_le
    {Arm : Type*} [MeasurableSpace Arm] [MeasurableSingletonClass Arm] [DecidableEq Arm]
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (d : Measure Arm) [IsProbabilityMeasure d] (N : ℕ) (Y : Fin N → Ω → Arm)
    (hYm : ∀ i, Measurable (Y i)) (hYind : iIndepFun Y μ) (hYlaw : ∀ i, HasLaw (Y i) d μ)
    (aStar : Arm) (hd : 0 < d.real {aStar}) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hN : 8 * (1 / d.real {aStar}) * Real.log (2 / δ) ≤ N) :
    μ.real {ω | (visitCount Y aStar ω : ℝ) < N * d.real {aStar} / 2} ≤ δ / 2 := by
  set p := d.real {aStar} with hp
  have htail := visitCount_lower_tail μ d N Y hYm hYind hYlaw aStar
  have h8 : Real.log (2 / δ) ≤ (N : ℝ) * p / 8 := by
    have h' : 8 * (1 / p) * Real.log (2 / δ) * (p / 8) ≤ (N : ℝ) * (p / 8) :=
      mul_le_mul_of_nonneg_right hN (by positivity)
    have he : 8 * (1 / p) * Real.log (2 / δ) * (p / 8) = Real.log (2 / δ) := by
      field_simp
    rw [he] at h'
    linarith
  have hexp : Real.exp (-((N : ℝ) * p / 8)) ≤ δ / 2 := by
    calc Real.exp (-((N : ℝ) * p / 8)) ≤ Real.exp (-Real.log (2 / δ)) :=
          Real.exp_le_exp.mpr (by linarith)
      _ = δ / 2 := by
          rw [Real.exp_neg, Real.exp_log (by positivity)]
          field_simp
  exact htail.trans hexp

/-- Complement form: the count event `N_{a⋆} ≥ N d{a⋆}/2` holds with
probability at least `1 − δ/2`. -/
theorem optimalArm_count_event
    {Arm : Type*} [MeasurableSpace Arm] [MeasurableSingletonClass Arm] [DecidableEq Arm]
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (d : Measure Arm) [IsProbabilityMeasure d] (N : ℕ) (Y : Fin N → Ω → Arm)
    (hYm : ∀ i, Measurable (Y i)) (hYind : iIndepFun Y μ) (hYlaw : ∀ i, HasLaw (Y i) d μ)
    (aStar : Arm) (hd : 0 < d.real {aStar}) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hN : 8 * (1 / d.real {aStar}) * Real.log (2 / δ) ≤ N) :
    1 - δ / 2 ≤ μ.real {ω | (N : ℝ) * d.real {aStar} / 2 ≤ visitCount Y aStar ω} := by
  have hbad := optimalArm_count_failure_le μ d N Y hYm hYind hYlaw aStar hd δ hδ hδ1 hN
  have hc : {ω | (N : ℝ) * d.real {aStar} / 2 ≤ visitCount Y aStar ω}ᶜ =
      {ω | (visitCount Y aStar ω : ℝ) < N * d.real {aStar} / 2} := by
    ext ω; simp
  have hu := measureReal_union_le (μ := μ) {ω | (N : ℝ) * d.real {aStar} / 2 ≤ visitCount Y aStar ω}
    {ω | (N : ℝ) * d.real {aStar} / 2 ≤ visitCount Y aStar ω}ᶜ
  rw [Set.union_compl_self, probReal_univ, hc] at hu
  linarith

end StatisticalRL.OfflineRL
