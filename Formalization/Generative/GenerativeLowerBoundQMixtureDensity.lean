import Formalization.Generative.GenerativeLowerBoundQMixtureActiveDiagonal

/-! Actual normalized alternative-mixture likelihood. -/
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators
namespace StatisticalRL.GenerativeLowerBound

/-- The actual mixture atom is the exactly normalized sum of the actual
alternative atoms. -/
theorem qMixtureActiveLaw_singleton {m A N : ℕ} [NeZero m] [NeZero A]
    (p q : ℝ≥0) (hp : p ≤ 1) (hq : q ≤ 1)
    (x : QMixtureActiveCoordinates m A N → Bool) :
    qMixtureActiveLaw p q hp hq {x} =
      (Fintype.card (Fin m × Fin A) : ℝ≥0∞)⁻¹ *
        ∑ θ, qMixtureActiveAlternative p q hp hq θ {x} := by
  classical
  unfold qMixtureActiveLaw
  rw [Measure.map_apply measurable_snd (measurableSet_singleton _)]
  let s : Finset ((Fin m × Fin A) × (QMixtureActiveCoordinates m A N → Bool)) :=
    Finset.univ.filter (fun z ↦ z.2 = x)
  have hs : (s : Set ((Fin m × Fin A) × (QMixtureActiveCoordinates m A N → Bool))) = Prod.snd ⁻¹' {x} := by ext z; simp [s]
  rw [← hs, ← sum_measure_singleton]
  simp [s, Finset.sum_filter, Fintype.sum_prod_type, finiteJointLaw_singleton,
    ← Finset.mul_sum]

/-- The actual normalized mixture derivative equals the uniform sum of the
actual one-row likelihoods; baseline positivity and K>0 are explicit. -/
theorem qMixtureActiveLaw_density_eq_likelihood {m A N : ℕ} [NeZero m] [NeZero A]
    (p q : ℝ≥0) (hp : 0 < p) (hp1 : p < 1) (hq1 : q ≤ 1)
    (x : QMixtureActiveCoordinates m A N → Bool) :
    ((qMixtureActiveLaw p q hp1.le hq1).rnDeriv
      (qMixtureActiveBaseline p q hp1.le hq1) x).toReal =
      qMixtureLikelihood (m := m) (A := A) (N := N) (p : ℝ) (q : ℝ) x := by
  classical
  rw [qMixtureActiveLaw_rnDeriv_atom p q hp hp1 hq1 x, qMixtureActiveLaw_singleton]
  rw [mul_div_assoc, ENNReal.toReal_mul, ENNReal.toReal_inv,
    ENNReal.toReal_natCast, div_eq_mul_inv, Finset.sum_mul, ENNReal.toReal_sum]
  · simp_rw [← div_eq_mul_inv, qMixtureActiveAlternative_atom_ratio p q hp hp1 hq1]
    simp [qMixtureLikelihood, Fintype.card_prod, mul_comm, div_eq_mul_inv]
  · intro θ _
    exact ENNReal.mul_ne_top (measure_ne_top _ _) (ENNReal.inv_ne_top.mpr (qMixtureActiveBaseline_atom_ne_zero p q hp hp1 hq1 x))

end StatisticalRL.GenerativeLowerBound
