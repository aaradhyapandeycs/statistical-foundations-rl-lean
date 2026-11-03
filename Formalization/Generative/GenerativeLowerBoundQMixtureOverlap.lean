import Formalization.Generative.GenerativeLowerBoundQMixtureChiActual
import Formalization.Generative.GenerativeLowerBoundQMixtureRiskSelection

/-! Actual finite-law χ² and normalized-mixture event averaging. -/
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators
namespace StatisticalRL.GenerativeLowerBound

/-- The finite scalar χ² of actual probability atoms is exactly the genuine
baseline integral of squared centered Radon–Nikodym density. -/
theorem finiteChiSquared_eq_density_integral {Ω : Type*} [Fintype Ω]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hν : ∀ x, ν {x} ≠ 0) :
    finiteChiSquared (fun x ↦ μ.real {x}) (fun x ↦ ν.real {x}) =
      ∫ x, ((μ.rnDeriv ν x).toReal - 1) ^ 2 ∂ν := by
  classical
  rw [integral_fintype _ Integrable.of_finite]
  unfold finiteChiSquared
  apply Finset.sum_congr rfl
  intro x _
  rw [finite_rnDeriv_apply μ ν hν, ENNReal.toReal_div]
  simp [measureReal_def, mul_comm]

/-- A genuine finite-law density integral at most one gives overlap at least
one half, with zero alternative atoms allowed. -/
theorem finiteOverlap_ge_half_of_density_integral {Ω : Type*} [Fintype Ω]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hν : ∀ x, ν {x} ≠ 0)
    (hχ : (∫ x, ((μ.rnDeriv ν x).toReal - 1) ^ 2 ∂ν) ≤ 1) :
    (1 : ℝ) / 2 ≤ finiteOverlap μ ν := by
  have hm : ∀ x, 0 ≤ μ.real {x} := fun _ ↦ measureReal_nonneg
  have hn : ∀ x, 0 < ν.real {x} := fun x ↦ ENNReal.toReal_pos (hν x) (measure_ne_top ν _)
  have hm1 : ∑ x, μ.real {x} = 1 := by rw [sum_measureReal_singleton, Finset.coe_univ, probReal_univ]
  have hn1 : ∑ x, ν.real {x} = 1 := by rw [sum_measureReal_singleton, Finset.coe_univ, probReal_univ]
  unfold finiteOverlap
  apply finite_overlap_ge_half_of_chi_le_one _ _ hm hn hm1 hn1
  rw [finiteChiSquared_eq_density_integral μ ν hν]
  exact hχ

/-- For every event on the common active sample space, the actual normalized
mixture is the uniform average of the actual alternative probabilities. -/
theorem qMixtureActiveLaw_real_event {m A N : ℕ} [NeZero m] [NeZero A]
    (p q : ℝ≥0) (hp : p ≤ 1) (hq : q ≤ 1)
    (E : Set (QMixtureActiveCoordinates m A N → Bool)) :
    (qMixtureActiveLaw p q hp hq).real E =
      (∑ θ : Fin m × Fin A, (qMixtureActiveAlternative p q hp hq θ).real E) / (m * A) := by
  classical
  let s : Finset (QMixtureActiveCoordinates m A N → Bool) := Finset.univ.filter (· ∈ E)
  have hs : (s : Set _) = E := by ext x; simp [s]
  rw [← hs, ← sum_measureReal_singleton]
  have hsum (x : QMixtureActiveCoordinates m A N → Bool) :
      (∑ θ : Fin m × Fin A, qMixtureActiveAlternative p q hp hq θ {x}).toReal =
        ∑ θ : Fin m × Fin A, (qMixtureActiveAlternative p q hp hq θ {x}).toReal := by
    rw [ENNReal.toReal_sum (fun θ _ ↦ measure_ne_top _ _)]
  have halt (θ : Fin m × Fin A) :
      (qMixtureActiveAlternative p q hp hq θ).real (s : Set (QMixtureActiveCoordinates m A N → Bool)) =
        ∑ x ∈ s, (qMixtureActiveAlternative p q hp hq θ).real {x} :=
    (sum_measureReal_singleton (μ := qMixtureActiveAlternative p q hp hq θ) s).symm
  simp_rw [halt]
  simp only [measureReal_def, qMixtureActiveLaw_singleton, ENNReal.toReal_mul,
    ENNReal.toReal_inv, ENNReal.toReal_natCast, hsum, Fintype.card_prod, Nat.cast_mul]
  rw [Finset.sum_comm]
  simp only [Finset.mul_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro θ _
  apply Finset.sum_congr rfl
  intro x _
  simp only [Fintype.card_fin]
  ring

end StatisticalRL.GenerativeLowerBound
