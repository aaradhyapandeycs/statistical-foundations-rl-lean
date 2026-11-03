import Formalization.Generative.GenerativeLowerBoundQMixtureRowDensity

/-! Product cancellation for one changed row and disjoint row pairs. -/
open scoped BigOperators
namespace StatisticalRL.GenerativeLowerBound

/-- In the actual active-coordinate shape, all unchanged likelihood factors
are one, so the full product reduces exactly to the N changed-row factors. -/
theorem qMixture_product_one_changed_row {m A N : ℕ} (θ : Fin m × Fin A)
    (f : Fin N → ℝ) :
    (∏ z : QMixtureActiveCoordinates m A N, if z.1 = θ then f z.2 else 1) =
      ∏ t : Fin N, f t := by
  classical
  rw [Fintype.prod_prod_type]
  have h (v : Fin m × Fin A) : (∏ t : Fin N, if v = θ then f t else 1) =
      if v = θ then ∏ t : Fin N, f t else 1 := by
    by_cases hv : v = θ <;> simp [hv]
  simp_rw [h]
  simp

/-- A coordinate-dependent integrand still restricts to the selected row. -/
theorem qMixture_product_restrict_row {m A N : ℕ} (θ : Fin m × Fin A)
    (g : QMixtureActiveCoordinates m A N → ℝ) :
    (∏ z, if z.1 = θ then g z else 1) = ∏ t : Fin N, g (θ,t) := by
  classical
  rw [Fintype.prod_prod_type]
  have h (v : Fin m × Fin A) : (∏ t : Fin N, if v = θ then g (v,t) else 1) =
      if v = θ then ∏ t : Fin N, g (θ,t) else 1 := by
    by_cases hv : v = θ <;> simp [hv]
  simp_rw [h]
  simp

/-- Likelihood factors from two different state/action rows never change the
same time-coordinate, including when N=0. -/
theorem qMixture_distinct_row_factors {m A N : ℕ}
    (θ θ' : Fin m × Fin A) (hne : θ ≠ θ') (f g : Fin N → ℝ) :
    (∏ z : QMixtureActiveCoordinates m A N,
      (if z.1 = θ then f z.2 else 1) * (if z.1 = θ' then g z.2 else 1)) =
      (∏ t : Fin N, f t) * (∏ t : Fin N, g t) := by
  classical
  rw [Finset.prod_mul_distrib, qMixture_product_one_changed_row,
    qMixture_product_one_changed_row]

end StatisticalRL.GenerativeLowerBound

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace StatisticalRL.GenerativeLowerBound

/-- Under the actual baseline active product, two distinct changed-row
likelihoods have cross moment one, including N=0. -/
theorem qMixture_distinct_rows_cross_moment {m A N : ℕ} [NeZero m] [NeZero A]
    (p q : ℝ≥0) (hp : 0 < p) (hp1 : p < 1) (hq1 : q ≤ 1)
    (θ θ' : Fin m × Fin A) (hne : θ ≠ θ') :
    ∫ x, qMixtureRowLikelihoodOnArray (p : ℝ) (q : ℝ) θ x *
        qMixtureRowLikelihoodOnArray (p : ℝ) (q : ℝ) θ' x
      ∂(qMixtureActiveBaseline (m := m) (A := A) (N := N) p q hp1.le hq1) = 1 := by
  classical
  let f (z : QMixtureActiveCoordinates m A N) (b : Bool) : ℝ :=
    (if z.1 = θ then qMixtureBernoulliLikelihood (p : ℝ) (q : ℝ) b else 1) *
    (if z.1 = θ' then qMixtureBernoulliLikelihood (p : ℝ) (q : ℝ) b else 1)
  have hfactor (x : QMixtureActiveCoordinates m A N → Bool) :
      qMixtureRowLikelihoodOnArray (p : ℝ) (q : ℝ) θ x *
        qMixtureRowLikelihoodOnArray (p : ℝ) (q : ℝ) θ' x = ∏ z, f z (x z) := by
    unfold qMixtureRowLikelihoodOnArray qMixtureRowLikelihood
    simp only [f, Finset.prod_mul_distrib]
    rw [qMixture_product_restrict_row, qMixture_product_restrict_row]
  simp_rw [hfactor]
  unfold qMixtureActiveBaseline indexedBernoulliLaw
  simp only [qMixtureBernoulliParameter, Option.noConfusion, ↓reduceIte]
  rw [integral_fintype_prod_eq_prod]
  apply Finset.prod_eq_one
  intro z _
  by_cases hθ : z.1 = θ
  · have hn : z.1 ≠ θ' := by intro hh; exact hne (hθ.symm.trans hh)
    simp [f, hθ, hn, hne, qMixtureBernoulliLikelihood_integral p q hp hp1 hq1]
  · by_cases hθ' : z.1 = θ'
    · simp [f, hθ, hθ', Ne.symm hne, qMixtureBernoulliLikelihood_integral p q hp hp1 hq1]
    · simp only [f, hθ, hθ', ↓reduceIte, mul_one]
      have hu : ({false, true} : Set Bool) = Set.univ := by ext b; cases b <;> simp
      simp only [integral_const, smul_eq_mul, mul_one]
      rw [probReal_univ]

end StatisticalRL.GenerativeLowerBound
