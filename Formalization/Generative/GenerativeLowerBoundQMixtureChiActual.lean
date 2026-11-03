import Formalization.Generative.GenerativeLowerBoundQMixtureChiAssembly

/-! Actual Q-mixture χ² from product likelihood moments. -/
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators
namespace StatisticalRL.GenerativeLowerBound

/-- The actual baseline integral of the squared centered mixture density has
its exact K=mA diagonal/off-diagonal expression, including N=0. -/
theorem qMixtureActual_density_chi_integral {m A N : ℕ} [NeZero m] [NeZero A]
    (p q : ℝ≥0) (hp : 0 < p) (hp1 : p < 1) (hq1 : q ≤ 1) :
    ∫ x, (((qMixtureActiveLaw p q hp1.le hq1).rnDeriv
      (qMixtureActiveBaseline (m := m) (A := A) (N := N) p q hp1.le hq1) x).toReal - 1) ^ 2
      ∂(qMixtureActiveBaseline (m := m) (A := A) (N := N) p q hp1.le hq1) =
      ((1 + ((q : ℝ) - (p : ℝ)) ^ 2 / ((p : ℝ) * (1 - (p : ℝ)))) ^ N - 1) / (m * A) := by
  classical
  let Θ := Fin m × Fin A
  let Ω := QMixtureActiveCoordinates m A N → Bool
  let μ := qMixtureActiveBaseline (m := m) (A := A) (N := N) p q hp1.le hq1
  let L : Θ → Ω → ℝ := fun θ x ↦ qMixtureRowLikelihoodOnArray (p : ℝ) (q : ℝ) θ x
  let d : ℝ := (1 + ((q : ℝ) - (p : ℝ)) ^ 2 / ((p : ℝ) * (1 - (p : ℝ)))) ^ N
  have hmean (θ : Θ) : ∫ x, L θ x ∂μ = 1 :=
    qMixture_active_row_mean p q hp hp1 hq1 θ
  have hpair (θ θ' : Θ) : ∫ x, L θ x * L θ' x ∂μ = if θ = θ' then d else 1 := by
    by_cases h : θ = θ'
    · subst θ'
      simpa [L, d, pow_two] using qMixture_active_row_diagonal_moment p q hp hp1 hq1 θ
    · simpa [L, h] using qMixture_distinct_rows_cross_moment p q hp hp1 hq1 θ θ' h
  have hi := finite_mixture_centered_sq_integral μ L d hmean hpair
  simp_rw [qMixtureActiveLaw_density_eq_likelihood p q hp hp1 hq1]
  simpa [qMixtureLikelihood, L, μ, d, Θ, Fintype.card_prod] using hi

end StatisticalRL.GenerativeLowerBound
