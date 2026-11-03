import Formalization.ModelFree.QLearningIndicatorConditional

/-! Conditional expectation of a fresh Q-learning transition indicator. -/
open MeasureTheory ProbabilityTheory
namespace StatisticalRL.QLearning
variable {State Action : Type*} [Fintype State] [Fintype Action]
local instance : MeasurableSpace State := ⊤
local instance : MeasurableSpace Action := ⊤

/-- The strict past is a sub-sigma-algebra of the actual sample space. -/
theorem qPastSigma_le (T t : ℕ) :
    qPastSigma (State := State) (Action := Action) T t ≤
      (inferInstance : MeasurableSpace (QSamples State Action T)) := by
  exact (measurable_of_countable
    (qPastData (State := State) (Action := Action) T t)).comap_le

/-- The actual fresh-row coordinate generates an ambient sub-sigma-algebra. -/
theorem qFreshSigma_le (T t : ℕ) (ht : t < T) (s : State) (a : Action) :
    qFreshSigma T t ht s a ≤ (inferInstance : MeasurableSpace (QSamples State Action T)) := by
  exact (measurable_pi_apply ((s,a), (⟨t,ht⟩ : Fin T))).comap_le

/-- The current-row indicator's conditional mean equals its unconditional mean.
The next step must calculate that integral from the actual row marginal. -/
theorem qFreshIndicator_condExp_integral (M : DiscountedMDP State Action) (T t : ℕ)
    (ht : t < T) (s : State) (a : Action) (x : State) :
    (qSamplingLaw M T)[qFreshIndicator T t ht s a x | qPastSigma T t] =ᵐ[qSamplingLaw M T]
      fun _ ↦ ∫ data, qFreshIndicator T t ht s a x data ∂qSamplingLaw M T := by
  exact condExp_indep_eq (qFreshSigma_le T t ht s a) (qPastSigma_le T t)
    (qFreshIndicator_strong T t ht s a x) (qFreshSigma_indep_past M T t ht s a)

/-- Finite actual experiment: no bound or learning-rate hypothesis is needed
for integrability of a real-valued sample statistic. -/
theorem qSampling_integrable (M : DiscountedMDP State Action) (T : ℕ)
    (f : QSamples State Action T → ℝ) : Integrable f (qSamplingLaw M T) := by
  exact Integrable.of_finite

/- Remaining calculation: express qFreshIndicator as the indicator of the
coordinate preimage of {x}; apply integral_indicator_one, map_apply with
qSamplingLaw_marginal, and PMF.toMeasure_apply_singleton. This must show the
real integral is exactly (M.transition s a).prob x, including zero-probability
atoms. For centering and variance, apply finite-sum linearity and pull out
strongly F_t-measurable qValueBefore/row-mean coefficients. Their products are
integrable by qSampling_integrable. The desired identities themselves are not
assumed or proved in this file. -/
end StatisticalRL.QLearning
