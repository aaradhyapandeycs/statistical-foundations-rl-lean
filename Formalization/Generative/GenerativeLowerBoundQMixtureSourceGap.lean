import Formalization.Generative.GenerativeLowerBoundQMixtureOptimal

/-! Actual source-parameter Q-mixture models and norm separation. -/
namespace StatisticalRL.GenerativeLowerBound
open StatisticalRL.DiscountedMDP

/-- The actual baseline/one-row-alternative MDP at source parameters. -/
noncomputable def qMixtureSourceMDP {m A : ℕ} [NeZero A] (i : QMixtureIndex m A)
    (γ ε : ℝ) (hγ : (2 : ℝ) / 3 ≤ γ) (hγ1 : γ < 1)
    (hε : 0 < ε) (hεmax : ε < 1 / (32 * (1 - γ))) :
    DiscountedMDP (Option (Fin m)) (Fin A) := by
  have ha := source_parameters_admissible γ ε hγ hγ1 hε hεmax
  exact qMixtureMDP i γ (baseProbability γ) (baseProbability γ + probabilityIncrement γ ε)
    (by linarith) hγ1 (by linarith [ha.1]) (by linarith [ha.2.1]) ha.2.2.1

/-- The actual optimal trajectory Q arrays of the baseline and each
alternative are more than 2ε apart in supremum norm. -/
theorem qMixtureSourceMDP_baseline_norm_gap {m A : ℕ} [NeZero A]
    (j : Fin m) (a : Fin A) (γ ε : ℝ) (hγ : (2 : ℝ) / 3 ≤ γ) (hγ1 : γ < 1)
    (hε : 0 < ε) (hεmax : ε < 1 / (32 * (1 - γ))) :
    let M₀ := qMixtureSourceMDP (none : QMixtureIndex m A) γ ε hγ hγ1 hε hεmax
    let M₁ := qMixtureSourceMDP (some (j,a)) γ ε hγ hγ1 hε hεmax
    2 * ε < ‖M₁.trajectoryExpectedQ M₁.optimalGreedyPolicy -
      M₀.trajectoryExpectedQ M₀.optimalGreedyPolicy‖ := by
  let M₀ := qMixtureSourceMDP (none : QMixtureIndex m A) γ ε hγ hγ1 hε hεmax
  let M₁ := qMixtureSourceMDP (some (j,a)) γ ε hγ hγ1 hε hεmax
  have hgap := qMixtureMDP_source_separation j a γ ε hγ hγ1 hε hεmax
  have h₁ := norm_le_pi_norm (M₁.trajectoryExpectedQ M₁.optimalGreedyPolicy -
    M₀.trajectoryExpectedQ M₀.optimalGreedyPolicy) (some j)
  have h₂ := norm_le_pi_norm ((M₁.trajectoryExpectedQ M₁.optimalGreedyPolicy -
    M₀.trajectoryExpectedQ M₀.optimalGreedyPolicy) (some j)) a
  have habs : M₁.trajectoryExpectedQ M₁.optimalGreedyPolicy (some j) a -
      M₀.trajectoryExpectedQ M₀.optimalGreedyPolicy (some j) a ≤
        |M₁.trajectoryExpectedQ M₁.optimalGreedyPolicy (some j) a -
          M₀.trajectoryExpectedQ M₀.optimalGreedyPolicy (some j) a| := le_abs_self _
  dsimp only [qMixtureSourceMDP] at hgap
  dsimp only [M₀, M₁, qMixtureSourceMDP] at *
  simpa only [Pi.sub_apply, Real.norm_eq_abs] using lt_of_lt_of_le hgap (habs.trans (h₂.trans h₁))

end StatisticalRL.GenerativeLowerBound
