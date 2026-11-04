import Formalization.Online.Regret.W2.OnlineW2IndicatorVariance

/-! Source-only coordinate-radius weakening. The simultaneous probability
certificate and its actual-history pullback are proved in the companion files.
The coordinate event is uniform over the finite state space. -/
namespace StatisticalRL.OnlineRL
variable {State : Type*} [Fintype State]
noncomputable local instance w2RadiusDecidable : DecidableEq State := Classical.decEq State

/-- The true-variance indicator radius implies the coordinate Bernstein radius
used by the source. -/
theorem onlineW2_indicator_radius_le (p : FiniteDistribution State) (x : State)
    (δ : ℝ) (n : ℕ) (hδ : 0 < δ) (hδsmall : δ ≤ 2 / 5) (hn : 0 < n) :
    onlineTrueW1Radius 1 δ n p (onlineW2Indicator x) ≤
      Real.sqrt (2 * p.prob x * Real.log (1 / δ) / n) + Real.log (1 / δ) / n := by
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  have hL : 0 ≤ Real.log (1 / (2 * δ)) := by
    apply Real.log_nonneg
    have : 2 * δ ≤ 1 := by linarith
    exact (one_le_div (by positivity)).2 this
  have hlog : Real.log (1 / (2 * δ)) ≤ Real.log (1 / δ) := by
    apply Real.log_le_log (by positivity)
    apply div_le_div_of_nonneg_left (by norm_num : (0:ℝ) ≤ 1) hδ
    linarith
  have hp := p.prob_nonneg x
  have hv := onlineW2Indicator_variance_le p x
  have hvar := p.variance_nonneg (onlineW2Indicator x)
  have hs : 2 * Real.log (1 / (2 * δ)) * p.variance (onlineW2Indicator x) / n ≤
      2 * p.prob x * Real.log (1 / δ) / n := by
    apply div_le_div_of_nonneg_right _ hn'.le
    nlinarith
  have hlin : 2 * 1 * Real.log (1 / (2 * δ)) / (3 * n) ≤
      Real.log (1 / δ) / n := by
    have : 2 * Real.log (1 / (2 * δ)) ≤ 3 * Real.log (1 / δ) := by linarith
    apply (div_le_div_iff₀ (by positivity : (0:ℝ) < 3 * n) hn').2
    nlinarith
  exact add_le_add (Real.sqrt_le_sqrt hs) hlin
end StatisticalRL.OnlineRL
