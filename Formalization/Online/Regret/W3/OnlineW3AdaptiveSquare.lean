import Formalization.Probability.Variance

/-! Deterministic adaptive squared-value gap estimates for W₃. -/
namespace StatisticalRL.OnlineRL
variable {State : Type*} [Fintype State]

theorem onlineW3_square_gap_bounds
    (p : FiniteDistribution State) (U V P : State → ℝ) (H : ℝ)
    (hH : 0 ≤ H) (hP : ∀ s, 0 ≤ P s) (hPV : ∀ s, P s ≤ V s)
    (hVU : ∀ s, V s ≤ U s) (hUH : ∀ s, U s ≤ H) :
    (∀ s, 0 ≤ U s^2 - V s^2 ∧ U s^2 - V s^2 ≤ H^2) ∧
    p.variance (fun s => U s^2 - V s^2) ≤
      4 * H^2 * p.expectation (fun s => (U s - P s)^2) := by
  have hv (s : State) : 0 ≤ V s := le_trans (hP s) (hPV s)
  have hu (s : State) : 0 ≤ U s := le_trans (hv s) (hVU s)
  have hg (s : State) : 0 ≤ U s^2 - V s^2 ∧ U s^2 - V s^2 ≤ H^2 := by
    constructor <;> nlinarith [hP s, hPV s, hVU s, hUH s, sq_nonneg (H - U s)]
  refine ⟨hg, ?_⟩
  apply (p.variance_le_expectation_sq _).trans
  have hp (s : State) : (U s^2 - V s^2)^2 ≤ 4 * H^2 * (U s - P s)^2 := by
    have hsum0 : 0 ≤ U s + V s := by linarith [hu s, hv s]
    have hsum : U s + V s ≤ 2 * H := by linarith [hVU s, hUH s]
    have hdiff0 : 0 ≤ U s - V s := by linarith [hVU s]
    have hdiff : U s - V s ≤ U s - P s := by linarith [hPV s]
    have hsqsum : (U s + V s)^2 ≤ (2 * H)^2 := by nlinarith
    have hsqdiff : (U s - V s)^2 ≤ (U s - P s)^2 := by nlinarith
    have ha := mul_le_mul hsqsum hsqdiff (sq_nonneg _) (sq_nonneg _)
    nlinarith [ha]
  have hp' := p.expectation_mono hp
  simpa only [FiniteDistribution.expectation_mul] using hp'
end StatisticalRL.OnlineRL
