import Formalization.ModelFree.MeanError

/-!
# Mean ℓ∞ error of asynchronous Q-learning (corrected Remark 4.3)

Source: arXiv:2610.41903v1, `chapters/generative_model_model_free.tex:2088–2090` (Remark 4.3, no
displayed formula), for Theorem 4.12 (:2062–2086). Reading: as in Remarks 4.1/4.2, `δ = ε(1−γ)/2`
inside Theorem 4.12's budget gives `E[max |Q_T − Q⋆|] ≤ ε(1−δ) + δ/(1−γ) ≤ 2ε`. The premises are
those of `Thm4_12_corrected` (`docs/SOURCE-ISSUES.md#C34`); the printed premises admit the
`T = 1`, `S A = 1` counterexample recorded there. Constants: `c₁ = 1` and `c₂ = max c₂⁰ 1`, where
`c₂⁰` is the constant of `AsyncQ.asyncQ_exists_c₂ 1`; enlarging `c₂` keeps Theorem 4.12's budget
(it is monotone in `c₂`) and makes the budget force the constant rate into `[0, 1]`, which the
crude bound `|Q_T − Q⋆| ≤ 1/(1−γ)` needs.
-/

open MeasureTheory ProbabilityTheory

namespace StatisticalRL.AsyncQ
open StatisticalRL.FiniteMarkov StatisticalRL.QLearning StatisticalRL.MeanError

universe u v

attribute [local instance] pairMeasurableSpace

local instance meanErrorPairMeasurableSingletonClass {S A : Type*} [Fintype S] [Fintype A] :
    @MeasurableSingletonClass (S × A) pairMeasurableSpace := ⟨fun _ ↦ trivial⟩

/-- `log 4 > 1`. -/
theorem one_lt_log_four : 1 < Real.log 4 := by
  rw [Real.lt_log_iff_exp_lt (by norm_num)]
  have := Real.exp_one_lt_d9
  linarith

/-- Scalar core of corrected Remark 4.3: the budget forces the constant rate
`log³T/((1−γ) T μ_min)` into `(−∞, 1]` once `c L² ≥ 1`, `ε ≤ 1` and `1−γ ≤ 1`. -/
theorem asyncRate_le_one {c L a h ε m T tm : ℝ} (hcL : 1 ≤ c * L ^ 2) (hm : 0 < m)
    (hh : 0 < h) (hh1 : h ≤ 1) (hε : 0 < ε) (hε1 : ε ≤ 1) (ha : 0 ≤ a) (hT : 0 < T)
    (hbud : c * L ^ 2 / m * max (a / (h ^ 4 * ε ^ 2)) tm ≤ T) :
    1 * a / (h * T * m) ≤ 1 := by
  have hq : 0 < h ^ 4 * ε ^ 2 := by positivity
  have hcLm : 0 ≤ c * L ^ 2 / m := div_nonneg (zero_le_one.trans hcL) hm.le
  have hfirst : c * L ^ 2 / m * (a / (h ^ 4 * ε ^ 2)) ≤ T :=
    le_trans (mul_le_mul_of_nonneg_left (le_max_left _ _) hcLm) hbud
  have hstep : a / (m * (h ^ 4 * ε ^ 2)) ≤ T := by
    refine le_trans ?_ hfirst
    rw [div_mul_div_comm, mul_comm (c * L ^ 2) a,
      div_le_div_iff₀ (by positivity) (by positivity)]
    have h0 : 0 ≤ a * (m * (h ^ 4 * ε ^ 2)) := by positivity
    have := mul_le_mul_of_nonneg_left hcL h0
    linarith
  have ha' : a ≤ T * m * (h ^ 4 * ε ^ 2) := by
    rw [div_le_iff₀ (by positivity)] at hstep
    linarith
  have hsmall : h ^ 3 * ε ^ 2 ≤ 1 := by
    have h1 : h ^ 3 ≤ 1 := pow_le_one₀ hh.le hh1
    have h2 : ε ^ 2 ≤ 1 := pow_le_one₀ hε.le hε1
    exact mul_le_one₀ h1 (sq_nonneg ε) h2
  have ha'' : a ≤ h * T * m := by
    have hTm : 0 ≤ T * m * h := by positivity
    have : T * m * (h ^ 4 * ε ^ 2) = T * m * h * (h ^ 3 * ε ^ 2) := by ring
    have h6 := mul_le_mul_of_nonneg_left hsmall hTm
    linarith
  rw [one_mul, div_le_one (by positivity)]
  exact ha''

open Classical in
/-- Corrected Remark 4.3: mean ℓ∞ error of asynchronous Q-learning with `δ = ε(1−γ)/2` in the
budget of `Thm4_12_corrected`. -/
theorem asyncQ_meanError_exists_constants :
    ∃ c₁ : ℝ, 0 < c₁ ∧ c₁ ≤ 1 ∧ ∃ c₂ : ℝ, 0 < c₂ ∧
    ∀ (S : Type u) (A : Type v) [Fintype S] [Fintype A]
      (M : DiscountedMDP S A) (πb : StationaryPolicy S A) (μ : FiniteDistribution (S × A))
      (μmin : ℝ) (tmix : ℕ) (s₀ : S) (ε : ℝ) (T : ℕ),
      1 / 2 ≤ M.discount →
      (∀ y, ∑ x, μ.prob x * pairKernel M πb x y = μ.prob y) →
      (∃ C r : ℝ, 0 ≤ r ∧ r < 1 ∧ ∀ (t : ℕ) (x : S × A),
          tvDist (pairPow M πb t x) μ.prob ≤ C * r ^ t) →
      IsLeast {t : ℕ | ∀ x : S × A, tvDist (pairPow M πb t x) μ.prob ≤ 1 / 4} tmix →
      (∀ x, μmin ≤ μ.prob x) → (∃ x, μ.prob x = μmin) →
      0 < μmin → 1 ≤ T → (2 ≤ T ∨ 2 ≤ Fintype.card S * Fintype.card A) →
      0 < ε → ε ≤ 1 →
      c₂ * Real.log (2 * (Fintype.card S : ℝ) * Fintype.card A * T /
            (ε * (1 - M.discount))) ^ 2 / μmin *
          max (Real.log T ^ 3 / ((1 - M.discount) ^ 4 * ε ^ 2)) (tmix / (1 - M.discount)) ≤ T →
      ∀ Q₀ : S → A → ℝ, (∀ s a, 0 ≤ Q₀ s a ∧ Q₀ s a ≤ M.effectiveHorizon) →
      let δ := ε * (1 - M.discount) / 2
      let err := fun x ↦ ⨆ p : S × A,
        |iterate M (c₁ * Real.log T ^ 3 / ((1 - M.discount) * T * μmin)) Q₀ x T p.1 p.2 -
          M.trajectoryExpectedQ M.optimalGreedyPolicy p.1 p.2|
      0 < δ ∧ δ < 1 ∧
      Integrable err (pathLaw M πb s₀ T) ∧
      ∫ x, err x ∂(pathLaw M πb s₀ T) ≤ ε * (1 - δ) + 1 / (1 - M.discount) * δ ∧
      ε * (1 - δ) + 1 / (1 - M.discount) * δ ≤ 2 * ε := by
  obtain ⟨c₂z, hc₂z, h⟩ := asyncQ_exists_c₂ 1 one_pos le_rfl
  refine ⟨1, one_pos, le_rfl, max c₂z 1, lt_of_lt_of_le one_pos (le_max_right _ _), ?_⟩
  intro S A _ _ M πb μ μmin tmix s₀ ε T hγ hst _herg htmix hμmin _hμatt hμ0 hT1 hT2 hε hε1
    hbud Q₀ h₀ δ err
  have hγone := M.discount_lt_one
  have hh : 0 < 1 - M.discount := by linarith
  have hhhalf : 1 - M.discount ≤ 1 / 2 := by linarith
  have hεγ : ε * (1 - M.discount) ≤ 1 := mul_le_one₀ hε1 hh.le (by linarith)
  obtain ⟨hδ0, hδ1, hscalar⟩ := meanError_scalar hγone hε hεγ
  -- notation
  set c := max c₂z 1 with hcdef
  set L := Real.log (2 * (Fintype.card S : ℝ) * Fintype.card A * T / (ε * (1 - M.discount)))
    with hLdef
  have hT1r : (1 : ℝ) ≤ T := by exact_mod_cast hT1
  have hlogT : 0 ≤ Real.log (T : ℝ) := Real.log_nonneg hT1r
  have hX0 : 0 ≤ max (Real.log T ^ 3 / ((1 - M.discount) ^ 4 * ε ^ 2))
      (tmix / (1 - M.discount)) := le_trans (by positivity) (le_max_right _ _)
  -- the budget with Theorem 4.12's own constant and δ
  have hlogarg : (Fintype.card S : ℝ) * Fintype.card A * T / δ =
      2 * (Fintype.card S : ℝ) * Fintype.card A * T / (ε * (1 - M.discount)) := by
    simp only [δ]
    rw [div_div_eq_mul_div]
    ring
  have hbud' : c₂z * Real.log ((Fintype.card S : ℝ) * Fintype.card A * T / δ) ^ 2 / μmin *
      max (Real.log T ^ 3 / ((1 - M.discount) ^ 4 * ε ^ 2)) (tmix / (1 - M.discount)) ≤ T := by
    rw [hlogarg]
    refine le_trans ?_ hbud
    exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _)) hμ0.le) hX0
  have hS1 : (1 : ℝ) ≤ Fintype.card S := by
    haveI := M.state_nonempty; exact_mod_cast Fintype.card_pos
  have hA1 : (1 : ℝ) ≤ Fintype.card A := by
    haveI := M.action_nonempty; exact_mod_cast Fintype.card_pos
  have hL1 : 1 ≤ L := by
    have h4 : (4 : ℝ) ≤
        2 * (Fintype.card S : ℝ) * Fintype.card A * T / (ε * (1 - M.discount)) := by
      rw [le_div_iff₀ (by positivity)]
      have hSAT : (1 : ℝ) ≤ (Fintype.card S : ℝ) * Fintype.card A * T := by
        have := mul_le_mul hS1 hA1 zero_le_one (by positivity)
        have := mul_le_mul this hT1r zero_le_one (by positivity)
        simpa using this
      have h5 : ε * (1 - M.discount) ≤ 1 * (1 / 2) := mul_le_mul hε1 hhhalf hh.le zero_le_one
      have : 4 * (ε * (1 - M.discount)) ≤ 2 := by linarith
      linarith
    exact (one_lt_log_four.trans_le (Real.log_le_log (by norm_num) h4)).le
  have hcL : 1 ≤ c * L ^ 2 := by
    have hc1 : 1 ≤ c := le_max_right _ _
    have hL2 : 1 ≤ L ^ 2 := one_le_pow₀ hL1
    exact one_le_mul_of_one_le_of_one_le hc1 hL2
  -- the constant rate lies in [0, 1]
  have hden : 0 < (1 - M.discount) * T * μmin := by positivity
  have hη0 : 0 ≤ 1 * Real.log T ^ 3 / ((1 - M.discount) * T * μmin) :=
    div_nonneg (by positivity) hden.le
  have hh1 : 1 - M.discount ≤ 1 := by linarith [M.discount_nonneg]
  have hη1 : 1 * Real.log T ^ 3 / ((1 - M.discount) * T * μmin) ≤ 1 :=
    asyncRate_le_one hcL hμ0 hh hh1 hε hε1 (pow_nonneg hlogT 3)
      (lt_of_lt_of_le one_pos hT1r) hbud
  have hp := h S A M πb μ μmin tmix s₀ δ ε T hγ hst htmix.1 hμmin hμ0 hT1 hT2 hδ0 hδ1 hε hε1
    hbud' Q₀ h₀
  -- the crude pathwise bound
  have hcrude : ∀ (x : Fin (T + 1) → S × A) (p : S × A),
      |iterate M (1 * Real.log T ^ 3 / ((1 - M.discount) * T * μmin)) Q₀ x T p.1 p.2 -
        M.trajectoryExpectedQ M.optimalGreedyPolicy p.1 p.2| ≤ 1 / (1 - M.discount) := by
    intro x p
    have h1 := iterate_mem M hη0 hη1 h₀ x T p.1 p.2
    have h2 := M.trajectoryExpectedQ_bounds M.optimalGreedyPolicy p.1 p.2
    simp only [DiscountedMDP.effectiveHorizon] at h1
    rw [abs_le]
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  haveI : Nonempty S := M.state_nonempty
  haveI : Nonempty A := M.action_nonempty
  haveI : IsProbabilityMeasure (pathLaw M πb s₀ T) :=
    pathMeasure_isProb (pairKernel_isStochastic M πb) (initLaw_isProb πb s₀) T
  have hεB : ε ≤ 1 / (1 - M.discount) := by
    rw [le_div_iff₀ hh]; linarith
  obtain ⟨hI, hE⟩ := integral_iSup_abs_le_of_highProb (pathLaw M πb s₀ T)
    (G := {x | ∀ s a,
      |iterate M (1 * Real.log T ^ 3 / ((1 - M.discount) * T * μmin)) Q₀ x T s a -
        M.trajectoryExpectedQ M.optimalGreedyPolicy s a| ≤ ε})
    (fun x (p : S × A) ↦
      iterate M (1 * Real.log T ^ 3 / ((1 - M.discount) * T * μmin)) Q₀ x T p.1 p.2 -
        M.trajectoryExpectedQ M.optimalGreedyPolicy p.1 p.2)
    hcrude hεB (fun _ hω p ↦ hω p.1 p.2) hp
  exact ⟨hδ0, hδ1, hI, hE, hscalar⟩

end StatisticalRL.AsyncQ
