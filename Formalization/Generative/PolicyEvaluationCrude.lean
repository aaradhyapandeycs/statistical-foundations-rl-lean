import Formalization.Generative.PolicyEvaluationUniversalConstant
import Formalization.Generative.ModelBasedPolicyEvaluation
import Formalization.MDP.PrefixValueBridge
import Formalization.MDP.InfiniteReturn

/-! The first-attempt policy-evaluation display
`eq:eq:Vhatpi-Vpi-difference-decoupled-Hoeffding`
(`chapters/generative_model_model_based.tex:270–276`), derived from the sharp
policy-evaluation export together with a crude bound and the one-state case. -/

open MeasureTheory ProbabilityTheory
namespace StatisticalRL.ModelBasedPolicyEvaluation

local instance crudeFinMeasurable (S : ℕ) : MeasurableSpace (Fin S) := ⊤

section General
variable {State Action : Type*} [Fintype State] [Fintype Action]

/-- The plug-in value lies in `[0, 1/(1−γ)]`. -/
theorem valueEstimator_bounds (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (N : ℕ) (hN : 0 < N) (data : Samples State N)
    (s : State) :
    0 ≤ valueEstimator M π N hN data s ∧
      valueEstimator M π N hN data s ≤ 1 / (1 - M.discount) := by
  unfold valueEstimator
  rw [← DiscountedMDP.trajectoryExpectedValue_eq_valueFixedPoint]
  exact (empiricalModel M π N hN data).trajectoryExpectedValue_bounds π s

/-- Crude bound `‖V̂^π − V^π‖∞ ≤ 1/(1−γ)`. -/
theorem norm_valueEstimator_sub_le (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (N : ℕ) (hN : 0 < N) (data : Samples State N) :
    ‖valueEstimator M π N hN data - M.trajectoryExpectedValue π‖ ≤ 1 / (1 - M.discount) := by
  have hh : 0 < 1 - M.discount := sub_pos.mpr M.discount_lt_one
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun s ↦ ?_
  have h1 := valueEstimator_bounds M π N hN data s
  have h2 := M.trajectoryExpectedValue_bounds π s
  rw [Pi.sub_apply, Real.norm_eq_abs, abs_sub_le_iff]
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

end General

/-- On one state every distribution is the point mass. -/
theorem expectation_fin_one (d : FiniteDistribution (Fin 1)) (V : Fin 1 → ℝ) :
    d.expectation V = V 0 := by
  have h := d.sum_prob
  rw [Fin.sum_univ_one] at h
  rw [FiniteDistribution.expectation, Fin.sum_univ_one, h, one_mul]

/-- With a single state the empirical model is exact: `V̂^π = V^π`. -/
theorem valueEstimator_eq_of_fin_one {A : ℕ} (M : DiscountedMDP (Fin 1) (Fin A))
    (π : StationaryPolicy (Fin 1) (Fin A)) (N : ℕ) (hN : 0 < N) (data : Samples (Fin 1) N) :
    valueEstimator M π N hN data = M.trajectoryExpectedValue π := by
  rw [DiscountedMDP.trajectoryExpectedValue_eq_valueFixedPoint]
  unfold valueEstimator
  have hop : (empiricalModel M π N hN data).valueBellman π (M.valueFixedPoint π) =
      M.valueBellman π (M.valueFixedPoint π) := by
    funext s
    simp only [DiscountedMDP.valueBellman, expectation_fin_one]
    simp [empiricalModel]
  exact ((DiscountedMDP.valueFixedPoint_characterization _ π _).1
    (hop.trans (M.valueFixedPoint_spec π))).symm

/-- Scalar estimate behind the first-attempt display: for `S ≥ 2`, `0 < δ < 1`,
`0 < h ≤ 1`, `(1−γ) · log(S/((δ/2)(1−γ))) ≤ 4 log(S/δ)` with `h = 1 − γ`. -/
theorem crude_log_estimate (S δ h : ℝ) (hS : 2 ≤ S) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hh : 0 < h) (hh1 : h ≤ 1) :
    h * Real.log (S / (δ / 2 * h)) ≤ 4 * Real.log (S / δ) := by
  have hSδ : 2 < S / δ := by
    rw [lt_div_iff₀ hδ]; nlinarith
  have hL : Real.log 2 < Real.log (S / δ) := Real.log_lt_log (by norm_num) hSδ
  have hlog2 := Real.log_two_gt_d9
  have hsplit : Real.log (S / (δ / 2 * h)) =
      Real.log 2 + Real.log (S / δ) + Real.log (1 / h) := by
    rw [show S / (δ / 2 * h) = 2 * (S / δ) * (1 / h) by field_simp,
      Real.log_mul (by positivity) (by positivity), Real.log_mul (by norm_num) (by positivity)]
  have hinv : Real.log (1 / h) ≤ 1 / h - 1 := Real.log_le_sub_one_of_pos (by positivity)
  have hhinv : h * Real.log (1 / h) ≤ 1 := by
    have : h * (1 / h - 1) ≤ 1 := by
      rw [mul_sub, mul_one_div_cancel hh.ne']; linarith
    exact (mul_le_mul_of_nonneg_left hinv hh.le).trans this
  have hlog2nn : 0 ≤ Real.log 2 := by linarith
  have hLnn : 0 ≤ Real.log (S / δ) := by linarith
  rw [hsplit, mul_add, mul_add]
  have e1 : h * Real.log 2 ≤ Real.log 2 := by nlinarith
  have e2 : h * Real.log (S / δ) ≤ Real.log (S / δ) := by nlinarith
  linarith

/-- `eq:eq:Vhatpi-Vpi-difference-decoupled-Hoeffding`: a universal `C₀` such that, with
probability exceeding `1 − δ`,
`‖V̂^π − V^π‖∞ ≤ C₀(√(log(S/δ)/((1−γ)⁴N)) + log(S/δ)/((1−γ)²N))`. -/
theorem decoupledHoeffding_universal_constant :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ (S A N : ℕ) (hN : 0 < N)
      (M : DiscountedMDP (Fin S) (Fin A)) (π : StationaryPolicy (Fin S) (Fin A)) (δ : ℝ),
      0 < δ → δ < 1 →
      1 - δ < (samplingLaw M π N).real
        {data | ‖valueEstimator M π N hN data - M.trajectoryExpectedValue π‖ ≤
          C₀ * (Real.sqrt (Real.log (S / δ) / ((1 - M.discount) ^ 4 * N)) +
            Real.log (S / δ) / ((1 - M.discount) ^ 2 * N))} := by
  obtain ⟨c, hc, hmain⟩ := policyEvaluation_universal_constant
  refine ⟨2 * Real.sqrt c, by positivity, ?_⟩
  intro S A N hN M π δ hδ hδ1
  have hh : 0 < 1 - M.discount := sub_pos.mpr M.discount_lt_one
  have hh1 : 1 - M.discount ≤ 1 := by linarith [M.discount_nonneg]
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hS1 : 1 ≤ S := by
    have := M.state_nonempty
    exact Nat.one_le_iff_ne_zero.mpr fun h ↦ by subst h; exact (not_isEmpty_of_nonempty (Fin 0)) inferInstance
  have hLnn : 0 ≤ Real.log (S / δ) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ hδ]
    have : (1 : ℝ) ≤ S := by exact_mod_cast hS1
    linarith
  set R := 2 * Real.sqrt c * (Real.sqrt (Real.log (S / δ) / ((1 - M.discount) ^ 4 * N)) +
    Real.log (S / δ) / ((1 - M.discount) ^ 2 * N)) with hR
  have hRnn : 0 ≤ R := by
    have : 0 ≤ Real.log (S / δ) / ((1 - M.discount) ^ 2 * N) := by positivity
    positivity
  have hall : (∀ data, ‖valueEstimator M π N hN data - M.trajectoryExpectedValue π‖ ≤ R) →
      1 - δ < (samplingLaw M π N).real
        {data | ‖valueEstimator M π N hN data - M.trajectoryExpectedValue π‖ ≤ R} := by
    intro hdata
    have h1 : (samplingLaw M π N).real Set.univ ≤ (samplingLaw M π N).real
        {data | ‖valueEstimator M π N hN data - M.trajectoryExpectedValue π‖ ≤ R} :=
      measureReal_mono (fun data _ ↦ hdata data) (measure_ne_top _ _)
    rw [probReal_univ] at h1
    linarith
  rcases hS1.eq_or_lt with hS | hS2
  · subst hS
    apply hall
    intro data
    rw [valueEstimator_eq_of_fin_one, sub_self, norm_zero]
    exact hRnn
  replace hS2 : (2 : ℝ) ≤ S := by exact_mod_cast hS2
  -- the accuracy level fed to the sharp export
  set x := c * Real.log (S / (δ / 2 * (1 - M.discount))) / ((1 - M.discount) ^ 3 * N) with hx
  have hlogpos : 0 < Real.log (S / (δ / 2 * (1 - M.discount))) := by
    apply Real.log_pos
    rw [lt_div_iff₀ (by positivity)]
    have : δ / 2 * (1 - M.discount) < 1 := by nlinarith
    linarith
  have hxpos : 0 < x := by positivity
  have hest := crude_log_estimate S δ (1 - M.discount) hS2 hδ hδ1 hh hh1
  have hxle : x ≤ (2 * Real.sqrt c) ^ 2 *
      (Real.log (S / δ) / ((1 - M.discount) ^ 4 * N)) := by
    have hkey : c * Real.log (S / (δ / 2 * (1 - M.discount))) * (1 - M.discount) ≤
        c * (4 * Real.log (S / δ)) := by
      rw [mul_assoc, mul_comm (Real.log _)]
      exact mul_le_mul_of_nonneg_left hest hc.le
    have hrhs : (2 * Real.sqrt c) ^ 2 * (Real.log (S / δ) / ((1 - M.discount) ^ 4 * N)) =
        c * (4 * Real.log (S / δ)) / ((1 - M.discount) * ((1 - M.discount) ^ 3 * N)) := by
      rw [mul_pow, Real.sq_sqrt hc.le]
      field_simp
      ring
    rw [hrhs, hx, div_le_div_iff₀ (by positivity) (by positivity)]
    have h3 : 0 ≤ (1 - M.discount) ^ 3 * (N : ℝ) := by positivity
    calc c * Real.log (S / (δ / 2 * (1 - M.discount))) *
          ((1 - M.discount) * ((1 - M.discount) ^ 3 * N))
        = (c * Real.log (S / (δ / 2 * (1 - M.discount))) * (1 - M.discount)) *
          ((1 - M.discount) ^ 3 * N) := by ring
      _ ≤ c * (4 * Real.log (S / δ)) * ((1 - M.discount) ^ 3 * N) :=
          mul_le_mul_of_nonneg_right hkey h3
  set ε := Real.sqrt x with hε
  have hεpos : 0 < ε := Real.sqrt_pos.mpr hxpos
  have hεR : ε ≤ R := by
    have h1 : ε ≤ 2 * Real.sqrt c *
        Real.sqrt (Real.log (S / δ) / ((1 - M.discount) ^ 4 * N)) := by
      rw [hε]
      calc Real.sqrt x ≤ Real.sqrt ((2 * Real.sqrt c) ^ 2 *
            (Real.log (S / δ) / ((1 - M.discount) ^ 4 * N))) := Real.sqrt_le_sqrt hxle
        _ = 2 * Real.sqrt c * Real.sqrt (Real.log (S / δ) / ((1 - M.discount) ^ 4 * N)) := by
          rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
    have h2 : 0 ≤ 2 * Real.sqrt c * (Real.log (S / δ) / ((1 - M.discount) ^ 2 * N)) := by
      positivity
    rw [hR, mul_add]
    linarith
  by_cases hεmax : ε ≤ 1 / (1 - M.discount)
  · have hthr : c * Real.log (S / (δ / 2 * (1 - M.discount))) /
        ((1 - M.discount) ^ 3 * ε ^ 2) ≤ N := by
      have hxN : (1 - M.discount) ^ 3 * x * N =
          c * Real.log (S / (δ / 2 * (1 - M.discount))) := by
        rw [hx]; field_simp
      rw [hε, Real.sq_sqrt hxpos.le, div_le_iff₀ (by positivity)]
      exact le_of_eq (by rw [← hxN]; ring)
    obtain ⟨hN', hp⟩ := hmain S A N M π (δ / 2) ε (by positivity) (by linarith) hεpos hεmax hthr
    have hmono : (samplingLaw M π N).real
        {data | ‖valueEstimator M π N hN' data - M.trajectoryExpectedValue π‖ ≤ ε} ≤
        (samplingLaw M π N).real
          {data | ‖valueEstimator M π N hN data - M.trajectoryExpectedValue π‖ ≤ R} :=
      measureReal_mono (fun data hd ↦ le_trans hd hεR) (measure_ne_top _ _)
    linarith
  · apply hall
    intro data
    have := norm_valueEstimator_sub_le M π N hN data
    push_neg at hεmax
    linarith

end StatisticalRL.ModelBasedPolicyEvaluation
