import Formalization.ModelFree.QLearningLowerBoundZeta
import Formalization.ModelFree.QLearningLowerBoundValues
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Lemma 4.15 (`lem:lower-bound-E-xi-lower-Q`)

`chapters/generative_model_model_free.tex:3429–3449`, proof `:3707–3944`.

Proof route (differs from the printed one, which uses Freedman's inequality and a truncation; see
`docs/SOURCE-ISSUES.md` C31(3) for constant slips in that route): with `ζ_t = ξ_t(1) - ξ_t(2)`,
`E ξ_{t,max} = E|ζ_t|/2`; the pointwise inequality `u² ≤ B|u| + u⁴/B²` gives
`E|ζ| ≥ (E ζ² - E ζ⁴/B²)/B`; the martingale structure gives
`E ζ² ≥ S₂/(4(1-γ))` (using `E V̂ ≥ V⋆(1)`) and `E ζ⁴ ≤ 3κ²S₂² + κη²S₂/(1-γ)²`, `κ = 2/(3(1-γ))`,
`S₂ = ∑_k η²(1-η)^{2(t-k)} ∈ [η/3, η]` once `(1-η)^{2t} ≤ 1/3`.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace StatisticalRL.QLearning

/-- The state-1 rows of `qLbMDP` are the source rows. -/
theorem qLbMDP_rowSpec (γ : ℝ) (hγ : (1 : ℝ) / 4 < γ) (hγ1 : γ < 1) :
    qLbRowSpec (qLbMDP γ hγ hγ1) (qHardP γ) := by
  intro a x
  simp [qLbMDP, qLbRow, qHardRow]

/-- Pointwise: `u² ≤ B|u| + u⁴/B²` for `B > 0`. -/
theorem qLb_sq_le_abs_quartic (u B : ℝ) (hB : 0 < B) : u ^ 2 ≤ B * |u| + u ^ 4 / B ^ 2 := by
  have hu : u ^ 2 = |u| ^ 2 := (sq_abs u).symm
  rcases le_or_gt |u| B with h | h
  · have : 0 ≤ u ^ 4 / B ^ 2 := by positivity
    have h0 := abs_nonneg u
    nlinarith
  · have h0 := abs_nonneg u
    have hBu : B ^ 2 ≤ u ^ 2 := by rw [hu]; nlinarith
    have : u ^ 2 ≤ u ^ 4 / B ^ 2 := by
      rw [le_div_iff₀ (by positivity)]
      nlinarith [sq_nonneg u]
    nlinarith

/-- Closed form of `S₂(t) = ∑_{k=1}^t (η(1-η)^{t-k})²`. -/
theorem qLb_weight_sq_sum (η : ℝ) (t : ℕ) :
    (∑ k ∈ Finset.Icc 1 t, (η * (1 - η) ^ (t - k)) ^ 2) * (1 - (1 - η) ^ 2) =
      η ^ 2 * (1 - (1 - η) ^ (2 * t)) := by
  have hrec : ∀ t : ℕ, ∑ k ∈ Finset.Icc 1 (t + 1), (η * (1 - η) ^ (t + 1 - k)) ^ 2 =
      (1 - η) ^ 2 * ∑ k ∈ Finset.Icc 1 t, (η * (1 - η) ^ (t - k)) ^ 2 + η ^ 2 := by
    intro t
    have h := qLb_sum_Icc_geom_succ ((1 - η) ^ 2) (fun _ ↦ η ^ 2) t
    have e : ∀ m : ℕ, (η * (1 - η) ^ m) ^ 2 = ((1 - η) ^ 2) ^ m * η ^ 2 := by
      intro m; rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm m 2]; ring
    simp only [e]
    exact h
  induction t with
  | zero => simp
  | succ t ih =>
    rw [hrec t, show 2 * (t + 1) = 2 * t + 2 by ring, pow_add]
    have : ((1 - η) ^ 2 * ∑ k ∈ Finset.Icc 1 t, (η * (1 - η) ^ (t - k)) ^ 2 + η ^ 2) *
        (1 - (1 - η) ^ 2) = (1 - η) ^ 2 * ((∑ k ∈ Finset.Icc 1 t, (η * (1 - η) ^ (t - k)) ^ 2) *
        (1 - (1 - η) ^ 2)) + η ^ 2 * (1 - (1 - η) ^ 2) := by ring
    rw [this, ih]
    ring

/-- Scalar step of the fourth-moment induction. -/
theorem qLb_scalar_step4 (m4 m4' X Y ν η h A0 w : ℝ)
    (e4 : m4' = m4 + X + Y) (ih4 : m4 ≤ 3 * ν ^ 2 * A0 ^ 2 + ν * η ^ 2 * h ^ 2 * A0)
    (t1 : X ≤ 6 * (w ^ 2 * ν) * (ν * A0)) (t2 : Y ≤ ν * η ^ 2 * h ^ 2 * w ^ 2) :
    m4' ≤ 3 * ν ^ 2 * (A0 + w ^ 2) ^ 2 + ν * η ^ 2 * h ^ 2 * (A0 + w ^ 2) := by
  have : 0 ≤ 3 * ν ^ 2 * (w ^ 2) ^ 2 := by positivity
  have e : 3 * ν ^ 2 * (A0 + w ^ 2) ^ 2 + ν * η ^ 2 * h ^ 2 * (A0 + w ^ 2) =
      (3 * ν ^ 2 * A0 ^ 2 + ν * η ^ 2 * h ^ 2 * A0) + 6 * (w ^ 2 * ν) * (ν * A0) +
        ν * η ^ 2 * h ^ 2 * w ^ 2 + 3 * ν ^ 2 * (w ^ 2) ^ 2 := by ring
  linarith

theorem qLb_scalar_m4 (ν A h η : ℝ) (hν0 : 0 ≤ ν) (hνup : ν ≤ 2 / 3 * h) (hA0 : 0 ≤ A)
    (hAup : A ≤ η) (hh0 : 0 ≤ h) (hη0 : 0 ≤ η) :
    3 * ν ^ 2 * A ^ 2 + ν * η ^ 2 * h ^ 2 * A ≤ 4 / 3 * (η * h) ^ 2 + 2 / 3 * (η * h) ^ 3 := by
  have a1 : ν ^ 2 * A ^ 2 ≤ (2 / 3 * h) ^ 2 * η ^ 2 :=
    mul_le_mul (pow_le_pow_left₀ hν0 hνup 2) (pow_le_pow_left₀ hA0 hAup 2) (by positivity)
      (by positivity)
  have a2 : ν * A ≤ 2 / 3 * h * η := mul_le_mul hνup hAup hA0 (by positivity)
  have a3 : ν * A * (η ^ 2 * h ^ 2) ≤ 2 / 3 * h * η * (η ^ 2 * h ^ 2) :=
    mul_le_mul_of_nonneg_right a2 (by positivity)
  have e1 : 3 * ν ^ 2 * A ^ 2 + ν * η ^ 2 * h ^ 2 * A = 3 * (ν ^ 2 * A ^ 2) + ν * A * (η ^ 2 * h ^ 2) := by
    ring
  have e3 : 4 / 3 * (η * h) ^ 2 + 2 / 3 * (η * h) ^ 3 =
      3 * ((2 / 3 * h) ^ 2 * η ^ 2) + 2 / 3 * h * η * (η ^ 2 * h ^ 2) := by ring
  rw [e1, e3]; linarith

theorem qLb_scalar_m2 (a A h η m2 : ℝ) (ha : h / 4 ≤ a) (hA : η / 3 ≤ A) (hh0 : 0 ≤ h)
    (hη0 : 0 ≤ η) (hm : a * A ≤ m2) : η * h / 12 ≤ m2 := by
  have := mul_le_mul ha hA (by positivity) (le_trans (by positivity) ha)
  have e : h / 4 * (η / 3) = η * h / 12 := by ring
  linarith

theorem qLb_scalar_final (m1 m2 m4 x : ℝ) (hx0 : 0 < x) (hm2 : x / 12 ≤ m2)
    (hm4 : m4 ≤ 4 / 3 * x ^ 2 + 2 / 3 * x ^ 3)
    (hkey : ∀ B : ℝ, 0 < B → m2 ≤ B * m1 + m4 / B ^ 2) :
    5 / 768 * min (Real.sqrt x) 1 ≤ m1 := by
  rcases le_or_gt x 1 with hx1 | hx1
  · set r := Real.sqrt x with hr
    have hr0 : 0 < r := Real.sqrt_pos.mpr hx0
    have hrx : r ^ 2 = x := Real.sq_sqrt hx0.le
    have hB := hkey (8 * r) (by positivity)
    have hdiv : m4 / (8 * r) ^ 2 ≤ x / 32 := by
      rw [div_le_iff₀ (by positivity)]
      have h1 : x ^ 3 ≤ x ^ 2 := by
        have := mul_le_mul_of_nonneg_left hx1 (by positivity : (0 : ℝ) ≤ x ^ 2)
        nlinarith
      have e : x / 32 * (8 * r) ^ 2 = 2 * x * r ^ 2 := by ring
      rw [e, hrx]
      nlinarith
    have hm1 : 5 * r / 768 ≤ m1 := by
      have h2 : 5 * x / 96 ≤ 8 * r * m1 := by linarith
      rw [← hrx] at h2
      have h3 : 5 * r / 768 * (8 * r) ≤ m1 * (8 * r) := by nlinarith
      exact le_of_mul_le_mul_right h3 (by positivity)
    have hmin : min r 1 ≤ r := min_le_left _ _
    have := mul_le_mul_of_nonneg_left hmin (by norm_num : (0 : ℝ) ≤ 5 / 768)
    linarith
  · have hB := hkey (8 * x) (by positivity)
    have hdiv : m4 / (8 * x) ^ 2 ≤ x / 32 := by
      rw [div_le_iff₀ (by positivity)]
      have h1 : x ^ 2 ≤ x ^ 3 := by
        have := mul_le_mul_of_nonneg_left hx1.le (by positivity : (0 : ℝ) ≤ x ^ 2)
        nlinarith
      have e : x / 32 * (8 * x) ^ 2 = 2 * x ^ 3 := by ring
      rw [e]
      linarith
    have hm1 : 5 / 768 ≤ m1 := by
      have h2 : 5 * x / 96 ≤ 8 * x * m1 := by linarith
      have h3 : 5 / 768 * (8 * x) ≤ m1 * (8 * x) := by nlinarith
      exact le_of_mul_le_mul_right h3 (by positivity)
    have hmin : min (Real.sqrt x) 1 ≤ 1 := min_le_right _ _
    have := mul_le_mul_of_nonneg_left hmin (by norm_num : (0 : ℝ) ≤ 5 / 768)
    linarith

section Moments
variable (M : DiscountedMDP (Fin 4) Bool) (N : ℕ) (γ η : ℝ)

/-- Second- and fourth-moment bounds for the partial sums `S_n`, by induction on `n ≤ N`. -/
theorem qLb_zeta_moment_bounds (hγ : 3 / 4 ≤ γ) (hγ1 : γ < 1) (hη0 : 0 ≤ η) (hη1 : η ≤ 1)
    (hrow : qLbRowSpec M (qHardP γ)) (t : ℕ) (n : ℕ) (hn : n ≤ N) :
    let A := ∑ k ∈ Finset.Icc 1 n, (η * (1 - η) ^ (t - k)) ^ 2
    let q2 := 2 * (qHardP γ * (1 - qHardP γ))
    let h := 1 / (1 - γ)
    let ν := γ ^ 2 * q2 * h ^ 2
    γ ^ 2 * q2 * (1 / (1 - γ * qHardP γ)) ^ 2 * A ≤
        ∫ d, qLbZetaPartial γ η (qSamplesExtend M N d) t n ^ 2 ∂qSamplingLaw M N ∧
      ∫ d, qLbZetaPartial γ η (qSamplesExtend M N d) t n ^ 2 ∂qSamplingLaw M N ≤ ν * A ∧
      ∫ d, qLbZetaPartial γ η (qSamplesExtend M N d) t n ^ 4 ∂qSamplingLaw M N ≤
        3 * ν ^ 2 * A ^ 2 + ν * η ^ 2 * h ^ 2 * A := by
  intro A q2 h ν
  have hγ' : (1 : ℝ) / 4 < γ := by linarith
  have hp := qHardP_bounds γ hγ' hγ1
  have hq2 : 0 ≤ q2 := by have := mul_nonneg hp.1 (by linarith : (0 : ℝ) ≤ 1 - qHardP γ); positivity
  have hh0 : 0 ≤ h := by have : 0 < 1 - γ := by linarith
                         positivity
  have hν0 : 0 ≤ ν := by positivity
  have hVh0 : 0 ≤ 1 / (1 - γ * qHardP γ) := by rw [qLb_vstar_eq γ hγ' hγ1]; have : 0 < 1 - γ := by linarith
                                               positivity
  induction n with
  | zero => simp [A, qLbZetaPartial]
  | succ n ih =>
    obtain ⟨ih1, ih2, ih4⟩ := ih (by omega)
    set w := η * (1 - η) ^ (t - (n + 1)) with hw
    have hw0 : 0 ≤ w := by have : 0 ≤ 1 - η := by linarith
                           positivity
    have hw1 : w ≤ η := by
      have : (1 - η) ^ (t - (n + 1)) ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
      nlinarith
    have hA : (∑ k ∈ Finset.Icc 1 (n + 1), (η * (1 - η) ^ (t - k)) ^ 2) =
        (∑ k ∈ Finset.Icc 1 n, (η * (1 - η) ^ (t - k)) ^ 2) + w ^ 2 := by
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1)]
    set A0 := ∑ k ∈ Finset.Icc 1 n, (η * (1 - η) ^ (t - k)) ^ 2
    have hA0 : 0 ≤ A0 := Finset.sum_nonneg (fun k _ ↦ sq_nonneg _)
    -- bounds on V̂_n
    have hVb := fun d : QSamples (Fin 4) Bool N ↦
      qLbAuxValue_bounds γ η hγ' hγ1 hη0 hη1 (qSamplesExtend M N d) n
    have hV2up : ∫ d, qLbAuxValue γ η (qSamplesExtend M N d) n ^ 2 ∂qSamplingLaw M N ≤ h ^ 2 := by
      calc _ ≤ ∫ _d, h ^ 2 ∂qSamplingLaw M N :=
            integral_mono (qSampling_integrable M N _) (integrable_const _)
              (fun d ↦ pow_le_pow_left₀ (hVb d).1 (hVb d).2 2)
        _ = h ^ 2 := by simp
    have hV2low : (1 / (1 - γ * qHardP γ)) ^ 2 ≤
        ∫ d, qLbAuxValue γ η (qSamplesExtend M N d) n ^ 2 ∂qSamplingLaw M N := by
      have h1 := qLb_auxValue_integral_ge M N γ η hγ' hγ1 hη0 hη1 hrow n (by omega)
      have h2 := qLb_sq_integral_le M N (fun d ↦ qLbAuxValue γ η (qSamplesExtend M N d) n) 0
      simp only [sub_zero] at h2
      exact (pow_le_pow_left₀ hVh0 h1 2).trans h2
    have hV4up : ∫ d, qLbAuxValue γ η (qSamplesExtend M N d) n ^ 4 ∂qSamplingLaw M N ≤ h ^ 4 := by
      calc _ ≤ ∫ _d, h ^ 4 ∂qSamplingLaw M N :=
            integral_mono (qSampling_integrable M N _) (integrable_const _)
              (fun d ↦ pow_le_pow_left₀ (hVb d).1 (hVb d).2 4)
        _ = h ^ 4 := by simp
    have hSV : ∫ d, qLbZetaPartial γ η (qSamplesExtend M N d) t n ^ 2 *
        qLbAuxValue γ η (qSamplesExtend M N d) n ^ 2 ∂qSamplingLaw M N ≤
        h ^ 2 * ∫ d, qLbZetaPartial γ η (qSamplesExtend M N d) t n ^ 2 ∂qSamplingLaw M N := by
      rw [← integral_const_mul]
      apply integral_mono (qSampling_integrable M N _) (qSampling_integrable M N _)
      intro d
      have := pow_le_pow_left₀ (hVb d).1 (hVb d).2 2
      have h0 := sq_nonneg (qLbZetaPartial γ η (qSamplesExtend M N d) t n)
      simp only
      nlinarith
    have e2 := qLb_zeta_sq_succ M N γ η hrow t n (by omega)
    have e4 := qLb_zeta_four_succ M N γ η hrow t n (by omega)
    rw [← hw] at e2 e4
    have hq2def : 2 * (qHardP γ * (1 - qHardP γ)) = q2 := rfl
    rw [hq2def] at e2 e4
    have hγ2 : γ ^ 2 ≤ 1 := by nlinarith
    have hγ20 : 0 ≤ γ ^ 2 := sq_nonneg γ
    refine ⟨?_, ?_, ?_⟩
    · show γ ^ 2 * q2 * (1 / (1 - γ * qHardP γ)) ^ 2 *
          (∑ k ∈ Finset.Icc 1 (n + 1), (η * (1 - η) ^ (t - k)) ^ 2) ≤ _
      rw [hA, e2]
      have : (w * γ) ^ 2 * q2 * (1 / (1 - γ * qHardP γ)) ^ 2 ≤ (w * γ) ^ 2 * q2 *
          ∫ d, qLbAuxValue γ η (qSamplesExtend M N d) n ^ 2 ∂qSamplingLaw M N :=
        mul_le_mul_of_nonneg_left hV2low (by positivity)
      have e : γ ^ 2 * q2 * (1 / (1 - γ * qHardP γ)) ^ 2 * (A0 + w ^ 2) =
          γ ^ 2 * q2 * (1 / (1 - γ * qHardP γ)) ^ 2 * A0 +
            (w * γ) ^ 2 * q2 * (1 / (1 - γ * qHardP γ)) ^ 2 := by ring
      linarith
    · show _ ≤ ν * (∑ k ∈ Finset.Icc 1 (n + 1), (η * (1 - η) ^ (t - k)) ^ 2)
      rw [hA, e2]
      have : (w * γ) ^ 2 * q2 * ∫ d, qLbAuxValue γ η (qSamplesExtend M N d) n ^ 2
          ∂qSamplingLaw M N ≤ (w * γ) ^ 2 * q2 * h ^ 2 :=
        mul_le_mul_of_nonneg_left hV2up (by positivity)
      have : ν * (A0 + w ^ 2) = ν * A0 + (w * γ) ^ 2 * q2 * h ^ 2 := by simp only [ν]; ring
      linarith
    · show _ ≤ 3 * ν ^ 2 * (∑ k ∈ Finset.Icc 1 (n + 1), (η * (1 - η) ^ (t - k)) ^ 2) ^ 2 +
          ν * η ^ 2 * h ^ 2 * (∑ k ∈ Finset.Icc 1 (n + 1), (η * (1 - η) ^ (t - k)) ^ 2)
      rw [hA, e4]
      set m2 := ∫ d, qLbZetaPartial γ η (qSamplesExtend M N d) t n ^ 2 ∂qSamplingLaw M N
      set m4 := ∫ d, qLbZetaPartial γ η (qSamplesExtend M N d) t n ^ 4 ∂qSamplingLaw M N
      have t1 : 6 * (w * γ) ^ 2 * q2 * ∫ d, qLbZetaPartial γ η (qSamplesExtend M N d) t n ^ 2 *
          qLbAuxValue γ η (qSamplesExtend M N d) n ^ 2 ∂qSamplingLaw M N ≤
          6 * (w ^ 2 * ν) * (ν * A0) := by
        have := mul_le_mul_of_nonneg_left (hSV.trans (mul_le_mul_of_nonneg_left ih2
          (by positivity))) (by positivity : (0 : ℝ) ≤ 6 * (w * γ) ^ 2 * q2)
        calc _ ≤ 6 * (w * γ) ^ 2 * q2 * (h ^ 2 * (ν * A0)) := this
          _ = 6 * (w ^ 2 * ν) * (ν * A0) := by simp only [ν]; ring
      have t2 : (w * γ) ^ 4 * q2 * ∫ d, qLbAuxValue γ η (qSamplesExtend M N d) n ^ 4
          ∂qSamplingLaw M N ≤ ν * η ^ 2 * h ^ 2 * w ^ 2 := by
        have := mul_le_mul_of_nonneg_left hV4up (by positivity : (0 : ℝ) ≤ (w * γ) ^ 4 * q2)
        have hww : w ^ 2 ≤ η ^ 2 := pow_le_pow_left₀ hw0 hw1 2
        calc _ ≤ (w * γ) ^ 4 * q2 * h ^ 4 := this
          _ = ν * h ^ 2 * w ^ 2 * (γ ^ 2 * w ^ 2) := by simp only [ν]; ring
          _ ≤ ν * h ^ 2 * w ^ 2 * (1 * η ^ 2) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact mul_le_mul hγ2 hww (sq_nonneg _) zero_le_one
          _ = ν * η ^ 2 * h ^ 2 * w ^ 2 := by ring
      exact qLb_scalar_step4 _ _ _ _ ν η h A0 w rfl ih4 t1 t2

/-- Internal form of Lemma 4.15: `E ξ_{t,max} ≥ (5/1536)·min(√(η/(1-γ)), 1)` whenever
`(1-η)^{2t} ≤ 1/3`, `t ≤ N`. -/
theorem qLb_xiMax_lower (hγ : 3 / 4 ≤ γ) (hγ1 : γ < 1) (hη0 : 0 < η) (hη1 : η ≤ 1)
    (hrow : qLbRowSpec M (qHardP γ)) (t : ℕ) (ht : t ≤ N) (hdec : (1 - η) ^ (2 * t) ≤ 1 / 3) :
    5 / 1536 * min (Real.sqrt (η / (1 - γ))) 1 ≤
      ∫ d, qLbXiMax γ η (qSamplesExtend M N d) t ∂qSamplingLaw M N := by
  have hγ' : (1 : ℝ) / 4 < γ := by linarith
  have hg : 0 < 1 - γ := by linarith
  obtain ⟨hm2, hm2u, hm4⟩ := qLb_zeta_moment_bounds M N γ η hγ hγ1 hη0.le hη1 hrow t t ht
  rw [qLb_integral_xiMax M N γ η hrow t ht]
  simp_rw [qLbXi_sub]
  set A := ∑ k ∈ Finset.Icc 1 t, (η * (1 - η) ^ (t - k)) ^ 2 with hAdef
  set m1 := ∫ d, |qLbZetaPartial γ η (qSamplesExtend M N d) t t| ∂qSamplingLaw M N
  set m2 := ∫ d, qLbZetaPartial γ η (qSamplesExtend M N d) t t ^ 2 ∂qSamplingLaw M N
  set m4 := ∫ d, qLbZetaPartial γ η (qSamplesExtend M N d) t t ^ 4 ∂qSamplingLaw M N
  set h := 1 / (1 - γ) with hh
  have hh0 : 0 < h := by positivity
  -- A ∈ [η/3, η]
  have hAc := qLb_weight_sq_sum η t
  rw [← hAdef] at hAc
  have hA1 : A * (2 - η) = η * (1 - (1 - η) ^ (2 * t)) := by
    have e : A * (1 - (1 - η) ^ 2) = η * (A * (2 - η)) := by ring
    rw [e, show η ^ 2 * (1 - (1 - η) ^ (2 * t)) = η * (η * (1 - (1 - η) ^ (2 * t))) by ring]
      at hAc
    exact mul_left_cancel₀ hη0.ne' hAc
  have hpow0 : 0 ≤ (1 - η) ^ (2 * t) := pow_nonneg (by linarith) _
  have hAlow : η / 3 ≤ A := by nlinarith
  have hAup : A ≤ η := by nlinarith
  have hA0 : 0 ≤ A := by linarith
  -- constants
  have hpv := qLb_gamma_sq_p_var γ hγ'
  have hVh := qLb_vstar_eq γ hγ' hγ1
  have hν'low : h / 4 ≤ γ ^ 2 * (2 * (qHardP γ * (1 - qHardP γ))) * (1 / (1 - γ * qHardP γ)) ^ 2 := by
    rw [hVh, show γ ^ 2 * (2 * (qHardP γ * (1 - qHardP γ))) = 2 * (γ ^ 2 * (qHardP γ * (1 - qHardP γ)))
      by ring, hpv, hh]
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 4)]
    field_simp
    nlinarith
  set ν := γ ^ 2 * (2 * (qHardP γ * (1 - qHardP γ))) * h ^ 2 with hνdef
  have hνup : ν ≤ 2 / 3 * h := by
    rw [hνdef, show γ ^ 2 * (2 * (qHardP γ * (1 - qHardP γ))) = 2 * (γ ^ 2 * (qHardP γ * (1 - qHardP γ)))
      by ring, hpv, hh]
    field_simp
    nlinarith
  have hν0 : 0 ≤ ν := by
    have hp := qHardP_bounds γ hγ' hγ1
    have := mul_nonneg hp.1 (by linarith : (0 : ℝ) ≤ 1 - qHardP γ)
    positivity
  set x := η / (1 - γ) with hx
  have hxh : x = η * h := by rw [hx, hh]; ring
  have hx0 : 0 < x := by positivity
  have hm2x : x / 12 ≤ m2 := by
    rw [hxh]
    exact qLb_scalar_m2 _ A h η m2 hν'low hAlow hh0.le hη0.le hm2
  have hm4x : m4 ≤ 4 / 3 * x ^ 2 + 2 / 3 * x ^ 3 := by
    rw [hxh]
    exact hm4.trans (qLb_scalar_m4 ν A h η hν0 hνup hA0 hAup hh0.le hη0.le)
  -- the truncation inequality
  have hkey : ∀ B : ℝ, 0 < B → m2 ≤ B * m1 + m4 / B ^ 2 := by
    intro B hB
    have := integral_mono (qSampling_integrable M N _) (qSampling_integrable M N _)
      (fun d ↦ qLb_sq_le_abs_quartic (qLbZetaPartial γ η (qSamplesExtend M N d) t t) B hB)
    rw [integral_add (qSampling_integrable M N _) (qSampling_integrable M N _),
      integral_const_mul, integral_div] at this
    exact this
  have := qLb_scalar_final m1 m2 m4 x hx0 hm2x hm4x hkey
  linarith

end Moments

/-- `ρ^T ≤ 1/100` once `η(1-γ)T ≥ 4`, where `ρ = 1 - η(1-γp)` (`eq:EV2-0246`). -/
theorem qLb_rho_pow_le (γ η : ℝ) (T : ℕ) (hγ : 3 / 4 ≤ γ) (hγ1 : γ < 1) (hη0 : 0 ≤ η)
    (hη1 : η ≤ 1) (h4 : 4 ≤ η * (1 - γ) * T) :
    (1 - η * (1 - γ * qHardP γ)) ^ T ≤ 1 / 100 := by
  have hγ' : (1 : ℝ) / 4 < γ := by linarith
  have hid : 1 - γ * qHardP γ = 4 * (1 - γ) / 3 := by
    have hγ0 : γ ≠ 0 := by intro h; rw [h] at hγ; norm_num at hγ
    unfold qHardP; field_simp; ring
  rw [hid]
  set y := η * (4 * (1 - γ) / 3)
  have hy1 : y ≤ 1 / 3 := by
    have : η * (1 - γ) ≤ 1 / 4 := by nlinarith
    simp only [y]; nlinarith
  have hρ0 : 0 ≤ 1 - y := by linarith
  have h1 : (1 - y) ^ T ≤ Real.exp (-y) ^ T :=
    pow_le_pow_left₀ hρ0 (Real.one_sub_le_exp_neg y) T
  rw [← Real.exp_nat_mul] at h1
  have h2 : (T : ℝ) * -y ≤ -5 := by
    have : (T : ℝ) * y = 4 / 3 * (η * (1 - γ) * T) := by simp only [y]; ring
    nlinarith
  have h3 : Real.exp ((T : ℝ) * -y) ≤ Real.exp (-5) := Real.exp_le_exp.mpr h2
  have h5 : (100 : ℝ) ≤ Real.exp 5 := by
    have he : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have : Real.exp 5 = Real.exp 1 ^ 5 := by rw [← Real.exp_nat_mul]; norm_num
    rw [this]
    calc (100 : ℝ) ≤ 2.7 ^ 5 := by norm_num
      _ ≤ Real.exp 1 ^ 5 := pow_le_pow_left₀ (by norm_num) he 5
  have h6 : Real.exp (-5) ≤ 1 / 100 := by
    rw [Real.exp_neg, inv_eq_one_div, div_le_div_iff₀ (Real.exp_pos 5) (by norm_num)]
    linarith
  linarith

/-- Lemma 4.15 (`lem:lower-bound-E-xi-lower-Q`), with the Step-5 context written out.
`c = 1/320`, `c₃ = 16`. -/
theorem qLb_lemma415 : ∃ c c₃ : ℝ, 0 < c ∧ 0 < c₃ ∧
    ∀ (γ : ℝ) (hγ : 3 / 4 ≤ γ) (hγ1 : γ < 1) (T : ℕ) (η : ℝ),
      c₃ / (1 - γ) ^ 2 ≤ T → 4 / ((1 - γ) * T) < η → η < 1 / ((1 - γ) ^ 2 * T) →
      let ρ := 1 - η * (1 - γ * qHardP γ)
      (∃ τ : ℕ, ρ ^ (T + 1 - τ) ≤ 6 / 7 ∧ ∀ τ' : ℕ, ρ ^ (T + 1 - τ') ≤ 6 / 7 → τ' ≤ τ) ∧
      ∀ τhat : ℕ, ρ ^ (T + 1 - τhat) ≤ 6 / 7 →
        (∀ τ' : ℕ, ρ ^ (T + 1 - τ') ≤ 6 / 7 → τ' ≤ τhat) →
        ∀ t N : ℕ, τhat ≤ t → t ≤ N →
          c / (Real.sqrt ((1 - γ) ^ 2 * T) * Real.log T) ≤
            ∫ d, qLbXiMax γ η (qSamplesExtend (qLbMDP γ (by linarith) hγ1) N d) t
              ∂qSamplingLaw (qLbMDP γ (by linarith) hγ1) N := by
  refine ⟨1 / 320, 16, by norm_num, by norm_num, ?_⟩
  intro γ hγ hγ1 T η hT hηlow hηup ρ
  have hγ' : (1 : ℝ) / 4 < γ := by linarith
  have hg : 0 < 1 - γ := by linarith
  have hg4 : 1 - γ ≤ 1 / 4 := by linarith
  have hg2 : 0 < (1 - γ) ^ 2 := by positivity
  have hRT : 16 ≤ (1 - γ) ^ 2 * T := by rw [div_le_iff₀ hg2] at hT; linarith
  have hT256 : (256 : ℝ) ≤ T := by
    have : (1 - γ) ^ 2 ≤ 1 / 16 := by nlinarith
    nlinarith
  have hTpos : (0 : ℝ) < T := by linarith
  have hη0 : 0 < η := lt_of_le_of_lt (by positivity) hηlow
  have hη1 : η ≤ 1 := by
    have : 1 / ((1 - γ) ^ 2 * T) ≤ 1 / 16 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
    linarith
  have h4 : 4 ≤ η * (1 - γ) * T := by
    rw [div_lt_iff₀ (by positivity)] at hηlow; linarith
  have hρT := qLb_rho_pow_le γ η T hγ hγ1 hη0.le hη1 h4
  have hid : 1 - γ * qHardP γ = 4 * (1 - γ) / 3 := by
    have hγ0 : γ ≠ 0 := by intro h; rw [h] at hγ; norm_num at hγ
    unfold qHardP; field_simp; ring
  have hρ0 : 0 ≤ ρ := by
    simp only [ρ]; rw [hid]; nlinarith
  have hρ1 : ρ ≤ 1 := by
    simp only [ρ]; rw [hid]; nlinarith
  have hηρ : 1 - η ≤ ρ := by
    simp only [ρ]; rw [hid]; nlinarith
  have hnotbig : ∀ τ' : ℕ, ρ ^ (T + 1 - τ') ≤ 6 / 7 → τ' ≤ T := by
    intro τ' h
    by_contra hc
    rw [show T + 1 - τ' = 0 by omega, pow_zero] at h
    norm_num at h
  constructor
  · classical
    refine ⟨Nat.findGreatest (fun τ ↦ ρ ^ (T + 1 - τ) ≤ 6 / 7) T, ?_, ?_⟩
    · have h0 : ρ ^ (T + 1 - 0) ≤ 6 / 7 := by
        have : ρ ^ (T + 1 - 0) ≤ ρ ^ T := pow_le_pow_of_le_one hρ0 hρ1 (by omega)
        linarith
      exact Nat.findGreatest_spec (P := fun τ ↦ ρ ^ (T + 1 - τ) ≤ 6 / 7) (Nat.zero_le T) h0
    · intro τ' h
      exact Nat.le_findGreatest (hnotbig τ' h) h
  · intro τhat hτ hmax t N htτ htN
    have hτT := hnotbig τhat hτ
    have hgt : 6 / 7 < ρ ^ (T - τhat) := by
      by_contra hc
      push_neg at hc
      have := hmax (τhat + 1) (by rw [show T + 1 - (τhat + 1) = T - τhat by omega]; exact hc)
      omega
    have hsplit : ρ ^ T = ρ ^ τhat * ρ ^ (T - τhat) := by
      rw [← pow_add, show τhat + (T - τhat) = T by omega]
    have hρτ : ρ ^ τhat ≤ 7 / 600 := by
      have h0 : 0 ≤ ρ ^ τhat := pow_nonneg hρ0 _
      nlinarith
    have hdec : (1 - η) ^ (2 * t) ≤ 1 / 3 := by
      have a1 : (1 - η) ^ (2 * t) ≤ (1 - η) ^ τhat :=
        pow_le_pow_of_le_one (by linarith) (by linarith) (by omega)
      have a2 : (1 - η) ^ τhat ≤ ρ ^ τhat := pow_le_pow_left₀ (by linarith) hηρ τhat
      linarith
    have hmain := qLb_xiMax_lower (qLbMDP γ hγ' hγ1) N γ η hγ hγ1 hη0 hη1
      (qLbMDP_rowSpec γ hγ' hγ1) t htN hdec
    refine le_trans ?_ hmain
    -- arithmetic: (1/320)/(R log T) ≤ (5/1536) min(√x, 1)
    set R := Real.sqrt ((1 - γ) ^ 2 * T) with hR
    have hR4 : 4 ≤ R := by
      rw [hR, show (4 : ℝ) = Real.sqrt 16 by
        rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt hRT
    have hR2 : R ^ 2 = (1 - γ) ^ 2 * T := Real.sq_sqrt (by positivity)
    have hlog : 1 ≤ Real.log T := by
      rw [Real.le_log_iff_exp_le hTpos]
      have := Real.exp_one_lt_d9
      linarith
    have hRL : 1 ≤ R * Real.log T := by
      have := mul_le_mul hR4 hlog zero_le_one (by linarith)
      linarith
    have hsx : 2 / R ≤ Real.sqrt (η / (1 - γ)) := by
      rw [Real.le_sqrt (by positivity) (by positivity), div_pow, hR2,
        div_le_div_iff₀ (by positivity) hg]
      rw [div_lt_iff₀ (by positivity)] at hηlow
      have := mul_lt_mul_of_pos_left hηlow hg
      have e : η * ((1 - γ) ^ 2 * T) = (1 - γ) * (η * ((1 - γ) * T)) := by ring
      linarith
    have hinv : 1 / (R * Real.log T) ≤ 1 := by
      rw [div_le_one (by linarith)]; exact hRL
    have hinv2 : 1 / (R * Real.log T) ≤ 2 / R := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have := mul_le_mul_of_nonneg_left hlog (by linarith : (0 : ℝ) ≤ R)
      linarith
    have hmin : 1 / (R * Real.log T) ≤ min (Real.sqrt (η / (1 - γ))) 1 :=
      le_min (hinv2.trans hsx) hinv
    have e : 1 / 320 / (R * Real.log T) = 1 / 320 * (1 / (R * Real.log T)) := by ring
    rw [e]
    have h0 : 0 ≤ 1 / (R * Real.log T) := by positivity
    have := mul_le_mul_of_nonneg_left hmin (by norm_num : (0 : ℝ) ≤ 5 / 1536)
    linarith

end StatisticalRL.QLearning
