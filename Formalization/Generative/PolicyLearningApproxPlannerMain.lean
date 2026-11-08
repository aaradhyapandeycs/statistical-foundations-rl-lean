import Formalization.Generative.PolicyLearningApproxPlanner
import Formalization.Generative.PolicyLearningMainSample

/-! # Theorem 3.2 with an approximate empirical planner: main sample budget

Source: prose claim `source/upstream/tex/chapters/generative_model_model_based.tex:943`
after `Thm:sample-compl-main` (MB:900–923). The printed budget with the same
constant `10240` as `mainSample_policyLearning` suffices. The exact-optimal
singleton-state branch of `mainSample_policyLearning` is not reused; instead the
proof splits on `|S|·|A| ≤ 1` (only one deterministic policy) versus
`|S|·|A| ≥ 2` (the general log comparison needs only `|S|·|A|·N ≥ 2`). -/

open MeasureTheory ProbabilityTheory
namespace StatisticalRL.ModelBasedPolicyLearning
open StatisticalRL.DiscountedMDP
variable {State Action : Type*} [Fintype State] [Fintype Action]
local instance approxPlannerMainStateMeasurable : MeasurableSpace State := ⊤

/-- Scalar radius bound in the shared scale `q = √x`, using the sharp
threshold `x h² ≤ 1/720` (from `720β ≤ N(1−γ)`):
`√(720x) + (2√(4x) + 12xh) + η ≤ 32√x` whenever `η ≤ x h²/β`. -/
theorem approxPlanner_radius_le (x h β η : ℝ) (hx : 0 ≤ x) (hh : 0 ≤ h) (hh1 : h ≤ 1)
    (hβ : 4 ≤ β) (hsmall : x * h ^ 2 ≤ 1 / 720) (hη : η ≤ x * h ^ 2 / β) :
    Real.sqrt (720 * x) + (2 * Real.sqrt (4 * x) + 12 * (x * h)) + η ≤
      32 * Real.sqrt x := by
  have hs16 : x * h ^ 2 ≤ 1 / 16 := by linarith
  have h27 := (sourceEvaluation_radius_le x h hx hh hs16).1
  have hq : 0 ≤ Real.sqrt x := Real.sqrt_nonneg _
  have hq2 : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx
  have hv : Real.sqrt (4 * x) = 2 * Real.sqrt x := by
    rw [Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num)]
  have hxh : 0 ≤ x * h := mul_nonneg hx hh
  have hxh2 : (x * h) ^ 2 ≤ x / 720 := by
    have hm := mul_le_mul_of_nonneg_left hsmall hx
    nlinarith
  have h12 : 12 * (x * h) ≤ Real.sqrt x / 2 := by
    nlinarith [mul_nonneg hxh hq]
  have hy : 0 ≤ x * h ^ 2 := by positivity
  have hy2 : (x * h ^ 2) ^ 2 ≤ x / 720 := by
    have hh2 : h ^ 2 ≤ 1 := by nlinarith
    have hm := mul_le_mul_of_nonneg_left hsmall hx
    have hm2 := mul_le_mul_of_nonneg_left hh2 (mul_nonneg hx hy)
    have he : (x * h ^ 2) ^ 2 = x * (x * h ^ 2) * h ^ 2 := by ring
    nlinarith
  have hyq : x * h ^ 2 ≤ Real.sqrt x / 26 := by
    nlinarith [mul_nonneg hy hq]
  have hηq : η ≤ Real.sqrt x / 104 := by
    have : x * h ^ 2 / β ≤ x * h ^ 2 / 4 := div_le_div_of_nonneg_left hy (by norm_num) hβ
    linarith
  rw [hv]
  linarith

/-- The source-scale radius `r₀ + r₁′ + 1/(N(1−γ))`, with `r₁′` computed from
`2β`, is at most `ε` under the threshold and accuracy supplied by
`mainSample_scalar_bounds` from the budget with constant `10240`. -/
theorem approxPlanner_source_radius_le (h β n ε : ℝ) (hh : 0 < h) (hh1 : h ≤ 1)
    (hβ : 4 ≤ β) (hn : 0 < n) (hcut : 720 * β ≤ n * h)
    (herr : 32 * Real.sqrt (β / (n * h ^ 3)) ≤ ε) :
    Real.sqrt (720 * β / (n * h ^ 3)) +
      (2 * Real.sqrt (2 * (2 * β) / (n * h ^ 3)) + 6 * (2 * β) / (n * h ^ 2)) +
      1 / (n * h) ≤ ε := by
  have hβ0 : 0 < β := by linarith
  have hx0 : 0 ≤ β / (n * h ^ 3) := by positivity
  have e1 : 720 * β / (n * h ^ 3) = 720 * (β / (n * h ^ 3)) := by ring
  have e2 : 2 * (2 * β) / (n * h ^ 3) = 4 * (β / (n * h ^ 3)) := by ring
  have e3 : 6 * (2 * β) / (n * h ^ 2) = 12 * (β / (n * h ^ 3) * h) := by
    field_simp
    norm_num
  have e4 : 1 / (n * h) = β / (n * h ^ 3) * h ^ 2 / β := by
    field_simp
  have hsmall : β / (n * h ^ 3) * h ^ 2 ≤ 1 / 720 := by
    have he : β / (n * h ^ 3) * h ^ 2 = β / (n * h) := by
      field_simp
    rw [he, div_le_iff₀ (by positivity)]
    linarith
  rw [e1, e2, e3, e4]
  exact (approxPlanner_radius_le (β / (n * h ^ 3)) h β _ hx0 hh.le hh1 hβ hsmall
    le_rfl).trans herr

/-- **Theorem 3.2 with an approximate planner (MB:943).** The printed budget,
with the same constant `10240`, yields the source V and Q performance bounds
simultaneously for every deterministic policy whose empirical value is within
`1/(N(1−γ))` of the empirical optimal value `V̂⋆` in sup norm. -/
theorem mainSample_policyLearning_approx (M : DiscountedMDP State Action)
    (N : ℕ) (hN : 0 < N) (δ ε : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hε : 0 < ε) (hεmax : ε ≤ 1 / (1 - M.discount))
    (hbudget : 10240 * Real.log (Fintype.card State * Fintype.card Action * N /
      ((1 - M.discount) ^ 2 * ε * δ)) / ((1 - M.discount) ^ 3 * ε ^ 2) ≤ N) :
    1 - δ < (samplingLaw M N).real {data |
      ∀ f : State → Action,
        ‖valueEstimator M N hN data - (empiricalModel M N hN data).trajectoryExpectedValue
          (fun t ↦ EnvironmentStage.pointMass (f t))‖ ≤ 1 / (N * (1 - M.discount)) →
        (∀ s, M.trajectoryExpectedValue M.optimalGreedyPolicy s - ε ≤
          M.trajectoryExpectedValue (fun t ↦ EnvironmentStage.pointMass (f t)) s) ∧
        (∀ s a, M.trajectoryExpectedQ M.optimalGreedyPolicy s a - M.discount * ε ≤
          M.trajectoryExpectedQ (fun t ↦ EnvironmentStage.pointMass (f t)) s a)} := by
  classical
  letI : Nonempty State := M.state_nonempty
  letI : Nonempty Action := M.action_nonempty
  by_cases hSA : Fintype.card State * Fintype.card Action ≤ 1
  · -- Only one deterministic policy: it is the exact empirical optimum.
    have hSpos : 0 < Fintype.card State := Fintype.card_pos
    have hA1 : Fintype.card Action ≤ 1 :=
      (Nat.le_mul_of_pos_left _ hSpos).trans hSA
    letI : Subsingleton Action := Fintype.card_le_one_iff_subsingleton.mp hA1
    have hold := mainSample_policyLearning M N hN δ ε hδ hδ1 hε hεmax hbudget
    apply hold.trans_le
    apply measureReal_mono _ (measure_ne_top (samplingLaw M N) _)
    intro data hd f _
    have hf : f = policyEstimator M N hN data := funext fun _ ↦ Subsingleton.elim _ _
    subst hf
    exact hd _ (policyEstimator_empiricallyOptimal M N hN data)
  · have hSAn : 2 ≤ Fintype.card State * Fintype.card Action := by omega
    have hSA2 : (2 : ℝ) ≤ (Fintype.card State : ℝ) * Fintype.card Action := by
      exact_mod_cast hSAn
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have hn : (0 : ℝ) < N := by exact_mod_cast hN
    have hK : 2 ≤ (Fintype.card State : ℝ) * Fintype.card Action * N := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hN1)
        (show 0 ≤ (Fintype.card State : ℝ) * Fintype.card Action by positivity)]
    have hh : 0 < 1 - M.discount := sub_pos.mpr M.discount_lt_one
    have hh1 : 1 - M.discount ≤ 1 := by linarith [M.discount_nonneg]
    let β := leaveOneOutBeta M N δ
    let L := Real.log (Fintype.card State * Fintype.card Action * N /
      ((1 - M.discount) ^ 2 * ε * δ))
    have hlog := mainSample_log_comparison (1 - M.discount) ε δ
      ((Fintype.card State : ℝ) * Fintype.card Action * N) hh hh1 hε hδ hδ1 hεmax hK
    have hβL : β ≤ 10 * L := by
      dsimp [β, L, leaveOneOutBeta]
      convert hlog using 1
      congr 2
      ring
    have hβ4 : 4 ≤ leaveOneOutBeta M N δ := leaveOneOutBeta_ge_four M N hN δ hδ hδ1
    have hβ : 0 ≤ β := le_trans (by norm_num) hβ4
    have hb : 10240 * L / ((1 - M.discount) ^ 3 * ε ^ 2) ≤ N := hbudget
    have hmain := mainSample_scalar_bounds (1 - M.discount) ε β L N hh hε hεmax hβ hβL hb
    have hcut : 720 * leaveOneOutBeta M N δ / (1 - M.discount) ≤ N := hmain.1
    have hcut' : 720 * leaveOneOutBeta M N δ ≤ N * (1 - M.discount) :=
      (div_le_iff₀ hh).1 hcut
    have herr : 32 * Real.sqrt (leaveOneOutBeta M N δ / (N * (1 - M.discount) ^ 3)) ≤ ε :=
      hmain.2
    have hrad := approxPlanner_source_radius_le (1 - M.discount) (leaveOneOutBeta M N δ) N ε
      hh hh1 hβ4 hn hcut' herr
    have hjoint := joint_approxPlanner_event M N hN δ hδ hδ1 hcut
    apply hjoint.trans_le
    apply measureReal_mono _ (measure_ne_top (samplingLaw M N) _)
    intro data hd f hslack
    obtain ⟨_, hv, hQ⟩ := hd f (1 / (N * (1 - M.discount))) le_rfl hslack
    constructor
    · intro s
      linarith [(hv s).2]
    · intro s a
      have hq := (hQ s a).2
      have hm := mul_le_mul_of_nonneg_left hrad M.discount_nonneg
      linarith

/-- One explicit universal constant (`10240`, the same as for exact planning)
precedes every finite model and accuracy; positive `N` is the
sampling/log-domain condition. -/
theorem mainSample_policyLearning_approx_universal_constant :
    ∃ c₀ : ℝ, 0 < c₀ ∧
      ∀ (State Action : Type*) [Fintype State] [Fintype Action]
        (M : DiscountedMDP State Action) (N : ℕ) (hN : 0 < N) (δ ε : ℝ),
      0 < δ → δ < 1 → 0 < ε → ε ≤ 1 / (1 - M.discount) →
      c₀ * Real.log (Fintype.card State * Fintype.card Action * N /
        ((1 - M.discount) ^ 2 * ε * δ)) / ((1 - M.discount) ^ 3 * ε ^ 2) ≤ N →
      1 - δ < (samplingLaw M N).real {data |
        ∀ f : State → Action,
          ‖valueEstimator M N hN data - (empiricalModel M N hN data).trajectoryExpectedValue
            (fun t ↦ EnvironmentStage.pointMass (f t))‖ ≤ 1 / (N * (1 - M.discount)) →
          (∀ s, M.trajectoryExpectedValue M.optimalGreedyPolicy s - ε ≤
            M.trajectoryExpectedValue (fun t ↦ EnvironmentStage.pointMass (f t)) s) ∧
          (∀ s a, M.trajectoryExpectedQ M.optimalGreedyPolicy s a - M.discount * ε ≤
            M.trajectoryExpectedQ (fun t ↦ EnvironmentStage.pointMass (f t)) s a)} := by
  refine ⟨10240, by norm_num, ?_⟩
  intro State Action _ _ M N hN δ ε hδ hδ1 hε hεmax hbudget
  exact mainSample_policyLearning_approx M N hN δ ε hδ hδ1 hε hεmax hbudget

end StatisticalRL.ModelBasedPolicyLearning
