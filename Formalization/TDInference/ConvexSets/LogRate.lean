import Formalization.TDInference.ConvexSets.AllConvexRate
import Formalization.TDInference.RemainderTail

/-!
# Partial result toward Theorem 7.11 (not the printed result): the TD estimate over all convex sets at `T^{-1/4}`

Infrastructure for `thm:Berry-Esseen-linear` (`chapters/inference.tex:132–141`; `d_cvx` at
:124–127; `Λ⋆ = A⁻¹ΓA⁻ᵀ` at :104–117, with `Γ := Γ_true`, SOURCE-ISSUES C43).

**This is a partial result, not Theorem 7.11 and not a statement-index entry.** The printed theorem
bounds the convex distance between `√T Δ̄_T` and `N(0, Λ⋆)` by an explicit coefficient times
`T^{-1/3}` (plus `C̃ T^{-1/2}`). Here:
* the transfer theorem `abs_lawProb_convex_sub_gaussCov_le_of_linRate` turns a convex-set rate
  `K₁ T^{-a}` for the linearised statistic `linPart` (an explicit hypothesis, a genuine input that is
  not proved here for general `a`) into the rate `K (T^{-a} + T^{-1/3} log(2T))` for the full
  statistic; even its `a = 1/3` instance would give `T^{-1/3} log T`, which still carries a log
  factor compared with the printed `T^{-1/3}`;
* the unconditional corollary `abs_lawProb_convex_sub_gaussCov_le_quarter` uses the proved linear
  rate `a = 1/4` and gives `K T^{-1/4}`, weaker than the printed `T^{-1/3}` (it improves the
  `T^{-2/9}` bound of `TDInference/ConvexSets/AllConvexRate.lean`);
* the constants are instance constants (they may depend on `M, π, μ, η₀, V₀`), not the printed
  coefficient times a universal constant;
* the covariance is the corrected `Γ_true` (SOURCE-ISSUES C43);
* the hypothesis `η₀ ≤ 1` is weaker than the printed `η₀ < 1/4`.

Route: write `√T Δ̄_T = linPart + R`. Sandwich `C` between its inner parallel set and its
`δ`-thickening (`abs_sum_indicator_sub_le_of_perturb`) with
`δ = K_R T^{-1/3} log(2T)`, `K_R = remTailConst`. The Gaussian `δ`-shell costs `≤ c δ`
(`tdGaussCov_convexShell_le_diagMin`); the event `‖R‖_∞ > δ` has probability `≤ 3|S|/T`
(`pathProb_le_norm_remainder_le_rate`, exponential Azuma tail), and
`1/T ≤ T^{-1/3} log(2T) / log 2`.
-/

open Finset Matrix MeasureTheory Metric
open scoped BigOperators

namespace StatisticalRL.Ch7Rest.TDInference

open StatisticalRL.Probability StatisticalRL.Analysis

variable {State Action : Type} [Fintype State] [Fintype Action] [DecidableEq State]

/-! ## Rate arithmetic -/

omit [Fintype State] [DecidableEq State] in
/-- `log(2T) ≥ log 2 > 0` for `T ≥ 1`. -/
theorem log_two_le_log_two_mul {T : ℕ} (hT : 1 ≤ T) : Real.log 2 ≤ Real.log (2 * T) := by
  have hT1 : (1 : ℝ) ≤ T := by exact_mod_cast hT
  exact Real.log_le_log (by norm_num) (by linarith)

omit [Fintype State] [DecidableEq State] in
/-- `1/T ≤ T^{-1/3} log(2T) / log 2` for `T ≥ 1`. -/
theorem inv_le_rpow_neg_third_mul_log_div {T : ℕ} (hT : 1 ≤ T) :
    (T : ℝ)⁻¹ ≤ (T : ℝ) ^ (-(1 / 3 : ℝ)) * Real.log (2 * T) / Real.log 2 := by
  have hT1 : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hT0 : (0 : ℝ) < T := by linarith
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h1 : (T : ℝ)⁻¹ ≤ (T : ℝ) ^ (-(1 / 3 : ℝ)) := by
    rw [← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le hT1 (by norm_num)
  have h2 : 1 ≤ Real.log (2 * T) / Real.log 2 :=
    (one_le_div hl2).2 (log_two_le_log_two_mul hT)
  have hr : 0 ≤ (T : ℝ) ^ (-(1 / 3 : ℝ)) := Real.rpow_nonneg hT0.le _
  rw [mul_div_assoc]
  calc (T : ℝ)⁻¹ ≤ (T : ℝ) ^ (-(1 / 3 : ℝ)) := h1
    _ = (T : ℝ) ^ (-(1 / 3 : ℝ)) * 1 := (mul_one _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left h2 hr

omit [Fintype State] [DecidableEq State] in
/-- `T^{-1/3} log(2T) ≤ 13 T^{-1/4}` for `T ≥ 1` (from `log T ≤ 12 T^{1/12}`, `log 2 ≤ 1`). -/
theorem rpow_neg_third_mul_log_two_mul_le {T : ℕ} (hT : 1 ≤ T) :
    (T : ℝ) ^ (-(1 / 3 : ℝ)) * Real.log (2 * T) ≤ 13 * (T : ℝ) ^ (-(1 / 4 : ℝ)) := by
  have hT1 : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hT0 : (0 : ℝ) < T := by linarith
  have hlog : Real.log (2 * T) = Real.log 2 + Real.log T :=
    Real.log_mul (by norm_num) hT0.ne'
  have hl2 : Real.log 2 ≤ 1 := by
    have := Real.log_two_lt_d9; linarith
  have hu : 1 ≤ (T : ℝ) ^ (1 / 12 : ℝ) := Real.one_le_rpow hT1 (by norm_num)
  have hlT : Real.log T ≤ (T : ℝ) ^ (1 / 12 : ℝ) / (1 / 12) :=
    Real.log_le_rpow_div hT0.le (by norm_num)
  have hL : Real.log (2 * T) ≤ 13 * (T : ℝ) ^ (1 / 12 : ℝ) := by
    rw [hlog]
    have : (T : ℝ) ^ (1 / 12 : ℝ) / (1 / 12) = 12 * (T : ℝ) ^ (1 / 12 : ℝ) := by ring
    linarith
  have hr : 0 ≤ (T : ℝ) ^ (-(1 / 3 : ℝ)) := Real.rpow_nonneg hT0.le _
  have he : (T : ℝ) ^ (-(1 / 3 : ℝ)) * (T : ℝ) ^ (1 / 12 : ℝ) = (T : ℝ) ^ (-(1 / 4 : ℝ)) := by
    rw [← Real.rpow_add hT0]; norm_num
  calc (T : ℝ) ^ (-(1 / 3 : ℝ)) * Real.log (2 * T)
      ≤ (T : ℝ) ^ (-(1 / 3 : ℝ)) * (13 * (T : ℝ) ^ (1 / 12 : ℝ)) :=
        mul_le_mul_of_nonneg_left hL hr
    _ = 13 * ((T : ℝ) ^ (-(1 / 3 : ℝ)) * (T : ℝ) ^ (1 / 12 : ℝ)) := by ring
    _ = 13 * (T : ℝ) ^ (-(1 / 4 : ℝ)) := by rw [he]

/-! ## The remainder tail in sum form -/

omit [DecidableEq State] in
/-- `0 ≤ remTailConst` for `0 < μmin`, `0 < η₀`. -/
theorem remTailConst_nonneg (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (V₀ : State → ℝ) {μmin η₀ : ℝ} (hμmin0 : 0 < μmin) (h0 : 0 < η₀) :
    0 ≤ remTailConst M π V₀ μmin η₀ := by
  have hK := (linWeightConst_pos M hμmin0 h0).le
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [remTailConst]
  exact add_nonneg (div_nonneg (mul_nonneg hK (norm_nonneg _)) (by positivity))
    (Real.sqrt_nonneg _)

/-- **Remainder tail, sum form.** For `T ≥ 1` and `δ = K_R T^{-1/3} log(2T)`:
`P(‖√TΔ̄_T − linPart‖_∞ > δ) ≤ 3|S|/T` (the strict event is contained in the `≤` event of
`pathProb_le_norm_remainder_le_rate`). -/
theorem sum_pathWeight_remainder_tail_le_rate (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) {η₀ μmin : ℝ}
    (h0 : 0 < η₀) (h1 : η₀ ≤ 1) (hμmin0 : 0 < μmin) (hμmin : ∀ s, μmin ≤ μ.prob s)
    (V₀ : State → ℝ) {T : ℕ} (hT : 1 ≤ T) :
    ∑ ω : Fin T → Tuple State Action, pathWeight M π μ ω *
        (if remTailConst M π V₀ μmin η₀ * (T : ℝ) ^ (-(1 / 3 : ℝ)) * Real.log (2 * T) <
            ‖scaledError M π η₀ V₀ ω - linPart M π μ η₀ ω‖ then (1 : ℝ) else 0) ≤
      3 * Fintype.card State / T := by
  refine le_trans ?_ (pathProb_le_norm_remainder_le_rate M π μ h0 h1 hμmin0 hμmin V₀ hT)
  rw [pathProb]
  refine sum_le_sum fun ω _ ↦ mul_le_mul_of_nonneg_left ?_ (pathWeight_nonneg M π μ ω)
  split_ifs with h
  · rw [Set.indicator_of_mem (show ω ∈ {ω : Fin T → Tuple State Action |
      remTailConst M π V₀ μmin η₀ * (T : ℝ) ^ (-(1 / 3 : ℝ)) * Real.log (2 * T) ≤
        ‖scaledError M π η₀ V₀ ω - linPart M π μ η₀ ω‖} from h.le)]
  · exact Set.indicator_nonneg (fun _ _ ↦ zero_le_one) _

/-! ## Main exports -/

/-- **Partial result toward Theorem 7.11 (not the printed result): transfer of a convex-set rate
from the linear part to `√T Δ̄_T`, with a log-loss remainder** (infrastructure, **partial, not the
printed result**, no statement-index entry).

For full-support `μ`, `0 < η₀ ≤ 1`, every `V₀` and `Γ_true ≻ 0`: **if** (explicit input
hypothesis `hlin`, not proved here for general `a`) the linearised statistic `linPart` satisfies
`|P(linPart_T ∈ C) − N(0, A⁻¹ diag(Γ_true) A⁻ᵀ)(C)| ≤ K₁ T^{-a}` for all `T ≥ 1` and convex `C`,
then there is an instance constant `K > 0` with
`|P(√T Δ̄_T ∈ C) − N(0, A⁻¹ diag(Γ_true) A⁻ᵀ)(C)| ≤ K (T^{-a} + T^{-1/3} log(2T))`
for all `T ≥ 1` and convex `C` (measurable or not; `gaussCov.real` is the outer measure).
No restriction on `a` is needed.

Differences from `thm:Berry-Esseen-linear` (`chapters/inference.tex:132–141`): conditional on the
linear-part rate; even for `a = 1/3` the rate is `T^{-1/3} log T`, not `T^{-1/3}`; instance
constant; covariance `Γ_true` (SOURCE-ISSUES C43). -/
theorem abs_lawProb_convex_sub_gaussCov_le_of_linRate [Nonempty State]
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (μ : FiniteDistribution State) {η₀ : ℝ} (h0 : 0 < η₀) (h1 : η₀ ≤ 1) (V₀ : State → ℝ)
    (hμ : ∀ s, 0 < μ.prob s) (hΓ : ∀ s, 0 < trueGamma M π μ s) (a : ℝ)
    (hlin : ∃ K₁ : ℝ, ∀ T : ℕ, 1 ≤ T → ∀ C : Set (State → ℝ), Convex ℝ C →
      |∑ ω : Fin T → Tuple State Action,
          pathWeight M π μ ω * C.indicator (fun _ ↦ (1 : ℝ)) (linPart M π μ η₀ ω) -
          (gaussCov (tdA M π μ) (trueGamma M π μ)).real C| ≤
        K₁ * (T : ℝ) ^ (-a)) :
    ∃ K : ℝ, 0 < K ∧ ∀ T : ℕ, 1 ≤ T → ∀ C : Set (State → ℝ), Convex ℝ C →
      |lawProb M π μ η₀ V₀ T C - (gaussCov (tdA M π μ) (trueGamma M π μ)).real C| ≤
        K * ((T : ℝ) ^ (-a) + (T : ℝ) ^ (-(1 / 3 : ℝ)) * Real.log (2 * T)) := by
  obtain ⟨K₁, hK₁⟩ := hlin
  set μmin := diagMin μ.prob
  have hμmin0 : 0 < μmin := (Finset.lt_inf'_iff _).2 fun s _ ↦ hμ s
  have hμmin : ∀ s, μmin ≤ μ.prob s := fun s ↦ Finset.inf'_le _ (mem_univ s)
  set Csh := 4 * (Fintype.card State : ℝ) ^ 2 * (2 / Real.sqrt (diagMin (trueGamma M π μ))) /
    Real.sqrt (2 * Real.pi) with hCsh
  set KR := remTailConst M π V₀ μmin η₀
  have hKR : 0 ≤ KR := remTailConst_nonneg M π V₀ hμmin0 h0
  have hCsh0 : 0 ≤ Csh := by rw [hCsh]; positivity
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set Q := 3 * (Fintype.card State : ℝ) / Real.log 2 with hQ
  have hQ0 : 0 ≤ Q := by rw [hQ]; positivity
  refine ⟨|K₁| + Csh * KR + Q + 1, by positivity, fun T hT C hC ↦ ?_⟩
  have hT1 : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hT0 : (0 : ℝ) < T := by linarith
  set L := (T : ℝ) ^ (-(1 / 3 : ℝ)) * Real.log (2 * T) with hL_def
  have hL0 : 0 ≤ L :=
    mul_nonneg (Real.rpow_nonneg hT0.le _) ((Real.log_pos (by linarith)).le)
  have hTa : 0 ≤ (T : ℝ) ^ (-a) := Real.rpow_nonneg hT0.le _
  set δ := KR * (T : ℝ) ^ (-(1 / 3 : ℝ)) * Real.log (2 * T) with hδ_def
  have hδL : δ = KR * L := by rw [hδ_def, hL_def]; ring
  have hδ : 0 ≤ δ := by rw [hδL]; exact mul_nonneg hKR hL0
  have hw := pathWeight_nonneg M π μ (T := T)
  have hsh := tdGaussCov_convexShell_le_diagMin M π μ hμmin0 hμmin hΓ hC hδ
  have hq := sum_pathWeight_remainder_tail_le_rate M π μ h0 h1 hμmin0 hμmin V₀ hT
  have hmain := abs_sum_indicator_sub_le_of_perturb hw
    (fun ω ↦ scaledError M π η₀ V₀ ω) (fun ω ↦ linPart M π μ η₀ ω)
    (gaussCov (tdA M π μ) (trueGamma M π μ)) (fun K hK ↦ hK₁ T hT K hK) hC hsh hq
  have e1 : 4 * (Fintype.card State : ℝ) ^ 2 * (2 / Real.sqrt (diagMin (trueGamma M π μ))) * δ /
      Real.sqrt (2 * Real.pi) = Csh * KR * L := by rw [hCsh, hδL]; ring
  rw [e1] at hmain
  have hq2 : 3 * (Fintype.card State : ℝ) / T ≤ Q * L := by
    have hi := inv_le_rpow_neg_third_mul_log_div hT
    have hS : 0 ≤ 3 * (Fintype.card State : ℝ) := by positivity
    calc 3 * (Fintype.card State : ℝ) / T = 3 * (Fintype.card State : ℝ) * (T : ℝ)⁻¹ :=
          div_eq_mul_inv _ _
      _ ≤ 3 * (Fintype.card State : ℝ) * (L / Real.log 2) := by
          rw [hL_def]; exact mul_le_mul_of_nonneg_left hi hS
      _ = Q * L := by rw [hQ]; ring
  have hk : K₁ * (T : ℝ) ^ (-a) ≤ |K₁| * (T : ℝ) ^ (-a) :=
    mul_le_mul_of_nonneg_right (le_abs_self _) hTa
  refine hmain.trans ?_
  have hexp : (|K₁| + Csh * KR + Q + 1) * ((T : ℝ) ^ (-a) + L) =
      |K₁| * (T : ℝ) ^ (-a) + Csh * KR * L + Q * L +
        (|K₁| * L + Csh * KR * (T : ℝ) ^ (-a) + Q * (T : ℝ) ^ (-a) + (T : ℝ) ^ (-a) + L) := by
    ring
  rw [hexp]
  have hrest : 0 ≤ |K₁| * L + Csh * KR * (T : ℝ) ^ (-a) + Q * (T : ℝ) ^ (-a) +
      (T : ℝ) ^ (-a) + L := by positivity
  linarith

/-- **Partial result toward Theorem 7.11 (not the printed result): all convex sets at the weaker
rate `T^{-1/4}`** (infrastructure, **partial, not the printed result**, no statement-index entry).
For full-support `μ`, `0 < η₀ ≤ 1`, every initial value `V₀` and `Γ_true ≻ 0`, there is an
instance constant `K > 0` (depending on `M, π, μ, η₀, V₀`) such that for every `T ≥ 1` and every
convex `C ⊆ ℝ^S` (measurable or not; `gaussCov.real` is the outer measure)
`|P(√T Δ̄_T ∈ C) − N(0, A⁻¹ diag(Γ_true) A⁻ᵀ)(C)| ≤ K T^{-1/4}`.

This improves the `T^{-2/9}` bound `abs_lawProb_convex_sub_gaussCov_le_twoNinths`. Differences from
`thm:Berry-Esseen-linear` (`chapters/inference.tex:132–141`): the rate is `T^{-1/4}` instead of
`T^{-1/3}`; the constant is an instance constant instead of the printed coefficient; the
covariance uses `Γ_true` (SOURCE-ISSUES C43). -/
theorem abs_lawProb_convex_sub_gaussCov_le_quarter [Nonempty State]
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (μ : FiniteDistribution State) {η₀ : ℝ} (h0 : 0 < η₀) (h1 : η₀ ≤ 1) (V₀ : State → ℝ)
    (hμ : ∀ s, 0 < μ.prob s) (hΓ : ∀ s, 0 < trueGamma M π μ s) :
    ∃ K : ℝ, 0 < K ∧ ∀ T : ℕ, 1 ≤ T → ∀ C : Set (State → ℝ), Convex ℝ C →
      |lawProb M π μ η₀ V₀ T C - (gaussCov (tdA M π μ) (trueGamma M π μ)).real C| ≤
        K * (T : ℝ) ^ (-(1 / 4 : ℝ)) := by
  obtain ⟨K₁, -, hlin⟩ := abs_linLaw_convex_sub_gaussCov_le_quarter M π μ h0 h1 hμ hΓ
  obtain ⟨K, hK, hmain⟩ := abs_lawProb_convex_sub_gaussCov_le_of_linRate M π μ h0 h1 V₀ hμ hΓ
    (1 / 4) ⟨K₁, hlin⟩
  refine ⟨14 * K, by positivity, fun T hT C hC ↦ (hmain T hT C hC).trans ?_⟩
  have h13 := rpow_neg_third_mul_log_two_mul_le hT
  calc K * ((T : ℝ) ^ (-(1 / 4 : ℝ)) + (T : ℝ) ^ (-(1 / 3 : ℝ)) * Real.log (2 * T))
      ≤ K * ((T : ℝ) ^ (-(1 / 4 : ℝ)) + 13 * (T : ℝ) ^ (-(1 / 4 : ℝ))) :=
        mul_le_mul_of_nonneg_left (by linarith) hK.le
    _ = 14 * K * (T : ℝ) ^ (-(1 / 4 : ℝ)) := by ring

end StatisticalRL.Ch7Rest.TDInference
