import Formalization.TDInference.LeaveOneOutBound

/-!
# Theorem 7.11 support: vector leave-one-out and remainder bounds for the TD statistic

Source: `thm:Berry-Esseen-linear`, `chapters/inference.tex:132–141`; the TD recursion and averages at
:52–64, :72, :82, :88; `η_t = η₀ t^{-2/3}` at :134. This module is library infrastructure toward the
all-convex-sets form of Theorem 7.11 at the printed rate `T^{-1/3}` (via a Shao–Zhang-type nonlinear
convex Berry–Esseen argument). **No source result is claimed here.**

Write `W = linPart = ∑_k ξ_k` with the independent summands `ξ_k = linSummand T k (ω k)`,
`D = √TΔ̄_T − W` (`scaledError − linPart`, the deterministic transient included), and for a sample
index `i` and replacement tuple `x⋆`, `D^{(i)}(ω) = D(ω[i ↦ x⋆])`, which does not depend on `ω i`.
Then `D − D^{(i)} = looRemainder i x⋆` (`looRemainder_eq_sub`). Let `S = |State|`,
`K_β = linWeightConst`, `B = tdNoiseBound`, `K_E = linRemainderConst`,
`K_CS = looChenShaoConst`. All bounds hold for `0 < η₀ ≤ 1`, `0 < μmin ≤ μ(s)`, `T ≥ 1`, every `V₀`
and every family of replacement tuples; the constants are free of `T`.

The vector bounds are reassembled coordinatewise from the per-coordinate `L²` estimates
`weightedL2_looRemainder_le` and `weightedL2_scaledError_sub_linPart_le`, through the `ℓ¹` norm
`∑_s |x s|`, which dominates both the sup norm and the Euclidean norm.

* `sum_looChenShao_vec_of_le`: the generic leave-one-out sum. If `F_i ≤ a T^{-1/2}K_β B` and
  `0 ≤ G_i ≤ b ∑_s |looRemainder_i(s)|`, then `∑_i E[F_i G_i] ≤ a b S K_CS T^{-1/3}`.
* `sum_looChenShao_norm_le` (sup norm): `∑_i E[‖ξ_i‖ ‖D − D^{(i)}‖] ≤ S K_CS T^{-1/3}`, and
  `sum_looChenShao_abs_norm_sub_le`: `∑_i E[‖ξ_i‖ |‖D‖ − ‖D^{(i)}‖|] ≤ S K_CS T^{-1/3}`.
* `sum_looChenShao_euclid_le`, `sum_looChenShao_abs_euclid_sub_le`: the Euclidean versions,
  constant `S² K_CS`; `sum_looChenShao_sumAbs_le`: the `ℓ¹` version, constant `S² K_CS`.
* `weightedL2_sumAbs_remainder_le`, `weightedL2_norm_remainder_le`,
  `sum_pathWeight_mul_norm_remainder_le`: `‖D‖` in `L²` and `L¹`, constant `S K_E`.
* `weightedL2_linPart_apply_le`: `‖W(s)‖_{L²} ≤ K_β B`; `sum_pathWeight_mul_norm_linPart_mul_le`:
  `E[‖W‖ ‖D‖] ≤ S² K_β B K_E T^{-1/3}` (sup norm), and the `ℓ¹` version
  `sum_pathWeight_mul_sumAbs_linPart_mul_le`; no Euclidean version is exported.
-/

open Finset Matrix
open scoped BigOperators

namespace StatisticalRL.Ch7Rest.TDInference

open StatisticalRL.Probability StatisticalRL.Analysis

variable {State Action : Type} [Fintype State] [Fintype Action]

/-! ## Norm comparisons on `State → ℝ` -/

/-- The sup norm is at most the `ℓ¹` norm. -/
theorem norm_le_sum_abs_apply (x : State → ℝ) : ‖x‖ ≤ ∑ s, |x s| := by
  refine (pi_norm_le_iff_of_nonneg (sum_nonneg fun s _ ↦ abs_nonneg _)).2 fun s ↦ ?_
  rw [Real.norm_eq_abs]
  exact single_le_sum (f := fun s ↦ |x s|) (fun s _ ↦ abs_nonneg _) (mem_univ s)

/-- The Euclidean norm is at most the `ℓ¹` norm. -/
theorem norm_toLp_two_le_sum_abs (x : State → ℝ) :
    ‖(WithLp.toLp 2 x : EuclideanSpace ℝ State)‖ ≤ ∑ s, |x s| := by
  rw [EuclideanSpace.norm_eq]
  calc √(∑ s, ‖(WithLp.toLp 2 x : EuclideanSpace ℝ State) s‖ ^ 2) = √(∑ s, |x s| ^ 2) := by
        simp [Real.norm_eq_abs]
    _ ≤ √((∑ s, |x s|) ^ 2) :=
        Real.sqrt_le_sqrt (sum_sq_le_sq_sum_of_nonneg fun s _ ↦ abs_nonneg _)
    _ = ∑ s, |x s| := Real.sqrt_sq (sum_nonneg fun s _ ↦ abs_nonneg _)

/-! ## The summands -/

/-- `‖ξ_k‖_∞ ≤ T^{-1/2} K_β B`. -/
theorem norm_linSummand_le_inv_sqrt [DecidableEq State] (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) {η₀ : ℝ} (h0 : 0 < η₀)
    (h1 : η₀ ≤ 1) {μmin : ℝ} (hμmin0 : 0 < μmin) (hμmin : ∀ s, μmin ≤ μ.prob s) (T k : ℕ)
    (x : Tuple State Action) :
    ‖linSummand M π μ η₀ T k x‖ ≤
      (Real.sqrt T)⁻¹ * (linWeightConst M μmin η₀ * tdNoiseBound M π) := by
  have hsT : 0 ≤ (Real.sqrt T)⁻¹ := inv_nonneg.2 (Real.sqrt_nonneg _)
  rw [linSummand, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg hsT]
  exact mul_le_mul_of_nonneg_left ((norm_linWeight_mulVec_le M π μ h0 h1 hμmin0 hμmin T k _).trans
    (mul_le_mul_of_nonneg_left (norm_noiseVec_le M π x) (linWeightConst_nonneg M hμmin0 h0))) hsT

/-- `‖ξ_k‖₁ ≤ S T^{-1/2} K_β B`. -/
theorem sum_abs_linSummand_le [DecidableEq State] (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) {η₀ : ℝ} (h0 : 0 < η₀)
    (h1 : η₀ ≤ 1) {μmin : ℝ} (hμmin0 : 0 < μmin) (hμmin : ∀ s, μmin ≤ μ.prob s) (T k : ℕ)
    (x : Tuple State Action) :
    ∑ s, |linSummand M π μ η₀ T k x s| ≤
      Fintype.card State * ((Real.sqrt T)⁻¹ * (linWeightConst M μmin η₀ * tdNoiseBound M π)) := by
  calc ∑ s, |linSummand M π μ η₀ T k x s|
      ≤ ∑ _s : State, (Real.sqrt T)⁻¹ * (linWeightConst M μmin η₀ * tdNoiseBound M π) :=
        sum_le_sum fun s _ ↦ by
          rw [← Real.norm_eq_abs]
          exact (norm_le_pi_norm _ s).trans
            (norm_linSummand_le_inv_sqrt M π μ h0 h1 hμmin0 hμmin T k x)
    _ = _ := by rw [sum_const, card_univ, nsmul_eq_mul]

/-! ## The leave-one-out differences -/

/-- `D(ω) − D(ω[i ↦ x⋆]) = looRemainder i x⋆ ω`, with `D = √TΔ̄_T − linPart`. -/
theorem looRemainder_eq_sub [DecidableEq State] (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) (η₀ : ℝ) (V₀ : State → ℝ)
    {T : ℕ} (i : Fin T) (xs : Tuple State Action) (ω : Fin T → Tuple State Action) :
    looRemainder M π μ η₀ V₀ i xs ω =
      (scaledError M π η₀ V₀ ω - linPart M π μ η₀ ω) -
        (scaledError M π η₀ V₀ (Function.update ω i xs) -
          linPart M π μ η₀ (Function.update ω i xs)) := by
  rw [looRemainder, sub_sub_sub_comm]

/-- `E‖D − D^{(i)}‖₁ ≤ S K_loo T^{-1/2} √η'_i`. -/
theorem sum_pathWeight_mul_sum_abs_looRemainder_le [DecidableEq State]
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (μ : FiniteDistribution State) {η₀ : ℝ} (h0 : 0 < η₀) (h1 : η₀ ≤ 1) (V₀ : State → ℝ)
    {μmin : ℝ} (hμmin0 : 0 < μmin) (hμmin : ∀ s, μmin ≤ μ.prob s) {T : ℕ} (i : Fin T)
    (xs : Tuple State Action) :
    ∑ ω : Fin T → Tuple State Action, pathWeight M π μ ω *
        ∑ s, |looRemainder M π μ η₀ V₀ i xs ω s| ≤
      Fintype.card State *
        (looConst M π V₀ μmin η₀ * ((Real.sqrt T)⁻¹ * Real.sqrt (stepSize η₀ (i + 1)))) := by
  calc ∑ ω : Fin T → Tuple State Action, pathWeight M π μ ω *
        ∑ s, |looRemainder M π μ η₀ V₀ i xs ω s|
      = ∑ s, ∑ ω : Fin T → Tuple State Action, pathWeight M π μ ω *
          |looRemainder M π μ η₀ V₀ i xs ω s| := by
        simp_rw [mul_sum]; exact sum_comm
    _ ≤ ∑ _s : State,
          looConst M π V₀ μmin η₀ * ((Real.sqrt T)⁻¹ * Real.sqrt (stepSize η₀ (i + 1))) :=
        sum_le_sum fun s _ ↦ (sum_pathWeight_mul_abs_le_weightedL2 M π μ _).trans
          (weightedL2_looRemainder_le M π μ h0 h1 V₀ hμmin0 hμmin i xs s)
    _ = _ := by rw [sum_const, card_univ, nsmul_eq_mul]

/-- `∑_{i<T} T⁻¹ √η'_i ≤ (3/2) √η₀ T^{-1/3}`. -/
theorem sum_fin_inv_mul_sqrt_stepSize_le (η₀ : ℝ) {T : ℕ} (hT : 1 ≤ T) :
    ∑ i : Fin T, (T : ℝ)⁻¹ * Real.sqrt (stepSize η₀ (i + 1)) ≤
      3 / 2 * Real.sqrt η₀ * (T : ℝ) ^ (-(1 / 3 : ℝ)) := by
  rw [← mul_sum, Fin.sum_univ_eq_sum_range (fun i ↦ Real.sqrt (stepSize η₀ (i + 1))),
    ← natCubeRoot_sq_div hT]
  have hT0 : (0 : ℝ) ≤ (T : ℝ)⁻¹ := inv_nonneg.2 (Nat.cast_nonneg _)
  calc (T : ℝ)⁻¹ * ∑ i ∈ range T, Real.sqrt (stepSize η₀ (i + 1))
      ≤ (T : ℝ)⁻¹ * (3 / 2 * Real.sqrt η₀ * natCubeRoot T ^ 2) :=
        mul_le_mul_of_nonneg_left (sum_range_sqrt_stepSize_le η₀ T) hT0
    _ = 3 / 2 * Real.sqrt η₀ * (natCubeRoot T ^ 2 / T) := by ring

/-- **Generic vector leave-one-out sum.** For `0 < η₀ ≤ 1`, `0 < μmin ≤ μ(s)`, `T ≥ 1`, every `V₀`
and replacement tuples `x⋆_i`: if `F_i(ω) ≤ a T^{-1/2} K_β B` and
`0 ≤ G_i(ω) ≤ b ∑_s |looRemainder_i(x⋆_i)(ω)(s)|` with `a, b ≥ 0`, then
`∑_i E[F_i G_i] ≤ a b S K_CS T^{-1/3}`. -/
theorem sum_looChenShao_vec_of_le [DecidableEq State] (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) {η₀ : ℝ} (h0 : 0 < η₀)
    (h1 : η₀ ≤ 1) (V₀ : State → ℝ) {μmin : ℝ} (hμmin0 : 0 < μmin)
    (hμmin : ∀ s, μmin ≤ μ.prob s) {T : ℕ} (hT : 1 ≤ T) (xs : Fin T → Tuple State Action)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (F G : Fin T → (Fin T → Tuple State Action) → ℝ)
    (hF : ∀ i ω, F i ω ≤ a * ((Real.sqrt T)⁻¹ * (linWeightConst M μmin η₀ * tdNoiseBound M π)))
    (hG0 : ∀ i ω, 0 ≤ G i ω)
    (hG : ∀ i ω, G i ω ≤ b * ∑ s, |looRemainder M π μ η₀ V₀ i (xs i) ω s|) :
    ∑ i : Fin T, ∑ ω : Fin T → Tuple State Action, pathWeight M π μ ω * (F i ω * G i ω) ≤
      a * b * Fintype.card State * looChenShaoConst M π V₀ μmin η₀ *
        (T : ℝ) ^ (-(1 / 3 : ℝ)) := by
  set K := linWeightConst M μmin η₀
  set B := tdNoiseBound M π
  set L := looConst M π V₀ μmin η₀
  set S : ℝ := (Fintype.card State : ℝ)
  have hK0 : 0 ≤ K := linWeightConst_nonneg M hμmin0 h0
  have hB0 : 0 < B := tdNoiseBound_pos M π
  have hL0 : 0 ≤ L := looConst_nonneg M π V₀ μmin η₀
  have hS0 : 0 ≤ S := Nat.cast_nonneg _
  have hT0 : (0 : ℝ) < T := by exact_mod_cast hT
  have hsT : 0 ≤ (Real.sqrt T)⁻¹ := inv_nonneg.2 (Real.sqrt_nonneg _)
  have hsTT : (Real.sqrt T)⁻¹ * (Real.sqrt T)⁻¹ = (T : ℝ)⁻¹ := by
    rw [← mul_inv, Real.mul_self_sqrt hT0.le]
  have hi : ∀ i : Fin T, ∑ ω : Fin T → Tuple State Action, pathWeight M π μ ω * (F i ω * G i ω) ≤
      a * b * S * (K * B * L) * ((T : ℝ)⁻¹ * Real.sqrt (stepSize η₀ (i + 1))) := by
    intro i
    set Ma := a * ((Real.sqrt T)⁻¹ * (K * B))
    have hMa : 0 ≤ Ma := by positivity
    calc ∑ ω : Fin T → Tuple State Action, pathWeight M π μ ω * (F i ω * G i ω)
        ≤ ∑ ω : Fin T → Tuple State Action, pathWeight M π μ ω *
            (Ma * (b * ∑ s, |looRemainder M π μ η₀ V₀ i (xs i) ω s|)) :=
          sum_le_sum fun ω _ ↦ mul_le_mul_of_nonneg_left
            (mul_le_mul (hF i ω) (hG i ω) (hG0 i ω) hMa) (pathWeight_nonneg M π μ ω)
      _ = Ma * b * ∑ ω : Fin T → Tuple State Action, pathWeight M π μ ω *
            ∑ s, |looRemainder M π μ η₀ V₀ i (xs i) ω s| := by
          rw [mul_sum]; exact sum_congr rfl fun ω _ ↦ by ring
      _ ≤ Ma * b * (S * (L * ((Real.sqrt T)⁻¹ * Real.sqrt (stepSize η₀ (i + 1))))) :=
          mul_le_mul_of_nonneg_left (sum_pathWeight_mul_sum_abs_looRemainder_le M π μ h0 h1 V₀
            hμmin0 hμmin i (xs i)) (mul_nonneg hMa hb)
      _ = a * b * S * (K * B * L) * (((Real.sqrt T)⁻¹ * (Real.sqrt T)⁻¹) *
            Real.sqrt (stepSize η₀ (i + 1))) := by ring
      _ = a * b * S * (K * B * L) * ((T : ℝ)⁻¹ * Real.sqrt (stepSize η₀ (i + 1))) := by
          rw [hsTT]
  have hC : 0 ≤ a * b * S * (K * B * L) := by positivity
  calc ∑ i : Fin T, ∑ ω : Fin T → Tuple State Action, pathWeight M π μ ω * (F i ω * G i ω)
      ≤ ∑ i : Fin T, a * b * S * (K * B * L) * ((T : ℝ)⁻¹ * Real.sqrt (stepSize η₀ (i + 1))) :=
        sum_le_sum fun i _ ↦ hi i
    _ = a * b * S * (K * B * L) *
          ∑ i : Fin T, (T : ℝ)⁻¹ * Real.sqrt (stepSize η₀ (i + 1)) := by rw [mul_sum]
    _ ≤ a * b * S * (K * B * L) * (3 / 2 * Real.sqrt η₀ * (T : ℝ) ^ (-(1 / 3 : ℝ))) :=
        mul_le_mul_of_nonneg_left (sum_fin_inv_mul_sqrt_stepSize_le η₀ hT) hC
    _ = a * b * S * looChenShaoConst M π V₀ μmin η₀ * (T : ℝ) ^ (-(1 / 3 : ℝ)) := by
        simp only [looChenShaoConst, K, B, L]; ring

/-! ## The leave-one-out sums in the sup, Euclidean and `ℓ¹` norms -/

/-- **Vector leave-one-out sum, sup norm.** For `0 < η₀ ≤ 1`, `0 < μmin ≤ μ(s)`, `T ≥ 1`, every
`V₀` and replacement tuples `x⋆_i`, with `D = √TΔ̄_T − linPart` and `D^{(i)}(ω) = D(ω[i ↦ x⋆_i])`:
`∑_i E[‖ξ_i‖_∞ ‖D − D^{(i)}‖_∞] ≤ S K_CS T^{-1/3}`. -/
theorem sum_looChenShao_norm_le [DecidableEq State] (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) {η₀ : ℝ} (h0 : 0 < η₀)
    (h1 : η₀ ≤ 1) (V₀ : State → ℝ) {μmin : ℝ} (hμmin0 : 0 < μmin)
    (hμmin : ∀ s, μmin ≤ μ.prob s) {T : ℕ} (hT : 1 ≤ T) (xs : Fin T → Tuple State Action) :
    ∑ i : Fin T, ∑ ω : Fin T → Tuple State Action, pathWeight M π μ ω *
        (‖linSummand M π μ η₀ T i (ω i)‖ *
          ‖(scaledError M π η₀ V₀ ω - linPart M π μ η₀ ω) -
            (scaledError M π η₀ V₀ (Function.update ω i (xs i)) -
              linPart M π μ η₀ (Function.update ω i (xs i)))‖) ≤
      Fintype.card State * looChenShaoConst M π V₀ μmin η₀ * (T : ℝ) ^ (-(1 / 3 : ℝ)) := by
  have h := sum_looChenShao_vec_of_le M π μ h0 h1 V₀ hμmin0 hμmin hT xs zero_le_one zero_le_one
    (fun i ω ↦ ‖linSummand M π μ η₀ T i (ω i)‖)
    (fun i ω ↦ ‖(scaledError M π η₀ V₀ ω - linPart M π μ η₀ ω) -
      (scaledError M π η₀ V₀ (Function.update ω i (xs i)) -
        linPart M π μ η₀ (Function.update ω i (xs i)))‖)
    (fun i ω ↦ by
      rw [one_mul]; exact norm_linSummand_le_inv_sqrt M π μ h0 h1 hμmin0 hμmin T i _)
    (fun _ _ ↦ norm_nonneg _)
    (fun i ω ↦ by
      dsimp only
      rw [one_mul, ← looRemainder_eq_sub]
      exact norm_le_sum_abs_apply _)
  simpa only [one_mul] using h

/-- **Shao–Zhang form, sup norm.** With `Δ = ‖D‖_∞` and `Δ^{(i)} = ‖D^{(i)}‖_∞` (independent of
`ω i`): `∑_i E[‖ξ_i‖_∞ |Δ − Δ^{(i)}|] ≤ S K_CS T^{-1/3}`, same hypotheses as
`sum_looChenShao_norm_le`. -/
theorem sum_looChenShao_abs_norm_sub_le [DecidableEq State] (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) {η₀ : ℝ} (h0 : 0 < η₀)
    (h1 : η₀ ≤ 1) (V₀ : State → ℝ) {μmin : ℝ} (hμmin0 : 0 < μmin)
    (hμmin : ∀ s, μmin ≤ μ.prob s) {T : ℕ} (hT : 1 ≤ T) (xs : Fin T → Tuple State Action) :
    ∑ i : Fin T, ∑ ω : Fin T → Tuple State Action, pathWeight M π μ ω *
        (‖linSummand M π μ η₀ T i (ω i)‖ *
          |‖scaledError M π η₀ V₀ ω - linPart M π μ η₀ ω‖ -
            ‖scaledError M π η₀ V₀ (Function.update ω i (xs i)) -
              linPart M π μ η₀ (Function.update ω i (xs i))‖|) ≤
      Fintype.card State * looChenShaoConst M π V₀ μmin η₀ * (T : ℝ) ^ (-(1 / 3 : ℝ)) := by
  have h := sum_looChenShao_vec_of_le M π μ h0 h1 V₀ hμmin0 hμmin hT xs zero_le_one zero_le_one
    (fun i ω ↦ ‖linSummand M π μ η₀ T i (ω i)‖)
    (fun i ω ↦ |‖scaledError M π η₀ V₀ ω - linPart M π μ η₀ ω‖ -
      ‖scaledError M π η₀ V₀ (Function.update ω i (xs i)) -
        linPart M π μ η₀ (Function.update ω i (xs i))‖|)
    (fun i ω ↦ by
      rw [one_mul]; exact norm_linSummand_le_inv_sqrt M π μ h0 h1 hμmin0 hμmin T i _)
    (fun _ _ ↦ abs_nonneg _)
    (fun i ω ↦ by
      dsimp only
      rw [one_mul]
      refine (abs_norm_sub_norm_le _ _).trans ?_
      rw [← looRemainder_eq_sub]
      exact norm_le_sum_abs_apply _)
  simpa only [one_mul] using h

/-- **Vector leave-one-out sum, `ℓ¹` norm.**
`∑_i E[‖ξ_i‖₁ ‖D − D^{(i)}‖₁] ≤ S² K_CS T^{-1/3}`, same hypotheses as
`sum_looChenShao_norm_le`. -/
theorem sum_looChenShao_sumAbs_le [DecidableEq State] (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) {η₀ : ℝ} (h0 : 0 < η₀)
    (h1 : η₀ ≤ 1) (V₀ : State → ℝ) {μmin : ℝ} (hμmin0 : 0 < μmin)
    (hμmin : ∀ s, μmin ≤ μ.prob s) {T : ℕ} (hT : 1 ≤ T) (xs : Fin T → Tuple State Action) :
    ∑ i : Fin T, ∑ ω : Fin T → Tuple State Action, pathWeight M π μ ω *
        ((∑ s, |linSummand M π μ η₀ T i (ω i) s|) *
          ∑ s, |looRemainder M π μ η₀ V₀ i (xs i) ω s|) ≤
      (Fintype.card State : ℝ) ^ 2 * looChenShaoConst M π V₀ μmin η₀ *
        (T : ℝ) ^ (-(1 / 3 : ℝ)) := by
  have h := sum_looChenShao_vec_of_le M π μ h0 h1 V₀ hμmin0 hμmin hT xs
    (Nat.cast_nonneg (Fintype.card State)) zero_le_one
    (fun i ω ↦ ∑ s, |linSummand M π μ η₀ T i (ω i) s|)
    (fun i ω ↦ ∑ s, |looRemainder M π μ η₀ V₀ i (xs i) ω s|)
    (fun i ω ↦ sum_abs_linSummand_le M π μ h0 h1 hμmin0 hμmin T i _)
    (fun _ _ ↦ sum_nonneg fun _ _ ↦ abs_nonneg _)
    (fun i ω ↦ (one_mul _).ge)
  refine h.trans (le_of_eq ?_)
  ring

/-- **Vector leave-one-out sum, Euclidean norm.**
`∑_i E[‖ξ_i‖₂ ‖D − D^{(i)}‖₂] ≤ S² K_CS T^{-1/3}`, same hypotheses as
`sum_looChenShao_norm_le`. -/
theorem sum_looChenShao_euclid_le [DecidableEq State] (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) {η₀ : ℝ} (h0 : 0 < η₀)
    (h1 : η₀ ≤ 1) (V₀ : State → ℝ) {μmin : ℝ} (hμmin0 : 0 < μmin)
    (hμmin : ∀ s, μmin ≤ μ.prob s) {T : ℕ} (hT : 1 ≤ T) (xs : Fin T → Tuple State Action) :
    ∑ i : Fin T, ∑ ω : Fin T → Tuple State Action, pathWeight M π μ ω *
        (‖(WithLp.toLp 2 (linSummand M π μ η₀ T i (ω i)) : EuclideanSpace ℝ State)‖ *
          ‖(WithLp.toLp 2 ((scaledError M π η₀ V₀ ω - linPart M π μ η₀ ω) -
            (scaledError M π η₀ V₀ (Function.update ω i (xs i)) -
              linPart M π μ η₀ (Function.update ω i (xs i)))) : EuclideanSpace ℝ State)‖) ≤
      (Fintype.card State : ℝ) ^ 2 * looChenShaoConst M π V₀ μmin η₀ *
        (T : ℝ) ^ (-(1 / 3 : ℝ)) := by
  have h := sum_looChenShao_vec_of_le M π μ h0 h1 V₀ hμmin0 hμmin hT xs
    (Nat.cast_nonneg (Fintype.card State)) zero_le_one
    (fun i ω ↦ ‖(WithLp.toLp 2 (linSummand M π μ η₀ T i (ω i)) : EuclideanSpace ℝ State)‖)
    (fun i ω ↦ ‖(WithLp.toLp 2 ((scaledError M π η₀ V₀ ω - linPart M π μ η₀ ω) -
      (scaledError M π η₀ V₀ (Function.update ω i (xs i)) -
        linPart M π μ η₀ (Function.update ω i (xs i)))) : EuclideanSpace ℝ State)‖)
    (fun i ω ↦ (norm_toLp_two_le_sum_abs _).trans
      (sum_abs_linSummand_le M π μ h0 h1 hμmin0 hμmin T i _))
    (fun _ _ ↦ norm_nonneg _)
    (fun i ω ↦ by
      dsimp only
      rw [one_mul, ← looRemainder_eq_sub]
      exact norm_toLp_two_le_sum_abs _)
  refine h.trans (le_of_eq ?_)
  ring

/-- **Shao–Zhang form, Euclidean norm.** With `Δ = ‖D‖₂`, `Δ^{(i)} = ‖D^{(i)}‖₂`:
`∑_i E[‖ξ_i‖₂ |Δ − Δ^{(i)}|] ≤ S² K_CS T^{-1/3}`, same hypotheses as
`sum_looChenShao_norm_le`. -/
theorem sum_looChenShao_abs_euclid_sub_le [DecidableEq State] (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) {η₀ : ℝ} (h0 : 0 < η₀)
    (h1 : η₀ ≤ 1) (V₀ : State → ℝ) {μmin : ℝ} (hμmin0 : 0 < μmin)
    (hμmin : ∀ s, μmin ≤ μ.prob s) {T : ℕ} (hT : 1 ≤ T) (xs : Fin T → Tuple State Action) :
    ∑ i : Fin T, ∑ ω : Fin T → Tuple State Action, pathWeight M π μ ω *
        (‖(WithLp.toLp 2 (linSummand M π μ η₀ T i (ω i)) : EuclideanSpace ℝ State)‖ *
          |‖(WithLp.toLp 2 (scaledError M π η₀ V₀ ω - linPart M π μ η₀ ω) :
              EuclideanSpace ℝ State)‖ -
            ‖(WithLp.toLp 2 (scaledError M π η₀ V₀ (Function.update ω i (xs i)) -
              linPart M π μ η₀ (Function.update ω i (xs i))) : EuclideanSpace ℝ State)‖|) ≤
      (Fintype.card State : ℝ) ^ 2 * looChenShaoConst M π V₀ μmin η₀ *
        (T : ℝ) ^ (-(1 / 3 : ℝ)) := by
  have h := sum_looChenShao_vec_of_le M π μ h0 h1 V₀ hμmin0 hμmin hT xs
    (Nat.cast_nonneg (Fintype.card State)) zero_le_one
    (fun i ω ↦ ‖(WithLp.toLp 2 (linSummand M π μ η₀ T i (ω i)) : EuclideanSpace ℝ State)‖)
    (fun i ω ↦ |‖(WithLp.toLp 2 (scaledError M π η₀ V₀ ω - linPart M π μ η₀ ω) :
        EuclideanSpace ℝ State)‖ -
      ‖(WithLp.toLp 2 (scaledError M π η₀ V₀ (Function.update ω i (xs i)) -
        linPart M π μ η₀ (Function.update ω i (xs i))) : EuclideanSpace ℝ State)‖|)
    (fun i ω ↦ (norm_toLp_two_le_sum_abs _).trans
      (sum_abs_linSummand_le M π μ h0 h1 hμmin0 hμmin T i _))
    (fun _ _ ↦ abs_nonneg _)
    (fun i ω ↦ by
      dsimp only
      rw [one_mul]
      refine (abs_norm_sub_norm_le _ _).trans ?_
      rw [← WithLp.toLp_sub, ← looRemainder_eq_sub]
      exact norm_toLp_two_le_sum_abs _)
  refine h.trans (le_of_eq ?_)
  ring

/-! ## The remainder `D` and the cross term `E‖W‖‖D‖` -/

/-- **`‖D‖₁` in `L²`.** For `0 < η₀ ≤ 1`, `0 < μmin ≤ μ(s)`, `T ≥ 1` and every `V₀`,
`‖ ∑_s |D(s)| ‖_{L²} ≤ S K_E T^{-1/3}`, `D = √TΔ̄_T − linPart`. -/
theorem weightedL2_sumAbs_remainder_le [DecidableEq State] (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) {η₀ : ℝ} (h0 : 0 < η₀)
    (h1 : η₀ ≤ 1) (V₀ : State → ℝ) {μmin : ℝ} (hμmin0 : 0 < μmin)
    (hμmin : ∀ s, μmin ≤ μ.prob s) {T : ℕ} (hT : 1 ≤ T) :
    weightedL2 (pathWeight M π μ) (fun ω : Fin T → Tuple State Action ↦
        ∑ s, |scaledError M π η₀ V₀ ω s - linPart M π μ η₀ ω s|) ≤
      Fintype.card State * (linRemainderConst M π V₀ μmin η₀ * (T : ℝ) ^ (-(1 / 3 : ℝ))) := by
  have hw := pathWeight_nonneg M π μ (T := T)
  refine (weightedL2_sum_le hw univ
    (fun s ω ↦ |scaledError M π η₀ V₀ ω s - linPart M π μ η₀ ω s|)).trans ?_
  calc ∑ s, weightedL2 (pathWeight M π μ)
        (fun ω : Fin T → Tuple State Action ↦ |scaledError M π η₀ V₀ ω s - linPart M π μ η₀ ω s|)
      ≤ ∑ _s : State, linRemainderConst M π V₀ μmin η₀ * (T : ℝ) ^ (-(1 / 3 : ℝ)) :=
        sum_le_sum fun s _ ↦ by
          rw [weightedL2_abs]
          exact weightedL2_scaledError_sub_linPart_le M π μ h0 h1 V₀ hμmin0 hμmin hT s
    _ = _ := by rw [sum_const, card_univ, nsmul_eq_mul]

/-- **`‖D‖_∞` in `L²`.** `‖ ‖D‖_∞ ‖_{L²} ≤ S K_E T^{-1/3}` (same hypotheses). -/
theorem weightedL2_norm_remainder_le [DecidableEq State] (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) {η₀ : ℝ} (h0 : 0 < η₀)
    (h1 : η₀ ≤ 1) (V₀ : State → ℝ) {μmin : ℝ} (hμmin0 : 0 < μmin)
    (hμmin : ∀ s, μmin ≤ μ.prob s) {T : ℕ} (hT : 1 ≤ T) :
    weightedL2 (pathWeight M π μ) (fun ω : Fin T → Tuple State Action ↦
        ‖scaledError M π η₀ V₀ ω - linPart M π μ η₀ ω‖) ≤
      Fintype.card State * (linRemainderConst M π V₀ μmin η₀ * (T : ℝ) ^ (-(1 / 3 : ℝ))) := by
  refine (weightedL2_mono (pathWeight_nonneg M π μ) fun ω ↦ ?_).trans
    (weightedL2_sumAbs_remainder_le M π μ h0 h1 V₀ hμmin0 hμmin hT)
  rw [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (sum_nonneg fun _ _ ↦ abs_nonneg _)]
  exact norm_le_sum_abs_apply _

/-- **`E‖D‖_∞`.** `E‖√TΔ̄_T − linPart‖_∞ ≤ S K_E T^{-1/3}` (same hypotheses). -/
theorem sum_pathWeight_mul_norm_remainder_le [DecidableEq State]
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (μ : FiniteDistribution State) {η₀ : ℝ} (h0 : 0 < η₀) (h1 : η₀ ≤ 1) (V₀ : State → ℝ)
    {μmin : ℝ} (hμmin0 : 0 < μmin) (hμmin : ∀ s, μmin ≤ μ.prob s) {T : ℕ} (hT : 1 ≤ T) :
    ∑ ω : Fin T → Tuple State Action, pathWeight M π μ ω *
        ‖scaledError M π η₀ V₀ ω - linPart M π μ η₀ ω‖ ≤
      Fintype.card State * (linRemainderConst M π V₀ μmin η₀ * (T : ℝ) ^ (-(1 / 3 : ℝ))) := by
  refine le_trans ?_ ((sum_pathWeight_mul_abs_le_weightedL2 M π μ _).trans
    (weightedL2_norm_remainder_le M π μ h0 h1 V₀ hμmin0 hμmin hT))
  exact le_of_eq (sum_congr rfl fun ω _ ↦ by rw [abs_of_nonneg (norm_nonneg _)])

/-- **`W(s)` in `L²`.** For `0 < η₀ ≤ 1`, `0 < μmin ≤ μ(s)`, `T ≥ 1` and every state `s`,
`‖linPart(s)‖_{L²} ≤ K_β B`. -/
theorem weightedL2_linPart_apply_le [DecidableEq State] (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) {η₀ : ℝ} (h0 : 0 < η₀)
    (h1 : η₀ ≤ 1) {μmin : ℝ} (hμmin0 : 0 < μmin) (hμmin : ∀ s, μmin ≤ μ.prob s) {T : ℕ}
    (hT : 1 ≤ T) (s : State) :
    weightedL2 (pathWeight M π μ) (fun ω : Fin T → Tuple State Action ↦ linPart M π μ η₀ ω s) ≤
      linWeightConst M μmin η₀ * tdNoiseBound M π := by
  set c := (Real.sqrt T)⁻¹ * (linWeightConst M μmin η₀ * tdNoiseBound M π)
  have hK0 := linWeightConst_nonneg M hμmin0 h0
  have hB0 := (tdNoiseBound_pos M π).le
  have hT0 : (0 : ℝ) < T := by exact_mod_cast hT
  have hpt : ∀ (k : ℕ) (x : Tuple State Action),
      linSummand M π μ η₀ T k x s * linSummand M π μ η₀ T k x s ≤ c ^ 2 := by
    intro k x
    rw [← sq, ← sq_abs]
    have h := (Real.norm_eq_abs _ ▸ norm_le_pi_norm (linSummand M π μ η₀ T k x) s).trans
      (norm_linSummand_le_inv_sqrt M π μ h0 h1 hμmin0 hμmin T k x)
    exact pow_le_pow_left₀ (abs_nonneg _) h 2
  have hsq : ∑ ω : Fin T → Tuple State Action, pathWeight M π μ ω * linPart M π μ η₀ ω s ^ 2 ≤
      (linWeightConst M μmin η₀ * tdNoiseBound M π) ^ 2 := by
    have e := sum_pathWeight_mul_sum_mul_sum M π μ (fun k x ↦ linSummand M π μ η₀ T k x s)
      (fun k x ↦ linSummand M π μ η₀ T k x s)
      (fun k ↦ sum_tupleProb_mul_linSummand M π μ η₀ T k s)
      (fun k ↦ sum_tupleProb_mul_linSummand M π μ η₀ T k s) T
    have e' : ∑ ω : Fin T → Tuple State Action, pathWeight M π μ ω * linPart M π μ η₀ ω s ^ 2 =
        ∑ k ∈ range T, ∑ x, tupleProb M π μ x *
          (linSummand M π μ η₀ T k x s * linSummand M π μ η₀ T k x s) := by
      rw [← e]
      refine sum_congr rfl fun ω _ ↦ ?_
      rw [linPart_eq_sum, Finset.sum_apply, sq]
    rw [e']
    calc ∑ k ∈ range T, ∑ x, tupleProb M π μ x *
          (linSummand M π μ η₀ T k x s * linSummand M π μ η₀ T k x s)
        ≤ ∑ _k ∈ range T, ∑ x, tupleProb M π μ x * c ^ 2 :=
          sum_le_sum fun k _ ↦ sum_le_sum fun x _ ↦
            mul_le_mul_of_nonneg_left (hpt k x) (tupleProb_nonneg M π μ x)
      _ = T * c ^ 2 := by
          simp only [← sum_mul, sum_tupleProb, one_mul, sum_const, card_range, nsmul_eq_mul]
      _ = (linWeightConst M μmin η₀ * tdNoiseBound M π) ^ 2 := by
          simp only [c, mul_pow, inv_pow, Real.sq_sqrt hT0.le]
          field_simp
  refine (weightedL2_le_sqrt hsq).trans (le_of_eq ?_)
  exact Real.sqrt_sq (mul_nonneg hK0 hB0)

/-- **The cross term `E[‖W‖₁ ‖D‖₁]`.** For `0 < η₀ ≤ 1`, `0 < μmin ≤ μ(s)`, `T ≥ 1` and every
`V₀`, `E[(∑_s |W(s)|)(∑_s |D(s)|)] ≤ S² K_β B K_E T^{-1/3}` (Cauchy–Schwarz). -/
theorem sum_pathWeight_mul_sumAbs_linPart_mul_le [DecidableEq State]
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (μ : FiniteDistribution State) {η₀ : ℝ} (h0 : 0 < η₀) (h1 : η₀ ≤ 1) (V₀ : State → ℝ)
    {μmin : ℝ} (hμmin0 : 0 < μmin) (hμmin : ∀ s, μmin ≤ μ.prob s) {T : ℕ} (hT : 1 ≤ T) :
    ∑ ω : Fin T → Tuple State Action, pathWeight M π μ ω *
        ((∑ s, |linPart M π μ η₀ ω s|) *
          ∑ s, |scaledError M π η₀ V₀ ω s - linPart M π μ η₀ ω s|) ≤
      (Fintype.card State : ℝ) ^ 2 * (linWeightConst M μmin η₀ * tdNoiseBound M π) *
        linRemainderConst M π V₀ μmin η₀ * (T : ℝ) ^ (-(1 / 3 : ℝ)) := by
  have hw := pathWeight_nonneg M π μ (T := T)
  have hW : weightedL2 (pathWeight M π μ)
      (fun ω : Fin T → Tuple State Action ↦ ∑ s, |linPart M π μ η₀ ω s|) ≤
      Fintype.card State * (linWeightConst M μmin η₀ * tdNoiseBound M π) := by
    refine (weightedL2_sum_le hw univ (fun s ω ↦ |linPart M π μ η₀ ω s|)).trans ?_
    calc ∑ s, weightedL2 (pathWeight M π μ)
          (fun ω : Fin T → Tuple State Action ↦ |linPart M π μ η₀ ω s|)
        ≤ ∑ _s : State, linWeightConst M μmin η₀ * tdNoiseBound M π :=
          sum_le_sum fun s _ ↦ by
            rw [weightedL2_abs]
            exact weightedL2_linPart_apply_le M π μ h0 h1 hμmin0 hμmin hT s
      _ = _ := by rw [sum_const, card_univ, nsmul_eq_mul]
  have hD := weightedL2_sumAbs_remainder_le M π μ h0 h1 V₀ hμmin0 hμmin hT
  have hK0 := linWeightConst_nonneg M hμmin0 h0
  have hB0 := (tdNoiseBound_pos M π).le
  refine (sum_mul_mul_le_weightedL2 hw _ _).trans ?_
  calc weightedL2 (pathWeight M π μ)
        (fun ω : Fin T → Tuple State Action ↦ ∑ s, |linPart M π μ η₀ ω s|) *
        weightedL2 (pathWeight M π μ) (fun ω : Fin T → Tuple State Action ↦
          ∑ s, |scaledError M π η₀ V₀ ω s - linPart M π μ η₀ ω s|)
      ≤ (Fintype.card State * (linWeightConst M μmin η₀ * tdNoiseBound M π)) *
          (Fintype.card State * (linRemainderConst M π V₀ μmin η₀ * (T : ℝ) ^ (-(1 / 3 : ℝ)))) :=
        mul_le_mul hW hD (weightedL2_nonneg _ _) (by positivity)
    _ = _ := by ring

/-- **The cross term `E[‖W‖_∞ ‖D‖_∞]`.** For `0 < η₀ ≤ 1`, `0 < μmin ≤ μ(s)`, `T ≥ 1` and every
`V₀`, `E[‖linPart‖_∞ ‖√TΔ̄_T − linPart‖_∞] ≤ S² K_β B K_E T^{-1/3}`. -/
theorem sum_pathWeight_mul_norm_linPart_mul_le [DecidableEq State]
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (μ : FiniteDistribution State) {η₀ : ℝ} (h0 : 0 < η₀) (h1 : η₀ ≤ 1) (V₀ : State → ℝ)
    {μmin : ℝ} (hμmin0 : 0 < μmin) (hμmin : ∀ s, μmin ≤ μ.prob s) {T : ℕ} (hT : 1 ≤ T) :
    ∑ ω : Fin T → Tuple State Action, pathWeight M π μ ω *
        (‖linPart M π μ η₀ ω‖ * ‖scaledError M π η₀ V₀ ω - linPart M π μ η₀ ω‖) ≤
      (Fintype.card State : ℝ) ^ 2 * (linWeightConst M μmin η₀ * tdNoiseBound M π) *
        linRemainderConst M π V₀ μmin η₀ * (T : ℝ) ^ (-(1 / 3 : ℝ)) := by
  refine le_trans (sum_le_sum fun ω _ ↦ mul_le_mul_of_nonneg_left ?_ (pathWeight_nonneg M π μ ω))
    (sum_pathWeight_mul_sumAbs_linPart_mul_le M π μ h0 h1 V₀ hμmin0 hμmin hT)
  exact mul_le_mul (norm_le_sum_abs_apply _) (norm_le_sum_abs_apply _) (norm_nonneg _)
    (sum_nonneg fun _ _ ↦ abs_nonneg _)

end StatisticalRL.Ch7Rest.TDInference
