import Formalization.Ch7Rest.TDInferenceConvexLinSharp711
import Formalization.Ch7Rest.TDInferenceLooVector711
import Formalization.Probability.ConvexNonlinearTransfer

/-!
# Corrected Theorem 7.11 over all convex sets at the printed rate `T^{-1/3}`

Source: `thm:Berry-Esseen-linear`, `chapters/inference.tex:132–141` (`d_cvx` at :124–129;
`Λ⋆ = A⁻¹ΓA⁻ᵀ` at :104–117). Two differences from the printed result:

* the covariance is the corrected `Γ := Γ_true` (SOURCE-ISSUES C43);
* the constant is an instance constant (depending on the MDP, `π`, `μ`, `η₀` and `V₀`), not the
  printed coefficient.

Proof (our own; a self-contained randomized-concentration argument for polyhedral
representations of convex sets, not the cited paper's proof). Write `W = linPart = ∑_k ξ_k`
(`ξ_k = linSummand T k (ω k)`, independent, mean zero, `‖ξ_k‖ ≤ δ_T = T^{-1/2} K_β B`) and
`D = √TΔ̄_T − W`. Then

`|P(W + D ∈ C) − N(C)| ≤ |P(W + D ∈ C) − P(W ∈ C)| + |P(W ∈ C) − N(C)|`.

The second term is `O(T^{-1/3})` by `abs_linLaw_convex_sub_gaussCov_le_third`. The first is
bounded by the nonlinear transfer theorem `Stein.Polyhedral.abs_pexp_convex_add_sub_le_update`,
whose inputs are:

* `λ = min Γ_true / (32 S²)`: the reservoir condition at `r = n = T`
  (`exists_linFactor_reservoirCond_of_pos`) together with `|v|₁² ≤ S |v|₂²`
  (`linSummand_quad_lower`);
* `E‖W‖ ≤ S K_β B` and `E m ≤ δ_T S² K_β B` (`pexp_norm_vsum_le`, `pexp_devSum_le`,
  `sum_sqrt_linSummand_sq_le`);
* `E‖W‖‖D‖ ≤ S² K_β B K_E T^{-1/3}` (`sum_pathWeight_mul_norm_linPart_mul_le`);
* `∑_i E‖ξ_i‖ |‖D‖ − ‖D(ω[i ↦ x⋆])‖| ≤ S K_CS T^{-1/3}` (`sum_looChenShao_abs_norm_sub_le`);
* `δ_T ≤ T^{-1/3} K_β B` for `T ≥ 1`.

Small `T` (below the reservoir burn-in `N`) uses the trivial bound `1 ≤ N^{1/3} T^{-1/3}`.

Main export: `abs_lawProb_convex_sub_gaussCov_le_third_sharp`.
-/

open Finset Matrix
open scoped BigOperators

namespace StatisticalRL.Ch7Rest.TDInference

open StatisticalRL.Probability StatisticalRL.Analysis

variable {State Action : Type} [Fintype State] [Fintype Action] [DecidableEq State]

/-- A second moment written as a quadratic form: if `∑ₓ p x yₓ(s) yₓ(s') = Q s s'` for all
`s, s'`, then `∑ₓ p x ⟨v, yₓ⟩² = v ⬝ᵥ (Q *ᵥ v)`. -/
theorem sum_mul_sq_dotProduct_eq {α κ : Type*} [Fintype α] [Fintype κ] (p : α → ℝ)
    (y : α → κ → ℝ) (Q : Matrix κ κ ℝ) (hQ : ∀ s s', ∑ x, p x * (y x s * y x s') = Q s s')
    (v : κ → ℝ) : ∑ x, p x * (v ⬝ᵥ y x) ^ 2 = v ⬝ᵥ (Q *ᵥ v) := by
  calc ∑ x, p x * (v ⬝ᵥ y x) ^ 2
      = ∑ x, ∑ s, ∑ s', v s * v s' * (p x * (y x s * y x s')) := by
        refine sum_congr rfl fun x _ ↦ ?_
        rw [sq, dotProduct, Finset.sum_mul_sum, Finset.mul_sum]
        refine sum_congr rfl fun s _ ↦ ?_
        rw [Finset.mul_sum]
        exact sum_congr rfl fun s' _ ↦ by ring
    _ = ∑ s, ∑ s', v s * v s' * ∑ x, p x * (y x s * y x s') := by
        rw [Finset.sum_comm]
        refine sum_congr rfl fun s _ ↦ ?_
        rw [Finset.sum_comm]
        simp_rw [Finset.mul_sum]
    _ = v ⬝ᵥ (Q *ᵥ v) := by
        simp only [hQ]
        simp only [dotProduct, mulVec, Finset.mul_sum]
        exact sum_congr rfl fun s _ ↦ sum_congr rfl fun s' _ ↦ by ring

omit [Fintype State] [DecidableEq State] in
/-- `T^{-1/2} ≤ T^{-1/3}` for `T ≥ 1`. -/
theorem inv_sqrt_le_rpow_neg_third {T : ℕ} (hT : 1 ≤ T) :
    (Real.sqrt T)⁻¹ ≤ (T : ℝ) ^ (-(1 / 3 : ℝ)) := by
  have hT1 : (1 : ℝ) ≤ T := by exact_mod_cast hT
  rw [Real.sqrt_eq_rpow, ← Real.rpow_neg (Nat.cast_nonneg _)]
  exact Real.rpow_le_rpow_of_exponent_le hT1 (by norm_num)

/-- **Uniform lower bound on directional variances** (the `λ` input of the nonlinear transfer
theorem). For `T ≥ linReservoirBurnIn` and every `v` with `∑ⱼ |vⱼ| = 1`,
`min Γ_true / (32 S) / S ≤ ∑_k E⟨v, ξ_k⟩²`. -/
theorem linSummand_quad_lower [Nonempty State] (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) {η₀ : ℝ} (h0 : 0 < η₀)
    (h1 : η₀ ≤ 1) {μmin : ℝ} (hμmin0 : 0 < μmin) (hμmin : ∀ s, μmin ≤ μ.prob s)
    (hΓ : ∀ s, 0 < trueGamma M π μ s) {T : ℕ} (hT : linReservoirBurnIn M μmin η₀ ≤ T)
    (v : State → ℝ) (hv : ∑ j, |v j| = 1) :
    diagMin (trueGamma M π μ) / (32 * Fintype.card State) / Fintype.card State ≤
      ∑ i : Fin T, ∑ x, tupleProb M π μ x * (v ⬝ᵥ linSummand M π μ η₀ T i x) ^ 2 := by
  have hT1 : 1 ≤ T := (one_le_linReservoirBurnIn M hμmin0 h0).trans hT
  obtain ⟨hc, e, hres⟩ := exists_linFactor_reservoirCond_of_pos M π μ h0 h1 hμmin0 hμmin hΓ hT
  set c := diagMin (trueGamma M π μ) / (32 * Fintype.card State) with hc_def
  have h := hres T hT1 le_rfl v
  have hTne : (T : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  rw [mul_div_assoc, div_self hTne, mul_one] at h
  rw [show (Finset.univ.filter fun m : Fin T ↦ T - T ≤ (m : ℕ)) = Finset.univ by
    ext m; simp] at h
  have hq : ∀ j : Fin T, v ⬝ᵥ ((linFactor M π μ η₀ T j * (linFactor M π μ η₀ T j)ᵀ) *ᵥ v) =
      ∑ x, tupleProb M π μ x * (v ⬝ᵥ linSummand M π μ η₀ T j x) ^ 2 := fun j ↦
    (sum_mul_sq_dotProduct_eq _ _ _
      (fun s s' ↦ sum_tupleProb_mul_linSummand_mul M π μ η₀ T j s s') v).symm
  have h' : c * (v ⬝ᵥ v) ≤
      ∑ i : Fin T, ∑ x, tupleProb M π μ x * (v ⬝ᵥ linSummand M π μ η₀ T i x) ^ 2 :=
    h.trans_eq ((Equiv.sum_comp e
      (fun j ↦ v ⬝ᵥ ((linFactor M π μ η₀ T j * (linFactor M π μ η₀ T j)ᵀ) *ᵥ v))).trans
        (sum_congr rfl fun j _ ↦ hq j))
  have hS : (0 : ℝ) < Fintype.card State := by exact_mod_cast Fintype.card_pos
  have hl1 : 1 ≤ (Fintype.card State : ℝ) * (v ⬝ᵥ v) := by
    have hcs := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun j ↦ |v j|)
    rw [hv, card_univ] at hcs
    have hvv : ∑ j, |v j| ^ 2 = v ⬝ᵥ v := by
      rw [dotProduct]; exact sum_congr rfl fun j _ ↦ by rw [sq_abs, sq]
    rw [hvv] at hcs
    simpa using hcs
  have hinv : 1 / (Fintype.card State : ℝ) ≤ v ⬝ᵥ v := by
    rw [div_le_iff₀ hS, mul_comm]; exact hl1
  calc c / Fintype.card State = c * (1 / Fintype.card State) := by ring
    _ ≤ c * (v ⬝ᵥ v) := mul_le_mul_of_nonneg_left hinv hc.le
    _ ≤ _ := h'

/-- `∑ⱼ √(∑_k E ξ_k(j)²) ≤ S K_β B` (each coordinate variance is at most `T δ_T² = (K_β B)²`). -/
theorem sum_sqrt_linSummand_sq_le (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) {η₀ : ℝ} (h0 : 0 < η₀)
    (h1 : η₀ ≤ 1) {μmin : ℝ} (hμmin0 : 0 < μmin) (hμmin : ∀ s, μmin ≤ μ.prob s) {T : ℕ}
    (hT : 1 ≤ T) :
    ∑ j, Real.sqrt (∑ i : Fin T, ∑ x, tupleProb M π μ x * linSummand M π μ η₀ T i x j ^ 2) ≤
      Fintype.card State * (linWeightConst M μmin η₀ * tdNoiseBound M π) := by
  set B := linWeightConst M μmin η₀ * tdNoiseBound M π with hB_def
  have hB : 0 ≤ B :=
    mul_nonneg (linWeightConst_nonneg M hμmin0 h0) (tdNoiseBound_pos M π).le
  set δ := (Real.sqrt T)⁻¹ * B with hδ_def
  have hδ : 0 ≤ δ := mul_nonneg (inv_nonneg.2 (Real.sqrt_nonneg _)) hB
  have hT0 : (0 : ℝ) < T := by exact_mod_cast hT
  have hTδ : (T : ℝ) * δ ^ 2 = B ^ 2 := by
    rw [hδ_def, mul_pow, inv_pow, Real.sq_sqrt hT0.le, ← mul_assoc, mul_inv_cancel₀ hT0.ne',
      one_mul]
  have hj : ∀ j, Real.sqrt (∑ i : Fin T, ∑ x, tupleProb M π μ x *
      linSummand M π μ η₀ T i x j ^ 2) ≤ B := by
    intro j
    have hle : ∑ i : Fin T, ∑ x, tupleProb M π μ x * linSummand M π μ η₀ T i x j ^ 2 ≤ B ^ 2 := by
      calc ∑ i : Fin T, ∑ x, tupleProb M π μ x * linSummand M π μ η₀ T i x j ^ 2
          ≤ ∑ _i : Fin T, ∑ x, tupleProb M π μ x * δ ^ 2 := by
            refine sum_le_sum fun i _ ↦ sum_le_sum fun x _ ↦ ?_
            refine mul_le_mul_of_nonneg_left ?_ (tupleProb_nonneg M π μ x)
            have hx : |linSummand M π μ η₀ T i x j| ≤ δ := by
              rw [← Real.norm_eq_abs]
              exact (norm_le_pi_norm _ j).trans
                (norm_linSummand_le_inv_sqrt M π μ h0 h1 hμmin0 hμmin T i x)
            rw [← sq_abs]
            exact pow_le_pow_left₀ (abs_nonneg _) hx 2
        _ = (T : ℝ) * δ ^ 2 := by
            simp only [← Finset.sum_mul, sum_tupleProb, one_mul, sum_const, card_univ,
              Fintype.card_fin, nsmul_eq_mul]
        _ = B ^ 2 := hTδ
    calc Real.sqrt _ ≤ Real.sqrt (B ^ 2) := Real.sqrt_le_sqrt hle
      _ = B := Real.sqrt_sq hB
  calc ∑ j, Real.sqrt (∑ i : Fin T, ∑ x, tupleProb M π μ x * linSummand M π μ η₀ T i x j ^ 2)
      ≤ ∑ _j : State, B := sum_le_sum fun j _ ↦ hj j
    _ = Fintype.card State * B := by rw [sum_const, card_univ, nsmul_eq_mul]

/-- The `T^{-1/3}` constant of the nonlinear transfer step for `T ≥ linReservoirBurnIn`:
`λ⁻¹ ((4/3)(S² K_β B K_E + 2 K_β B · S K_β B + S K_CS) + K_β B · S · S K_β B)` with
`λ = min Γ_true / (32 S) / S`. -/
noncomputable def convexNonlinConst [Nonempty State] (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) (V₀ : State → ℝ)
    (μmin η₀ : ℝ) : ℝ :=
  (diagMin (trueGamma M π μ) / (32 * Fintype.card State) / Fintype.card State)⁻¹ *
    ((4 / 3) * ((Fintype.card State : ℝ) ^ 2 * (linWeightConst M μmin η₀ * tdNoiseBound M π) *
          linRemainderConst M π V₀ μmin η₀ +
        2 * (linWeightConst M μmin η₀ * tdNoiseBound M π) *
          (Fintype.card State * (linWeightConst M μmin η₀ * tdNoiseBound M π)) +
        Fintype.card State * looChenShaoConst M π V₀ μmin η₀) +
      (linWeightConst M μmin η₀ * tdNoiseBound M π) * Fintype.card State *
        (Fintype.card State * (linWeightConst M μmin η₀ * tdNoiseBound M π)))

/-- **Nonlinear transfer for the TD statistic.** For `T ≥ linReservoirBurnIn` and every convex
`C` (measurable or not): `|P(√TΔ̄_T ∈ C) − P(linPart ∈ C)| ≤ convexNonlinConst · T^{-1/3}`. -/
theorem abs_lawProb_sub_linLaw_le_third_of_burnIn [Nonempty State]
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (μ : FiniteDistribution State) {η₀ : ℝ} (h0 : 0 < η₀) (h1 : η₀ ≤ 1) (V₀ : State → ℝ)
    {μmin : ℝ} (hμmin0 : 0 < μmin) (hμmin : ∀ s, μmin ≤ μ.prob s)
    (hΓ : ∀ s, 0 < trueGamma M π μ s) {T : ℕ} (hT : linReservoirBurnIn M μmin η₀ ≤ T)
    {C : Set (State → ℝ)} (hC : Convex ℝ C) :
    |lawProb M π μ η₀ V₀ T C - ∑ ω : Fin T → Tuple State Action,
        pathWeight M π μ ω * C.indicator (fun _ ↦ (1 : ℝ)) (linPart M π μ η₀ ω)| ≤
      convexNonlinConst M π μ V₀ μmin η₀ * (T : ℝ) ^ (-(1 / 3 : ℝ)) := by
  have hT1 : 1 ≤ T := (one_le_linReservoirBurnIn M hμmin0 h0).trans hT
  have : Nonempty Action := M.action_nonempty
  set B := linWeightConst M μmin η₀ * tdNoiseBound M π with hB_def
  have hB : 0 ≤ B :=
    mul_nonneg (linWeightConst_nonneg M hμmin0 h0) (tdNoiseBound_pos M π).le
  set S : ℝ := (Fintype.card State : ℝ) with hS_def
  have hS : 0 ≤ S := Nat.cast_nonneg _
  set t : ℝ := (T : ℝ) ^ (-(1 / 3 : ℝ)) with ht_def
  set δ := (Real.sqrt T)⁻¹ * B with hδ_def
  have hδ : 0 ≤ δ := mul_nonneg (inv_nonneg.2 (Real.sqrt_nonneg _)) hB
  have hδt : δ ≤ t * B := mul_le_mul_of_nonneg_right (inv_sqrt_le_rpow_neg_third hT1) hB
  set lam := diagMin (trueGamma M π μ) / (32 * Fintype.card State) / Fintype.card State
    with hlam_def
  have hγ : 0 < diagMin (trueGamma M π μ) := (Finset.lt_inf'_iff _).2 fun s _ ↦ hΓ s
  have hSpos : (0 : ℝ) < Fintype.card State := by exact_mod_cast Fintype.card_pos
  have hlam0 : 0 < lam := by positivity
  -- the product law, summands and perturbation
  set p : Fin T → Tuple State Action → ℝ := fun _ ↦ tupleProb M π μ with hp_def
  set ξ : ∀ _ : Fin T, Tuple State Action → State → ℝ :=
    fun i x ↦ linSummand M π μ η₀ T i x with hξ_def
  set D : (Fin T → Tuple State Action) → State → ℝ :=
    fun ω ↦ scaledError M π η₀ V₀ ω - linPart M π μ η₀ ω with hD_def
  set xs : Fin T → Tuple State Action := fun _ ↦ Classical.arbitrary _ with hxs_def
  have hP : ∀ F : (Fin T → Tuple State Action) → ℝ,
      Stein.pexp p F = ∑ ω : Fin T → Tuple State Action, pathWeight M π μ ω * F ω :=
    fun F ↦ rfl
  have hvsum : ∀ ω, Stein.Polyhedral.vsum ξ ω = linPart M π μ η₀ ω := fun ω ↦ by
    rw [linPart_eq_sum]; rfl
  have hp0 : ∀ i x, 0 ≤ p i x := fun _ x ↦ tupleProb_nonneg M π μ x
  have hp1 : ∀ i, ∑ x, p i x = 1 := fun _ ↦ sum_tupleProb M π μ
  have hmean : ∀ i j, ∑ x, p i x * ξ i x j = 0 := fun i j ↦
    sum_tupleProb_mul_linSummand M π μ η₀ T i j
  have hbd : ∀ i x, ‖ξ i x‖ ≤ δ := fun i x ↦
    norm_linSummand_le_inv_sqrt M π μ h0 h1 hμmin0 hμmin T i x
  have hlam : ∀ v : State → ℝ, ∑ j, |v j| = 1 →
      lam ≤ ∑ i, ∑ x, p i x * (v ⬝ᵥ ξ i x) ^ 2 := fun v hv ↦
    linSummand_quad_lower M π μ h0 h1 hμmin0 hμmin hΓ hT v hv
  have hN3 := Stein.Polyhedral.abs_pexp_convex_add_sub_le_update hp0 hp1 hmean hδ hbd hlam0
    hlam D xs hC
  -- identify the two probabilities
  have e1 : Stein.pexp p (fun ω ↦ C.indicator (fun _ ↦ (1 : ℝ))
      (Stein.Polyhedral.vsum ξ ω + D ω)) = lawProb M π μ η₀ V₀ T C := by
    rw [hP, lawProb]
    refine sum_congr rfl fun ω _ ↦ ?_
    rw [hvsum, hD_def, add_sub_cancel]
  have e2 : Stein.pexp p (fun ω ↦ C.indicator (fun _ ↦ (1 : ℝ))
      (Stein.Polyhedral.vsum ξ ω)) = ∑ ω : Fin T → Tuple State Action,
        pathWeight M π μ ω * C.indicator (fun _ ↦ (1 : ℝ)) (linPart M π μ η₀ ω) := by
    rw [hP]
    refine sum_congr rfl fun ω _ ↦ ?_
    rw [hvsum]
  rw [e1, e2] at hN3
  -- the inputs
  have hWD : Stein.pexp p (fun ω ↦ ‖Stein.Polyhedral.vsum ξ ω‖ * ‖D ω‖) ≤
      S ^ 2 * B * linRemainderConst M π V₀ μmin η₀ * t := by
    rw [hP]
    simp only [hvsum]
    exact sum_pathWeight_mul_norm_linPart_mul_le M π μ h0 h1 V₀ hμmin0 hμmin hT1
  have hsq := sum_sqrt_linSummand_sq_le M π μ h0 h1 hμmin0 hμmin hT1
  have hW : Stein.pexp p (fun ω ↦ ‖Stein.Polyhedral.vsum ξ ω‖) ≤ S * B :=
    (Stein.Polyhedral.pexp_norm_vsum_le hp0 hp1 hmean).trans hsq
  have hW0 : 0 ≤ Stein.pexp p (fun ω ↦ ‖Stein.Polyhedral.vsum ξ ω‖) :=
    Stein.pexp_nonneg hp0 fun _ ↦ norm_nonneg _
  have hloo : ∑ i, Stein.pexp p (fun ω ↦ ‖ξ i (ω i)‖ *
      |‖D ω‖ - ‖D (Function.update ω i (xs i))‖|) ≤
      S * looChenShaoConst M π V₀ μmin η₀ * t := by
    simp only [hP]
    exact sum_looChenShao_abs_norm_sub_le M π μ h0 h1 V₀ hμmin0 hμmin hT1 xs
  have hdev : Stein.pexp p (Stein.Polyhedral.devSum p ξ) ≤ δ * S * (S * B) := by
    refine (Stein.Polyhedral.pexp_devSum_le hp0 hp1 hδ hbd).trans ?_
    exact mul_le_mul_of_nonneg_left hsq (mul_nonneg hδ hS)
  have hSB : 0 ≤ S * B := mul_nonneg hS hB
  have h2 : 2 * δ * Stein.pexp p (fun ω ↦ ‖Stein.Polyhedral.vsum ξ ω‖) ≤
      2 * (t * B) * (S * B) := by
    have := mul_le_mul hδt hW hW0 (by
      have : 0 ≤ (T : ℝ) ^ (-(1 / 3 : ℝ)) := Real.rpow_nonneg (Nat.cast_nonneg _) _
      exact mul_nonneg this hB)
    nlinarith
  have hdev' : Stein.pexp p (Stein.Polyhedral.devSum p ξ) ≤ t * B * S * (S * B) :=
    hdev.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hδt hS) hSB)
  refine hN3.trans ?_
  calc lam⁻¹ * ((4 / 3) * (Stein.pexp p (fun ω ↦ ‖Stein.Polyhedral.vsum ξ ω‖ * ‖D ω‖) +
          2 * δ * Stein.pexp p (fun ω ↦ ‖Stein.Polyhedral.vsum ξ ω‖) +
          ∑ i, Stein.pexp p (fun ω ↦ ‖ξ i (ω i)‖ *
            |‖D ω‖ - ‖D (Function.update ω i (xs i))‖|)) +
        Stein.pexp p (Stein.Polyhedral.devSum p ξ))
      ≤ lam⁻¹ * ((4 / 3) * (S ^ 2 * B * linRemainderConst M π V₀ μmin η₀ * t +
          2 * (t * B) * (S * B) + S * looChenShaoConst M π V₀ μmin η₀ * t) +
        t * B * S * (S * B)) := by
        refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 hlam0.le)
        linarith
    _ = convexNonlinConst M π μ V₀ μmin η₀ * t := by
        rw [convexNonlinConst]; ring

/-- **Corrected Theorem 7.11 over all convex sets at the printed rate `T^{-1/3}`**
(`thm:Berry-Esseen-linear`, `chapters/inference.tex:132–141`; corrected covariance `Γ_true`,
SOURCE-ISSUES C43; instance constant, not the printed coefficient). For full-support `μ`,
`0 < η₀ ≤ 1`, any initial value `V₀` and `Γ_true ≻ 0` there is a constant `K > 0` (depending on
the instance, `η₀` and `V₀`) such that for every `T ≥ 1` and every convex `C ⊆ ℝ^S` (measurable or
not; `gaussCov.real` is the outer measure)
`|P(√T Δ̄_T ∈ C) − N(0, A⁻¹ diag(Γ_true) A⁻ᵀ)(C)| ≤ K · T^{-1/3}`.

Our own proof: a self-contained randomized-concentration argument for polyhedral representations
of convex sets (`Stein.Polyhedral.abs_pexp_convex_add_sub_le_update`), combined with the linear
rate `abs_linLaw_convex_sub_gaussCov_le_third`; it is not the cited paper's proof. Same hypotheses
and shape as `abs_lawProb_convex_sub_gaussCov_le_third_log`, without the factor `log(2T)`. -/
theorem abs_lawProb_convex_sub_gaussCov_le_third_sharp [Nonempty State]
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (μ : FiniteDistribution State) {η₀ : ℝ} (h0 : 0 < η₀) (h1 : η₀ ≤ 1) (V₀ : State → ℝ)
    (hμ : ∀ s, 0 < μ.prob s) (hΓ : ∀ s, 0 < trueGamma M π μ s) :
    ∃ K : ℝ, 0 < K ∧ ∀ T : ℕ, 1 ≤ T → ∀ C : Set (State → ℝ), Convex ℝ C →
      |lawProb M π μ η₀ V₀ T C - (gaussCov (tdA M π μ) (trueGamma M π μ)).real C| ≤
        K * (T : ℝ) ^ (-(1 / 3 : ℝ)) := by
  set μmin := diagMin μ.prob with hμmin_def
  have hμmin0 : 0 < μmin := (Finset.lt_inf'_iff _).2 fun s _ ↦ hμ s
  have hμmin : ∀ s, μmin ≤ μ.prob s := fun s ↦ Finset.inf'_le _ (mem_univ s)
  set N := linReservoirBurnIn M μmin η₀
  set K₁ := linConvexThirdConst M π μ μmin η₀
  set K₂ := convexNonlinConst M π μ V₀ μmin η₀
  set K := |K₁| + |K₂| + (N : ℝ) ^ (1 / 3 : ℝ) + 1 with hK_def
  have hN0 : 0 ≤ (N : ℝ) ^ (1 / 3 : ℝ) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  refine ⟨K, by positivity, fun T hT C hC ↦ ?_⟩
  have hTr : 0 ≤ (T : ℝ) ^ (-(1 / 3 : ℝ)) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  by_cases hTN : N ≤ T
  · have hlin := abs_linLaw_convex_sub_gaussCov_le_third_of_burnIn M π μ h0 h1 hμmin0 hμmin hΓ
      hTN hC
    have hnl := abs_lawProb_sub_linLaw_le_third_of_burnIn M π μ h0 h1 V₀ hμmin0 hμmin hΓ hTN hC
    have hK₁ := le_abs_self K₁
    have hK₂ := le_abs_self K₂
    calc _ ≤ |lawProb M π μ η₀ V₀ T C - ∑ ω : Fin T → Tuple State Action,
            pathWeight M π μ ω * C.indicator (fun _ ↦ (1 : ℝ)) (linPart M π μ η₀ ω)| +
          |∑ ω : Fin T → Tuple State Action,
            pathWeight M π μ ω * C.indicator (fun _ ↦ (1 : ℝ)) (linPart M π μ η₀ ω) -
            (gaussCov (tdA M π μ) (trueGamma M π μ)).real C| := abs_sub_le _ _ _
      _ ≤ K₂ * (T : ℝ) ^ (-(1 / 3 : ℝ)) + K₁ * (T : ℝ) ^ (-(1 / 3 : ℝ)) := add_le_add hnl hlin
      _ ≤ K * (T : ℝ) ^ (-(1 / 3 : ℝ)) := by
          rw [← add_mul]
          refine mul_le_mul_of_nonneg_right ?_ hTr
          linarith
  · have h1' := abs_sum_pathWeight_indicator_sub_gaussCov_le_one M π μ (T := T)
      (fun ω ↦ scaledError M π η₀ V₀ ω) (tdA M π μ) (trueGamma M π μ) C
    have h2 := ReservoirSharp.one_le_rpow_third_mul_of_lt hT (not_le.1 hTN)
    refine h1'.trans (h2.trans ?_)
    refine mul_le_mul_of_nonneg_right ?_ hTr
    have := abs_nonneg K₁
    have := abs_nonneg K₂
    linarith

end StatisticalRL.Ch7Rest.TDInference
