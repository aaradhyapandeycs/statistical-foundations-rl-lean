import Formalization.TDInference.PolyakRuppert

/-!
# Theorem 7.11 support (M3): explicit `L²` bounds for the Polyak–Ruppert remainder

Continuation of `TDInference/PolyakRuppert.lean`; all expectations are under the i.i.d. path
law `pathWeight` on `Fin T → Tuple` (`inference.tex:54–61`), written as weighted `L²` seminorms
`weightedL2 (pathWeight M π μ)`. Hypotheses throughout: `0 < η₀ ≤ 1`, `0 < μmin ≤ μ(s)` for all
`s`, `T ≥ 1`. Constants: `B = tdNoiseBound`, `D = tdPathBound`, `C = tdMomentConst`,
`u_T = natCubeRoot T = T^{1/3}`.
-/

open Finset Matrix
open scoped BigOperators

namespace StatisticalRL.Ch7Rest.TDInference

open StatisticalRL.Probability

variable {State Action : Type} [Fintype State] [Fintype Action]

/-! ## The martingale part -/

/-- `E_x ((A_x − A)Δ)(s)² ≤ 2Δ(s)² + 2 E_{P_π(·|s)} Δ²`. -/
theorem sum_tupleProb_mul_sq_prMartingaleTerm_le [DecidableEq State]
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (μ : FiniteDistribution State) (s : State) (k : ℕ) (V : State → ℝ) :
    ∑ x, tupleProb M π μ x * prMartingaleTerm M π μ s k V x ^ 2 ≤
      2 * (V s - M.valueFixedPoint π s) ^ 2 + 2 * ∑ s', (M.policyTransition π s).prob s' *
        (V s' - M.valueFixedPoint π s') ^ 2 := by
  set Δ := V - M.valueFixedPoint π with hΔ
  have hγ0 := M.discount_nonneg
  have hγ1 := M.discount_lt_one
  unfold prMartingaleTerm
  rw [← hΔ, ← sum_tupleProb_mul_sampleA M π μ Δ s]
  refine (sum_mul_sq_sub_mean_le (sum_tupleProb M π μ) (fun x ↦ sampleA M x Δ s)).trans ?_
  have e : ∀ x : Tuple State Action, sampleA M x Δ s ^ 2 =
      if s = x.1 then (Δ s - M.discount * Δ x.2.2) ^ 2 else 0 := by
    intro x; rw [sampleA_apply]; split_ifs <;> ring
  simp_rw [e]
  rw [sum_tupleProb_mul_ite_zero M π μ s (fun _ s' ↦ (Δ s - M.discount * Δ s') ^ 2)]
  have hc0 : 0 ≤ tupleCondExp M π s (fun _ s' ↦ (Δ s - M.discount * Δ s') ^ 2) :=
    (π s).expectation_nonneg fun a ↦ (M.transition s a).expectation_nonneg fun s' ↦ sq_nonneg _
  have hle : tupleCondExp M π s (fun _ s' ↦ (Δ s - M.discount * Δ s') ^ 2) ≤
      tupleCondExp M π s (fun a s' ↦ 2 * Δ s ^ 2 + 2 * (fun s' ↦ Δ s' ^ 2) s' +
        0 * (fun (_ : Action) (_ : State) ↦ (0 : ℝ)) a s') := by
    refine tupleCondExp_mono M π s fun a s' ↦ ?_
    have : M.discount ^ 2 ≤ 1 := by nlinarith
    nlinarith [sq_nonneg (Δ s + M.discount * Δ s'), sq_nonneg (Δ s'),
      mul_le_mul_of_nonneg_right this (sq_nonneg (Δ s'))]
  rw [tupleCondExp_affine] at hle
  simp only [zero_mul, add_zero, FiniteDistribution.expectation] at hle ⊢
  have hμ := prob_le_one μ s
  have hμ0 := μ.prob_nonneg s
  simp only [hΔ, Pi.sub_apply] at hle hc0 ⊢
  nlinarith [mul_le_mul_of_nonneg_right hμ hc0]

theorem sum_tupleProb_mul_prMartingaleTerm [DecidableEq State]
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (μ : FiniteDistribution State) (s : State) (k : ℕ) (V : State → ℝ) :
    ∑ x, tupleProb M π μ x * prMartingaleTerm M π μ s k V x = 0 := by
  simp only [prMartingaleTerm, mul_sub, sum_sub_distrib, sum_tupleProb_mul_sampleA, ← sum_mul,
    sum_tupleProb, one_mul, sub_self]

/-- `E (∑_{k<T} ((A_k − A)Δ_k)(s))² ≤ 4D² + 12 C η₀ T^{1/3}`. -/
theorem sum_pathWeight_mul_sq_prMartingale_le [DecidableEq State]
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (μ : FiniteDistribution State) {η₀ : ℝ} (h0 : 0 < η₀) (h1 : η₀ ≤ 1) (V₀ : State → ℝ)
    {μmin : ℝ} (hμmin0 : 0 < μmin) (hμmin : ∀ s, μmin ≤ μ.prob s) {T : ℕ} (hT : 1 ≤ T)
    (s : State) :
    ∑ ω : Fin T → Tuple State Action, pathWeight M π μ ω *
        (∑ k : Fin T, prMartingaleTerm M π μ s k (tdIter M η₀ V₀ ω k) (ω k)) ^ 2 ≤
      4 * tdPathBound M π V₀ ^ 2 +
        12 * tdMomentConst M π V₀ μmin η₀ * η₀ * natCubeRoot T := by
  set D := tdPathBound M π V₀
  set C := tdMomentConst M π V₀ μmin η₀
  rw [sum_pathWeight_mul_sq_sum_eq M π μ η₀ V₀ (fun k V x ↦ prMartingaleTerm M π μ s k V x)
    (fun k V ↦ sum_tupleProb_mul_prMartingaleTerm M π μ s k V) T]
  -- per-step bound by `4 Q_k`
  have hstep : ∀ k (Q : ℝ), (∀ s', tdSecondMoment M π μ η₀ V₀ k s' ≤ Q) →
      ∑ ω : Fin k → Tuple State Action, pathWeight M π μ ω *
        ∑ x, tupleProb M π μ x * prMartingaleTerm M π μ s k (tdIter M η₀ V₀ ω k) x ^ 2 ≤
        4 * Q := by
    intro k Q hQ
    calc _ ≤ ∑ ω : Fin k → Tuple State Action, pathWeight M π μ ω *
          (2 * (tdIter M η₀ V₀ ω k s - M.valueFixedPoint π s) ^ 2 +
            2 * ∑ s', (M.policyTransition π s).prob s' *
              (tdIter M η₀ V₀ ω k s' - M.valueFixedPoint π s') ^ 2 + 0) :=
          sum_le_sum fun ω _ ↦ mul_le_mul_of_nonneg_left
            ((sum_tupleProb_mul_sq_prMartingaleTerm_le M π μ s k _).trans_eq (add_zero _).symm)
            (pathWeight_nonneg M π μ ω)
      _ = 2 * tdSecondMoment M π μ η₀ V₀ k s +
          2 * ∑ s', (M.policyTransition π s).prob s' * tdSecondMoment M π μ η₀ V₀ k s' + 0 :=
          sum_mul_affine_eq (sum_pathWeight M π μ k) _ _ _ _ _ _
      _ ≤ 2 * Q + 2 * ∑ s', (M.policyTransition π s).prob s' * Q + 0 := by
          have hsum : ∑ s', (M.policyTransition π s).prob s' * tdSecondMoment M π μ η₀ V₀ k s' ≤
              ∑ s', (M.policyTransition π s).prob s' * Q :=
            sum_le_sum fun s' _ ↦
              mul_le_mul_of_nonneg_left (hQ s') ((M.policyTransition π s).prob_nonneg s')
          linarith [hQ s]
      _ = 4 * Q := by rw [← sum_mul, (M.policyTransition π s).sum_prob]; ring
  obtain ⟨n, rfl⟩ : ∃ n, T = n + 1 := ⟨T - 1, by omega⟩
  rw [sum_range_succ']
  have h0term := hstep 0 (D ^ 2) fun s' ↦ tdSecondMoment_le_sq M π μ h0.le h1 V₀ 0 s'
  have hrest : ∑ k ∈ range n, ∑ ω : Fin (k + 1) → Tuple State Action, pathWeight M π μ ω *
        ∑ x, tupleProb M π μ x *
          prMartingaleTerm M π μ s (k + 1) (tdIter M η₀ V₀ ω (k + 1)) x ^ 2 ≤
      ∑ k ∈ range n, 4 * C * stepSize η₀ (k + 1) := by
    refine sum_le_sum fun k _ ↦ ?_
    have := hstep (k + 1) (C * stepSize η₀ (k + 1)) fun s' ↦
      tdSecondMoment_le M π μ h0 h1 V₀ hμmin0 hμmin (Nat.le_add_left 1 k) s'
    linarith
  have hsum := sum_range_stepSize_succ_le h0.le n
  have hC : 0 ≤ C := tdMomentConst_nonneg M π V₀ hμmin0
  have hcube : natCubeRoot n ≤ natCubeRoot (n + 1) := natCubeRoot_mono (Nat.le_succ n)
  rw [← mul_sum] at hrest
  have : 4 * C * ∑ k ∈ range n, stepSize η₀ (k + 1) ≤ 12 * C * η₀ * natCubeRoot (n + 1) := by
    nlinarith [mul_le_mul_of_nonneg_left hsum (by positivity : (0 : ℝ) ≤ 4 * C),
      mul_le_mul_of_nonneg_left hcube (by positivity : (0 : ℝ) ≤ 12 * C * η₀)]
  linarith

/-! ## Moments of the errors along the length-`T` path law -/

theorem weightedL2_tdError_eq [DecidableEq State] (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) (η₀ : ℝ)
    (V₀ : State → ℝ) {k T : ℕ} (hk : k ≤ T) (s : State) :
    weightedL2 (pathWeight M π μ) (fun ω : Fin T → Tuple State Action ↦ tdError M π η₀ V₀ ω k s) =
      √(tdSecondMoment M π μ η₀ V₀ k s) := by
  unfold weightedL2 tdError tdSecondMoment
  simp only [Pi.sub_apply]
  rw [sum_pathWeight_mul_tdIter_of_le M π μ η₀ V₀
    (fun V ↦ (V s - M.valueFixedPoint π s) ^ 2) hk]

theorem weightedL2_tdError_le_sqrt [DecidableEq State] (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) {η₀ : ℝ} (h0 : 0 < η₀)
    (h1 : η₀ ≤ 1) (V₀ : State → ℝ) {μmin : ℝ} (hμmin0 : 0 < μmin)
    (hμmin : ∀ s, μmin ≤ μ.prob s) {k T : ℕ} (hk1 : 1 ≤ k) (hk : k ≤ T) (s : State) :
    weightedL2 (pathWeight M π μ) (fun ω : Fin T → Tuple State Action ↦ tdError M π η₀ V₀ ω k s) ≤
      √(tdMomentConst M π V₀ μmin η₀) * √(stepSize η₀ k) := by
  rw [weightedL2_tdError_eq M π μ η₀ V₀ hk, ← Real.sqrt_mul (tdMomentConst_nonneg M π V₀ hμmin0)]
  exact Real.sqrt_le_sqrt (tdSecondMoment_le M π μ h0 h1 V₀ hμmin0 hμmin hk1 s)

theorem weightedL2_tdError_le_pathBound [DecidableEq State] (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) {η₀ : ℝ} (h0 : 0 ≤ η₀)
    (h1 : η₀ ≤ 1) (V₀ : State → ℝ) {T : ℕ} (k : ℕ) (s : State) :
    weightedL2 (pathWeight M π μ) (fun ω : Fin T → Tuple State Action ↦ tdError M π η₀ V₀ ω k s) ≤
      tdPathBound M π V₀ :=
  weightedL2_le_of_abs_le (pathWeight_nonneg M π μ) (sum_pathWeight M π μ T)
    (tdPathBound_nonneg M π V₀) fun ω ↦ abs_tdIter_sub_le M π h0 h1 V₀ ω k s

/-! ## The telescoping and boundary parts -/

/-- `‖∑_{k<T}(1/η_{k+1} − 1/η_k)Δ_k(s)‖_{L²} ≤ D/η₀ + 3√C T^{1/3}/√η₀`. -/
theorem weightedL2_prTelescope_le [DecidableEq State] (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) {η₀ : ℝ} (h0 : 0 < η₀)
    (h1 : η₀ ≤ 1) (V₀ : State → ℝ) {μmin : ℝ} (hμmin0 : 0 < μmin)
    (hμmin : ∀ s, μmin ≤ μ.prob s) {T : ℕ} (hT : 1 ≤ T) (s : State) :
    weightedL2 (pathWeight M π μ) (fun ω : Fin T → Tuple State Action ↦
        ∑ k ∈ range T, (invStepSize η₀ (k + 1) - invStepSize η₀ k) * tdError M π η₀ V₀ ω k s) ≤
      tdPathBound M π V₀ / η₀ +
        3 * √(tdMomentConst M π V₀ μmin η₀) * natCubeRoot T / √η₀ := by
  set C := tdMomentConst M π V₀ μmin η₀
  set D := tdPathBound M π V₀
  have hw := pathWeight_nonneg M π μ (T := T)
  have hs0 : 0 < √η₀ := Real.sqrt_pos.2 h0
  have hc : ∀ k, 0 ≤ invStepSize η₀ (k + 1) - invStepSize η₀ k :=
    fun k ↦ sub_nonneg.2 (invStepSize_mono h0 (Nat.le_succ k))
  refine (weightedL2_sum_le hw (range T) _).trans ?_
  simp_rw [weightedL2_const_mul, abs_of_nonneg (hc _)]
  obtain ⟨n, rfl⟩ : ∃ n, T = n + 1 := ⟨T - 1, by omega⟩
  rw [sum_range_succ']
  have hfirst : (invStepSize η₀ (0 + 1) - invStepSize η₀ 0) *
      weightedL2 (pathWeight M π μ) (fun ω : Fin (n + 1) → Tuple State Action ↦
        tdError M π η₀ V₀ ω 0 s) ≤ D / η₀ := by
    rw [invStepSize_zero, zero_add, invStepSize, natCubeRoot_one, sub_zero, one_pow, div_mul_eq_mul_div,
      one_mul]
    exact div_le_div_of_nonneg_right (weightedL2_tdError_le_pathBound M π μ h0.le h1 V₀ 0 s)
      h0.le
  have hrest : ∑ k ∈ range n, (invStepSize η₀ (k + 1 + 1) - invStepSize η₀ (k + 1)) *
      weightedL2 (pathWeight M π μ) (fun ω : Fin (n + 1) → Tuple State Action ↦
        tdError M π η₀ V₀ ω (k + 1) s) ≤
      ∑ k ∈ range n, √C * (stepSize η₀ (k + 1) / (η₀ * √η₀)) := by
    refine sum_le_sum fun k hk ↦ ?_
    have hk' : k + 1 ≤ n + 1 := by have := mem_range.1 hk; omega
    calc _ ≤ (invStepSize η₀ (k + 1 + 1) - invStepSize η₀ (k + 1)) *
          (√C * √(stepSize η₀ (k + 1))) :=
          mul_le_mul_of_nonneg_left (weightedL2_tdError_le_sqrt M π μ h0 h1 V₀ hμmin0 hμmin
            (Nat.le_add_left 1 k) hk' s) (hc _)
      _ = √C * ((invStepSize η₀ (k + 1 + 1) - invStepSize η₀ (k + 1)) *
          √(stepSize η₀ (k + 1))) := by ring
      _ ≤ √C * (stepSize η₀ (k + 1) / (η₀ * √η₀)) :=
          mul_le_mul_of_nonneg_left
            (invStepSize_succ_sub_mul_sqrt_le h0 (Nat.le_add_left 1 k)) (Real.sqrt_nonneg _)
  have hsum := sum_range_stepSize_succ_le h0.le n
  have hcube : natCubeRoot n ≤ natCubeRoot (n + 1) := natCubeRoot_mono (Nat.le_succ n)
  have hC : 0 ≤ √C := Real.sqrt_nonneg _
  have hfin : ∑ k ∈ range n, √C * (stepSize η₀ (k + 1) / (η₀ * √η₀)) ≤
      3 * √C * natCubeRoot (n + 1) / √η₀ := by
    rw [← mul_sum, ← sum_div]
    rw [mul_div_assoc', div_le_div_iff₀ (by positivity) hs0]
    have hη : η₀ * √η₀ * √η₀ = η₀ * η₀ := by rw [mul_assoc, Real.mul_self_sqrt h0.le]
    have key : √C * ∑ k ∈ range n, stepSize η₀ (k + 1) ≤ √C * (3 * η₀ * natCubeRoot (n + 1)) :=
      mul_le_mul_of_nonneg_left (hsum.trans (by nlinarith)) hC
    calc √C * (∑ k ∈ range n, stepSize η₀ (k + 1)) * √η₀
        ≤ √C * (3 * η₀ * natCubeRoot (n + 1)) * √η₀ := mul_le_mul_of_nonneg_right key hs0.le
      _ = 3 * √C * natCubeRoot (n + 1) * (η₀ * √η₀) := by ring
  linarith

/-- `‖(1/η_T)Δ_T(s)‖_{L²} ≤ √C T^{1/3}/√η₀`. -/
theorem weightedL2_prEndpoint_le [DecidableEq State] (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) {η₀ : ℝ} (h0 : 0 < η₀)
    (h1 : η₀ ≤ 1) (V₀ : State → ℝ) {μmin : ℝ} (hμmin0 : 0 < μmin)
    (hμmin : ∀ s, μmin ≤ μ.prob s) {T : ℕ} (hT : 1 ≤ T) (s : State) :
    weightedL2 (pathWeight M π μ) (fun ω : Fin T → Tuple State Action ↦
        invStepSize η₀ T * tdError M π η₀ V₀ ω T s) ≤
      √(tdMomentConst M π V₀ μmin η₀) * natCubeRoot T / √η₀ := by
  rw [weightedL2_const_mul,
    abs_of_nonneg (show 0 ≤ invStepSize η₀ T from div_nonneg (sq_nonneg _) h0.le)]
  calc invStepSize η₀ T * weightedL2 (pathWeight M π μ)
        (fun ω : Fin T → Tuple State Action ↦ tdError M π η₀ V₀ ω T s)
      ≤ invStepSize η₀ T * (√(tdMomentConst M π V₀ μmin η₀) * √(stepSize η₀ T)) :=
        mul_le_mul_of_nonneg_left
          (weightedL2_tdError_le_sqrt M π μ h0 h1 V₀ hμmin0 hμmin hT le_rfl s)
          (div_nonneg (sq_nonneg _) h0.le)
    _ = √(tdMomentConst M π V₀ μmin η₀) * (invStepSize η₀ T * √(stepSize η₀ T)) := by ring
    _ = _ := by rw [invStepSize_mul_sqrt_eq h0 hT, mul_div_assoc]

/-- Pathwise `|(A(Δ_T − Δ_0))(s)| ≤ 4D`, hence the same `L²` bound. -/
theorem weightedL2_prBoundary_le [DecidableEq State] (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) {η₀ : ℝ} (h0 : 0 ≤ η₀)
    (h1 : η₀ ≤ 1) (V₀ : State → ℝ) (T : ℕ) (s : State) :
    weightedL2 (pathWeight M π μ) (fun ω : Fin T → Tuple State Action ↦
        (tdA M π μ *ᵥ (tdError M π η₀ V₀ ω T - tdError M π η₀ V₀ ω 0)) s) ≤
      4 * tdPathBound M π V₀ := by
  have hD := tdPathBound_nonneg M π V₀
  refine weightedL2_le_of_abs_le (pathWeight_nonneg M π μ) (sum_pathWeight M π μ T)
    (by positivity) fun ω ↦ ?_
  set x := tdError M π η₀ V₀ ω T - tdError M π η₀ V₀ ω 0
  have hx : ∀ s', |x s'| ≤ 2 * tdPathBound M π V₀ := by
    intro s'
    simp only [x, tdError, Pi.sub_apply]
    have h₁ := abs_tdIter_sub_le M π h0 h1 V₀ ω T s'
    have h₂ := abs_tdIter_sub_le M π h0 h1 V₀ ω 0 s'
    calc _ ≤ |tdIter M η₀ V₀ ω T s' - M.valueFixedPoint π s'| +
          |tdIter M η₀ V₀ ω 0 s' - M.valueFixedPoint π s'| := abs_sub _ _
      _ ≤ _ := by linarith
  have hE : |(M.policyTransition π s).expectation x| ≤ 2 * tdPathBound M π V₀ :=
    (M.policyTransition π s).abs_expectation_le hx
  have hγ0 := M.discount_nonneg
  have hγ1 := M.discount_lt_one
  rw [tdA_mulVec_apply, abs_mul, abs_of_nonneg (μ.prob_nonneg s)]
  have hin : |x s - M.discount * (M.policyTransition π s).expectation x| ≤
      4 * tdPathBound M π V₀ := by
    calc _ ≤ |x s| + |M.discount * (M.policyTransition π s).expectation x| := abs_sub _ _
      _ = |x s| + M.discount * |(M.policyTransition π s).expectation x| := by
          rw [abs_mul, abs_of_nonneg hγ0]
      _ ≤ 2 * tdPathBound M π V₀ + 1 * (2 * tdPathBound M π V₀) :=
          add_le_add (hx s) (mul_le_mul hγ1.le hE (abs_nonneg _) zero_le_one)
      _ = _ := by ring
  calc μ.prob s * |x s - M.discount * (M.policyTransition π s).expectation x|
      ≤ 1 * (4 * tdPathBound M π V₀) :=
        mul_le_mul (prob_le_one μ s) hin (abs_nonneg _) zero_le_one
    _ = _ := one_mul _

/-! ## The residual and the main remainder bound -/

/-- The explicit `L²` bound on each coordinate of the residual `R_T`:
`√(4D² + 12Cη₀u_T) + 4√C u_T/√η₀ + D/η₀ + 4D`. -/
noncomputable def prResidualBound (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (V₀ : State → ℝ) (μmin η₀ : ℝ) (T : ℕ) : ℝ :=
  √(4 * tdPathBound M π V₀ ^ 2 + 12 * tdMomentConst M π V₀ μmin η₀ * η₀ * natCubeRoot T) +
    4 * √(tdMomentConst M π V₀ μmin η₀) * natCubeRoot T / √η₀ + tdPathBound M π V₀ / η₀ +
      4 * tdPathBound M π V₀

theorem weightedL2_prResidual_le [DecidableEq State] (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) {η₀ : ℝ} (h0 : 0 < η₀)
    (h1 : η₀ ≤ 1) (V₀ : State → ℝ) {μmin : ℝ} (hμmin0 : 0 < μmin)
    (hμmin : ∀ s, μmin ≤ μ.prob s) {T : ℕ} (hT : 1 ≤ T) (s : State) :
    weightedL2 (pathWeight M π μ)
        (fun ω : Fin T → Tuple State Action ↦ prResidual M π μ η₀ V₀ ω s) ≤
      prResidualBound M π V₀ μmin η₀ T := by
  have hw := pathWeight_nonneg M π μ (T := T)
  have hR : (fun ω : Fin T → Tuple State Action ↦ prResidual M π μ η₀ V₀ ω s) =
      (fun ω ↦ -∑ k : Fin T, prMartingaleTerm M π μ s k (tdIter M η₀ V₀ ω k) (ω k)) +
        (fun ω ↦ -(invStepSize η₀ T * tdError M π η₀ V₀ ω T s)) +
        (fun ω ↦ ∑ k ∈ range T,
          (invStepSize η₀ (k + 1) - invStepSize η₀ k) * tdError M π η₀ V₀ ω k s) +
        (fun ω ↦ (tdA M π μ *ᵥ (tdError M π η₀ V₀ ω T - tdError M π η₀ V₀ ω 0)) s) := by
    funext ω
    simp only [Pi.add_apply]
    rw [prResidual_apply M π μ h0 V₀ ω s]
    ring
  have hMart : weightedL2 (pathWeight M π μ) (fun ω : Fin T → Tuple State Action ↦
      ∑ k : Fin T, prMartingaleTerm M π μ s k (tdIter M η₀ V₀ ω k) (ω k)) ≤
      √(4 * tdPathBound M π V₀ ^ 2 + 12 * tdMomentConst M π V₀ μmin η₀ * η₀ * natCubeRoot T) :=
    weightedL2_le_sqrt (sum_pathWeight_mul_sq_prMartingale_le M π μ h0 h1 V₀ hμmin0 hμmin hT s)
  have hEnd := weightedL2_prEndpoint_le M π μ h0 h1 V₀ hμmin0 hμmin hT s
  have hTel := weightedL2_prTelescope_le M π μ h0 h1 V₀ hμmin0 hμmin hT s
  have hBdy := weightedL2_prBoundary_le M π μ h0.le h1 V₀ T s
  rw [hR]
  refine (weightedL2_add₄_le hw _ _ _ _).trans ?_
  rw [weightedL2_neg, weightedL2_neg]
  unfold prResidualBound
  have : 3 * √(tdMomentConst M π V₀ μmin η₀) * natCubeRoot T / √η₀ +
      √(tdMomentConst M π V₀ μmin η₀) * natCubeRoot T / √η₀ =
      4 * √(tdMomentConst M π V₀ μmin η₀) * natCubeRoot T / √η₀ := by ring
  linarith

/-- **Polyak–Ruppert remainder in `L²`.** For `0 < η₀ ≤ 1`, `0 < μmin ≤ min_s μ(s)`, `T ≥ 1` and
every state `s`,
`‖(√T Δ̄_T − W_T)(s)‖_{L²} ≤ |State| · prResidualBound / ((1−γ) μmin √T)`,
where `W_T = −A⁻¹ T^{-1/2} ∑_k ξ_k` (`prGaussPart`). -/
theorem weightedL2_scaledError_sub_prGaussPart_le [DecidableEq State]
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (μ : FiniteDistribution State) {η₀ : ℝ} (h0 : 0 < η₀) (h1 : η₀ ≤ 1) (V₀ : State → ℝ)
    {μmin : ℝ} (hμmin0 : 0 < μmin) (hμmin : ∀ s, μmin ≤ μ.prob s) {T : ℕ} (hT : 1 ≤ T)
    (s : State) :
    weightedL2 (pathWeight M π μ) (fun ω : Fin T → Tuple State Action ↦
        scaledError M π η₀ V₀ ω s - prGaussPart M π μ ω s) ≤
      Fintype.card State * prResidualBound M π V₀ μmin η₀ T /
        ((1 - M.discount) * μmin * Real.sqrt T) := by
  have hw := pathWeight_nonneg M π μ (T := T)
  have hc : 0 < (1 - M.discount) * μmin := mul_pos (by linarith [M.discount_lt_one]) hμmin0
  have hT0 : (0 : ℝ) < T := by exact_mod_cast hT
  have hsT : 0 < Real.sqrt T := Real.sqrt_pos.2 hT0
  have heq : (fun ω : Fin T → Tuple State Action ↦
      scaledError M π η₀ V₀ ω s - prGaussPart M π μ ω s) = fun ω ↦
        (Real.sqrt T)⁻¹ * ((tdA M π μ)⁻¹ *ᵥ prResidual M π μ η₀ V₀ ω) s := by
    funext ω
    have := congrFun (scaledError_sub_prGaussPart M π μ hμmin0 hμmin η₀ V₀ hT ω) s
    simpa using this
  rw [heq, weightedL2_const_mul, abs_of_nonneg (inv_nonneg.2 hsT.le)]
  have hpt : ∀ ω : Fin T → Tuple State Action,
      |((tdA M π μ)⁻¹ *ᵥ prResidual M π μ η₀ V₀ ω) s| ≤
        |(1 / ((1 - M.discount) * μmin)) * ∑ s', abs (prResidual M π μ η₀ V₀ ω s')| := by
    intro ω
    rw [abs_of_nonneg (show (0 : ℝ) ≤ 1 / ((1 - M.discount) * μmin) *
      ∑ s', abs (prResidual M π μ η₀ V₀ ω s') from
        mul_nonneg (by positivity) (sum_nonneg fun _ _ ↦ abs_nonneg _))]
    calc _ ≤ ‖(tdA M π μ)⁻¹ *ᵥ prResidual M π μ η₀ V₀ ω‖ := abs_apply_le_norm _ s
      _ ≤ ‖prResidual M π μ η₀ V₀ ω‖ / ((1 - M.discount) * μmin) :=
          norm_tdA_inv_mulVec_le M π μ hμmin0 hμmin _
      _ ≤ (∑ s', abs (prResidual M π μ η₀ V₀ ω s')) / ((1 - M.discount) * μmin) := by
          refine div_le_div_of_nonneg_right ?_ hc.le
          refine (pi_norm_le_iff_of_nonneg (sum_nonneg fun _ _ ↦ abs_nonneg _)).2 fun s' ↦ ?_
          rw [Real.norm_eq_abs]
          exact single_le_sum (f := fun s' ↦ abs (prResidual M π μ η₀ V₀ ω s'))
            (fun _ _ ↦ abs_nonneg _) (mem_univ s')
      _ = _ := by ring
  have hmono := weightedL2_mono hw hpt
  rw [weightedL2_const_mul, abs_of_nonneg (by positivity)] at hmono
  have hsum := weightedL2_sum_le hw univ (fun s' ω ↦ abs (prResidual M π μ η₀ V₀ ω s'))
  simp only [weightedL2_abs] at hsum
  have hbound : ∑ s' : State, weightedL2 (pathWeight M π μ)
      (fun ω : Fin T → Tuple State Action ↦ prResidual M π μ η₀ V₀ ω s') ≤
      Fintype.card State * prResidualBound M π V₀ μmin η₀ T := by
    calc _ ≤ ∑ _s' : State, prResidualBound M π V₀ μmin η₀ T :=
          sum_le_sum fun s' _ ↦ weightedL2_prResidual_le M π μ h0 h1 V₀ hμmin0 hμmin hT s'
      _ = _ := by rw [sum_const, card_univ, nsmul_eq_mul]
  calc (Real.sqrt T)⁻¹ * weightedL2 (pathWeight M π μ)
        (fun ω ↦ ((tdA M π μ)⁻¹ *ᵥ prResidual M π μ η₀ V₀ ω) s)
      ≤ (Real.sqrt T)⁻¹ * (1 / ((1 - M.discount) * μmin) *
          (Fintype.card State * prResidualBound M π V₀ μmin η₀ T)) := by
        refine mul_le_mul_of_nonneg_left (hmono.trans ?_) (inv_nonneg.2 hsT.le)
        exact mul_le_mul_of_nonneg_left (hsum.trans hbound) (by positivity)
    _ = _ := by field_simp

/-! ## The `T^{-1/6}` form -/

/-- `K_R = 2D + √(12Cη₀) + 4√C/√η₀ + D/η₀ + 4D`. -/
noncomputable def prRemainderConst (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (V₀ : State → ℝ) (μmin η₀ : ℝ) : ℝ :=
  2 * tdPathBound M π V₀ + √(12 * tdMomentConst M π V₀ μmin η₀ * η₀) +
    4 * √(tdMomentConst M π V₀ μmin η₀) / √η₀ + tdPathBound M π V₀ / η₀ +
      4 * tdPathBound M π V₀

theorem prResidualBound_le (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (V₀ : State → ℝ) {μmin η₀ : ℝ} (hμmin0 : 0 < μmin) (h0 : 0 < η₀) {T : ℕ} (hT : 1 ≤ T) :
    prResidualBound M π V₀ μmin η₀ T ≤ prRemainderConst M π V₀ μmin η₀ * natCubeRoot T := by
  set D := tdPathBound M π V₀
  set C := tdMomentConst M π V₀ μmin η₀
  set u := natCubeRoot T
  have hD : 0 ≤ D := tdPathBound_nonneg M π V₀
  have hC : 0 ≤ C := tdMomentConst_nonneg M π V₀ hμmin0
  have hu : 1 ≤ u := by
    have := natCubeRoot_mono hT; rwa [natCubeRoot_one] at this
  have hq : 0 ≤ 12 * C * η₀ := by positivity
  have hsq : √(4 * D ^ 2 + 12 * C * η₀ * u) ≤ (2 * D + √(12 * C * η₀)) * u := by
    have hs := Real.sq_sqrt hq
    have hs0 := Real.sqrt_nonneg (12 * C * η₀)
    refine (Real.sqrt_le_sqrt ?_).trans_eq (Real.sqrt_sq (by positivity))
    nlinarith [mul_nonneg (mul_nonneg hD hs0) (sq_nonneg u), mul_le_mul_of_nonneg_left hu hq,
      mul_nonneg (sq_nonneg D) (sub_nonneg.2 (one_le_pow₀ hu : (1 : ℝ) ≤ u ^ 2)),
      mul_nonneg hq (sub_nonneg.2 hu), mul_nonneg (mul_nonneg hq (sub_nonneg.2 hu)) (by linarith : (0:ℝ) ≤ u)]
  have h3 : D / η₀ ≤ D / η₀ * u := le_mul_of_one_le_right (by positivity) hu
  have h4 : 4 * D ≤ 4 * D * u := le_mul_of_one_le_right (by positivity) hu
  unfold prResidualBound prRemainderConst
  have e : 4 * √C * u / √η₀ = 4 * √C / √η₀ * u := by ring
  nlinarith [e]

/-- **Polyak–Ruppert remainder, rate form.** Under the hypotheses of
`weightedL2_scaledError_sub_prGaussPart_le`,
`‖(√T Δ̄_T − W_T)(s)‖_{L²} ≤ |State| K_R / ((1−γ) μmin) · T^{-1/6}`. -/
theorem weightedL2_scaledError_sub_prGaussPart_le_rpow [DecidableEq State]
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (μ : FiniteDistribution State) {η₀ : ℝ} (h0 : 0 < η₀) (h1 : η₀ ≤ 1) (V₀ : State → ℝ)
    {μmin : ℝ} (hμmin0 : 0 < μmin) (hμmin : ∀ s, μmin ≤ μ.prob s) {T : ℕ} (hT : 1 ≤ T)
    (s : State) :
    weightedL2 (pathWeight M π μ) (fun ω : Fin T → Tuple State Action ↦
        scaledError M π η₀ V₀ ω s - prGaussPart M π μ ω s) ≤
      Fintype.card State * prRemainderConst M π V₀ μmin η₀ / ((1 - M.discount) * μmin) *
        (T : ℝ) ^ (-(1 / 6 : ℝ)) := by
  have hc : 0 < (1 - M.discount) * μmin := mul_pos (by linarith [M.discount_lt_one]) hμmin0
  have hT0 : (0 : ℝ) < T := by exact_mod_cast hT
  have hsT : 0 < Real.sqrt T := Real.sqrt_pos.2 hT0
  refine (weightedL2_scaledError_sub_prGaussPart_le M π μ h0 h1 V₀ hμmin0 hμmin hT s).trans ?_
  rw [← natCubeRoot_div_sqrt_eq hT]
  have hb := prResidualBound_le M π V₀ hμmin0 h0 hT
  have hS : (0 : ℝ) ≤ Fintype.card State := Nat.cast_nonneg _
  calc (Fintype.card State : ℝ) * prResidualBound M π V₀ μmin η₀ T /
        ((1 - M.discount) * μmin * Real.sqrt T)
      ≤ Fintype.card State * (prRemainderConst M π V₀ μmin η₀ * natCubeRoot T) /
          ((1 - M.discount) * μmin * Real.sqrt T) := by
        gcongr
    _ = _ := by field_simp

/-! ## The covariance of the noise sum (C43) -/

/-- `E_x (∑_s c_s ξ_x(s))² = ∑_s c_s² Γ_true(s)`. -/
theorem sum_tupleProb_mul_sq_sum_noiseVec [DecidableEq State] (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) (c : State → ℝ) :
    ∑ x, tupleProb M π μ x * (∑ s, c s * noiseVec M π x s) ^ 2 =
      ∑ s, c s ^ 2 * trueGamma M π μ s := by
  have e : ∀ x : Tuple State Action, tupleProb M π μ x * (∑ s, c s * noiseVec M π x s) ^ 2 =
      ∑ s, ∑ s', c s * c s' * (tupleProb M π μ x * (noiseVec M π x s * noiseVec M π x s')) := by
    intro x
    rw [sq, sum_mul_sum, mul_sum]
    exact sum_congr rfl fun s _ ↦ by rw [mul_sum]; exact sum_congr rfl fun s' _ ↦ by ring
  simp_rw [e]
  rw [sum_comm]
  refine sum_congr rfl fun s _ ↦ ?_
  rw [sum_comm]
  simp_rw [← mul_sum, sum_tupleProb_mul_noiseVec_mul, mul_ite, mul_zero]
  rw [sum_ite_eq]
  simp only [mem_univ, if_true]
  ring

/-- **The noise sum has covariance `T · diag(Γ_true)`**: for every `c : State → ℝ`,
`E (∑_s c_s (∑_{k<T} ξ_k)(s))² = T ∑_s c_s² Γ_true(s)`. With the centring
`sum_pathWeight_mul_prNoiseSum`, this gives `Cov(W_T) = A⁻¹ diag(Γ_true) A⁻ᵀ`
(`sum_pathWeight_mul_prGaussPart_mul`), not the printed `A⁻¹ diag(Γ_printed) A⁻ᵀ` (C43). -/
theorem sum_pathWeight_mul_sq_prNoiseSum [DecidableEq State] (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) (c : State → ℝ) (T : ℕ) :
    ∑ ω : Fin T → Tuple State Action, pathWeight M π μ ω *
        (∑ s, c s * prNoiseSum M π ω s) ^ 2 =
      T * ∑ s, c s ^ 2 * trueGamma M π μ s := by
  have hf : ∀ (k : ℕ) (V : State → ℝ), ∑ x, tupleProb M π μ x *
      (fun (_ : ℕ) (_ : State → ℝ) (x : Tuple State Action) ↦ ∑ s, c s * noiseVec M π x s) k V x
        = 0 := by
    intro k V
    simp only [mul_sum]
    rw [sum_comm]
    simp_rw [mul_left_comm (tupleProb M π μ _), ← mul_sum, sum_tupleProb_mul_noiseVec, mul_zero,
      sum_const_zero]
  have key := sum_pathWeight_mul_sq_sum_eq M π μ 0 0 _ hf T
  have hcomm : ∀ ω : Fin T → Tuple State Action, ∑ s, c s * prNoiseSum M π ω s =
      ∑ k : Fin T, ∑ s, c s * noiseVec M π (ω k) s := by
    intro ω
    simp only [prNoiseSum, Finset.sum_apply, mul_sum]
    exact sum_comm
  simp_rw [hcomm]
  rw [key]
  simp only [sum_tupleProb_mul_sq_sum_noiseVec, ← sum_mul, sum_pathWeight, one_mul, sum_const,
    card_range, nsmul_eq_mul]

/-- The noise sum is centred on the path law: `E (∑_{k<T} ξ_k)(s) = 0`. -/
theorem sum_pathWeight_mul_prNoiseSum [DecidableEq State] (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) (T : ℕ) (s : State) :
    ∑ ω : Fin T → Tuple State Action, pathWeight M π μ ω * prNoiseSum M π ω s = 0 := by
  induction T with
  | zero => simp [prNoiseSum]
  | succ T ih =>
    rw [Fintype.sum_fin_succ_snoc]
    have : ∀ ω : Fin T → Tuple State Action,
        ∑ x, pathWeight M π μ (Fin.snoc ω x : Fin (T + 1) → Tuple State Action) *
          prNoiseSum M π (Fin.snoc ω x : Fin (T + 1) → Tuple State Action) s =
        pathWeight M π μ ω * prNoiseSum M π ω s := by
      intro ω
      simp only [pathWeight_snoc, prNoiseSum, Finset.sum_apply, Fin.sum_univ_castSucc,
        Fin.snoc_castSucc, Fin.snoc_last]
      have h0 := sum_tupleProb_mul_noiseVec M π μ s
      have h1 := sum_tupleProb M π μ
      simp only [mul_add, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]
      rw [← Finset.sum_mul, h1, h0]; ring
    simp_rw [this]; exact ih

/-- Bilinear form of the noise covariance:
`E[(∑_s c_s N(s))(∑_s d_s N(s))] = T ∑_s c_s d_s Γ_true(s)`, `N = ∑_{k<T} ξ_k`. -/
theorem sum_pathWeight_mul_sum_prNoiseSum_mul [DecidableEq State]
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (μ : FiniteDistribution State) (c d : State → ℝ) (T : ℕ) :
    ∑ ω : Fin T → Tuple State Action, pathWeight M π μ ω *
        ((∑ s, c s * prNoiseSum M π ω s) * (∑ s, d s * prNoiseSum M π ω s)) =
      T * ∑ s, c s * d s * trueGamma M π μ s := by
  have hcd := sum_pathWeight_mul_sq_prNoiseSum M π μ (c + d) T
  have hc := sum_pathWeight_mul_sq_prNoiseSum M π μ c T
  have hd := sum_pathWeight_mul_sq_prNoiseSum M π μ d T
  have e : ∀ ω : Fin T → Tuple State Action, pathWeight M π μ ω *
      (∑ s, (c + d) s * prNoiseSum M π ω s) ^ 2 =
      pathWeight M π μ ω * (∑ s, c s * prNoiseSum M π ω s) ^ 2 +
        pathWeight M π μ ω * (∑ s, d s * prNoiseSum M π ω s) ^ 2 +
        2 * (pathWeight M π μ ω *
          ((∑ s, c s * prNoiseSum M π ω s) * (∑ s, d s * prNoiseSum M π ω s))) := by
    intro ω
    simp only [Pi.add_apply, add_mul, sum_add_distrib]
    ring
  simp_rw [e, sum_add_distrib, ← mul_sum] at hcd
  rw [hc, hd] at hcd
  have e2 : ∑ s, (c + d) s ^ 2 * trueGamma M π μ s = ∑ s, c s ^ 2 * trueGamma M π μ s +
      ∑ s, d s ^ 2 * trueGamma M π μ s + 2 * ∑ s, c s * d s * trueGamma M π μ s := by
    simp only [Pi.add_apply, mul_sum, ← sum_add_distrib]
    exact sum_congr rfl fun s _ ↦ by ring
  rw [e2] at hcd
  linarith

/-- `E[N(s) N(s')] = T · 1{s = s'} Γ_true(s)` for the noise sum `N = ∑_{k<T} ξ_k`. -/
theorem sum_pathWeight_mul_prNoiseSum_mul [DecidableEq State]
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (μ : FiniteDistribution State) (T : ℕ) (s s' : State) :
    ∑ ω : Fin T → Tuple State Action, pathWeight M π μ ω *
        (prNoiseSum M π ω s * prNoiseSum M π ω s') =
      T * if s = s' then trueGamma M π μ s else 0 := by
  have h := sum_pathWeight_mul_sum_prNoiseSum_mul M π μ (Pi.single s 1) (Pi.single s' 1) T
  simp only [Pi.single_apply, ite_mul, one_mul, zero_mul, sum_ite_eq', mem_univ, if_true] at h
  rw [h]

theorem prGaussPart_apply [DecidableEq State] (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) {T : ℕ}
    (ω : Fin T → Tuple State Action) (s : State) :
    prGaussPart M π μ ω s =
      -((Real.sqrt T)⁻¹ * ∑ u, (tdA M π μ)⁻¹ s u * prNoiseSum M π ω u) := by
  simp [prGaussPart, Matrix.mulVec, dotProduct]

/-- `W_T` is centred: `E W_T(s) = 0`. -/
theorem sum_pathWeight_mul_prGaussPart [DecidableEq State] (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) (T : ℕ) (s : State) :
    ∑ ω : Fin T → Tuple State Action, pathWeight M π μ ω * prGaussPart M π μ ω s = 0 := by
  simp_rw [prGaussPart_apply, mul_neg, sum_neg_distrib, mul_sum]
  rw [sum_comm]
  simp_rw [show ∀ (u : State) (ω : Fin T → Tuple State Action), pathWeight M π μ ω *
      ((Real.sqrt T)⁻¹ * ((tdA M π μ)⁻¹ s u * prNoiseSum M π ω u)) =
      (Real.sqrt T)⁻¹ * (tdA M π μ)⁻¹ s u * (pathWeight M π μ ω * prNoiseSum M π ω u) from
    fun u ω ↦ by ring]
  simp_rw [← mul_sum, sum_pathWeight_mul_prNoiseSum, mul_zero, sum_const_zero, neg_zero]

/-- **Covariance of the leading term** (C43): for `T ≥ 1`,
`E[W_T(s) W_T(s')] = (A⁻¹ diag(Γ_true) A⁻ᵀ)(s, s')`, with `A⁻¹ = Matrix.inv (tdA M π μ)`.
`A⁻¹` is the true inverse only when `0 < μmin ≤ μ(s)` for all `s` (`tdA_isUnit`); otherwise
`Matrix.inv` returns the junk value `0`, so `W_T ≡ 0` and the identity reduces to `0 = 0`. -/
theorem sum_pathWeight_mul_prGaussPart_mul [DecidableEq State] (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) {T : ℕ} (hT : 1 ≤ T)
    (s s' : State) :
    ∑ ω : Fin T → Tuple State Action, pathWeight M π μ ω *
        (prGaussPart M π μ ω s * prGaussPart M π μ ω s') =
      ((tdA M π μ)⁻¹ * Matrix.diagonal (trueGamma M π μ) * ((tdA M π μ)⁻¹)ᵀ) s s' := by
  have hT0 : (0 : ℝ) < T := by exact_mod_cast hT
  have hss : (Real.sqrt T)⁻¹ * (Real.sqrt T)⁻¹ = (T : ℝ)⁻¹ := by
    rw [← mul_inv, Real.mul_self_sqrt hT0.le]
  have h := sum_pathWeight_mul_sum_prNoiseSum_mul M π μ (fun u ↦ (tdA M π μ)⁻¹ s u)
    (fun u ↦ (tdA M π μ)⁻¹ s' u) T
  have e : ∀ ω : Fin T → Tuple State Action, pathWeight M π μ ω *
      (prGaussPart M π μ ω s * prGaussPart M π μ ω s') =
      (T : ℝ)⁻¹ * (pathWeight M π μ ω *
        ((∑ u, (tdA M π μ)⁻¹ s u * prNoiseSum M π ω u) *
          (∑ u, (tdA M π μ)⁻¹ s' u * prNoiseSum M π ω u))) := by
    intro ω
    rw [prGaussPart_apply, prGaussPart_apply, ← hss]
    ring
  simp_rw [e]
  rw [← mul_sum, h, ← mul_assoc, inv_mul_cancel₀ hT0.ne', one_mul]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.diagonal_apply, mul_ite, mul_zero,
    sum_ite_eq', mem_univ, if_true]
  exact sum_congr rfl fun u _ ↦ by ring

/-- **The Polyak–Ruppert remainder tends to zero in `L²`** (from the `T^{-1/6}` rate). -/
theorem tendsto_weightedL2_scaledError_sub_prGaussPart [DecidableEq State]
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (μ : FiniteDistribution State) {η₀ : ℝ} (h0 : 0 < η₀) (h1 : η₀ ≤ 1) (V₀ : State → ℝ)
    {μmin : ℝ} (hμmin0 : 0 < μmin) (hμmin : ∀ s, μmin ≤ μ.prob s) (s : State) :
    Filter.Tendsto (fun T : ℕ ↦ weightedL2 (pathWeight M π μ)
        (fun ω : Fin T → Tuple State Action ↦
          scaledError M π η₀ V₀ ω s - prGaussPart M π μ ω s)) Filter.atTop (nhds 0) := by
  set K := Fintype.card State * prRemainderConst M π V₀ μmin η₀ / ((1 - M.discount) * μmin)
  have hlim : Filter.Tendsto (fun T : ℕ ↦ K * (T : ℝ) ^ (-(1 / 6 : ℝ))) Filter.atTop (nhds 0) := by
    have := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 6)).comp
      tendsto_natCast_atTop_atTop
    simpa using this.const_mul K
  refine squeeze_zero' (Filter.Eventually.of_forall fun T ↦ weightedL2_nonneg _ _) ?_ hlim
  filter_upwards [Filter.eventually_ge_atTop 1] with T hT
  exact weightedL2_scaledError_sub_prGaussPart_le_rpow M π μ h0 h1 V₀ hμmin0 hμmin hT s

end StatisticalRL.Ch7Rest.TDInference
