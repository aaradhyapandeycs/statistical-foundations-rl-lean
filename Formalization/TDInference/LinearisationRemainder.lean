import Formalization.TDInference.Kernel
import Formalization.TDInference.PolyakRuppertRemainder

/-!
# Theorem 7.11 support (M5, B4): the linearisation remainder is `O(T^{-1/3})` in `L²`

Source: `chapters/inference.tex:52–117` (sampling, update, `V̄_T`, `Δ̄_T`, `A`), :134 (`η_t`).
Library infrastructure only; no source result is claimed.

With `E_T = √TΔ̄_T − linPart` (`scaledError_sub_linPart_eq`):

  `E_T = T^{-1/2}[(∑_{t<T} G_{0,t+1}) Δ_0 − ∑_k linWeight T k ζ_k]`, `ζ_k = (A_{ω k} − A)Δ_k`.

* The transient is deterministic and bounded by `K_β D/η₀` (`abs_linTransient_le`).
* The martingale part has `E(·)² ≤ 4K_β²(D² + 3Cη₀u_T)` by martingale orthogonality
  (`sum_pathWeight_mul_sq_linMart_le`; `tdSecondMoment_le` gives `E Δ_k(s)² ≤ Cη_k`).
* `weightedL2_scaledError_sub_linPart_le`: for `0 < η₀ ≤ 1`, `0 < μmin ≤ μ(s)`, `T ≥ 1`, every
  `V₀` and every state `s`,
  `‖E_T(s)‖_{L²} ≤ K_E T^{-1/3}`, `K_E = K_β (D/η₀ + 2D + 2√(3Cη₀))` (`linRemainderConst`),
  with `B, D, C` of `TDInference/Noise.lean` and `K_β = linWeightConst`. No `Γ ≻ 0` and no
  stationarity hypothesis.
-/

open Finset Matrix
open scoped BigOperators

namespace StatisticalRL.Ch7Rest.TDInference

open StatisticalRL.Probability StatisticalRL.Analysis

variable {State Action : Type} [Fintype State] [Fintype Action]

/-! ## Rate conversions -/

theorem inv_sqrt_le_rpow {T : ℕ} (hT : 1 ≤ T) :
    (Real.sqrt T)⁻¹ ≤ (T : ℝ) ^ (-(1 / 3 : ℝ)) := by
  have hT1 : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hT0 : (0 : ℝ) ≤ T := by linarith
  rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hT0]
  exact Real.rpow_le_rpow_of_exponent_le hT1 (by norm_num)

theorem inv_sqrt_mul_sqrt_natCubeRoot {T : ℕ} (hT : 1 ≤ T) :
    (Real.sqrt T)⁻¹ * Real.sqrt (natCubeRoot T) = (T : ℝ) ^ (-(1 / 3 : ℝ)) := by
  have hT0 : (0 : ℝ) < T := by exact_mod_cast hT
  rw [natCubeRoot, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_neg hT0.le,
    ← Real.rpow_mul hT0.le, ← Real.rpow_add hT0]
  norm_num

theorem natCubeRoot_sq_div {T : ℕ} (hT : 1 ≤ T) :
    natCubeRoot T ^ 2 / T = (T : ℝ) ^ (-(1 / 3 : ℝ)) := by
  have hT0 : (0 : ℝ) < T := by exact_mod_cast hT
  rw [← natCast_rpow_two_thirds_eq, ← Real.rpow_sub_one hT0.ne']
  norm_num

/-! ## The transient -/

/-- `|((∑_{t<T} G_{0,t+1}) Δ_0)(s)| ≤ K_β ‖Δ_0‖_∞ / η₀`. -/
theorem abs_linTransient_le [DecidableEq State] (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) {η₀ μmin : ℝ}
    (h0 : 0 < η₀) (h1 : η₀ ≤ 1) (hμmin0 : 0 < μmin) (hμmin : ∀ s, μmin ≤ μ.prob s) (T : ℕ)
    (v : State → ℝ) (s : State) :
    |((∑ t ∈ range T, linKernel M π μ η₀ 0 (t + 1)) *ᵥ v) s| ≤
      linWeightConst M μmin η₀ * ‖v‖ / η₀ := by
  obtain ⟨he0, hae, hanti, hE, hslow⟩ := linStepSeq_facts M μ hμmin0 hμmin h0 h1
  have ha := linRate_pos M hμmin0
  have hK := linStepSeq_mul_contrSum_le M μ hμmin0 hμmin h0 h1 T 0
  have he0' : linStepSeq η₀ 0 = η₀ := by simp [linStepSeq, stepSize]
  rw [he0'] at hK
  have hσ : contrSum (linRate M μmin) (linStepSeq η₀) T 0 ≤ linWeightConst M μmin η₀ / η₀ := by
    rw [le_div_iff₀ h0, mul_comm]; exact hK
  have hterm : ∀ t ∈ range T, ‖linKernel M π μ η₀ 0 (t + 1) *ᵥ v‖ ≤
      contrProd (linRate M μmin) (linStepSeq η₀) 1 (t + 1) * ‖v‖ := by
    intro t _
    refine (norm_linKernel_mulVec_le M π μ h0.le h1 hμmin0 hμmin 0 (t + 1) v).trans ?_
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg v)
    have h := contrProd_succ_bot (a := linRate M μmin) (e := linStepSeq η₀) (Nat.succ_pos t)
    rw [zero_add] at h
    rw [h]
    have := contrProd_nonneg hae 1 (t + 1)
    nlinarith [mul_nonneg ha.le (he0 0)]
  calc |((∑ t ∈ range T, linKernel M π μ η₀ 0 (t + 1)) *ᵥ v) s|
      ≤ ‖(∑ t ∈ range T, linKernel M π μ η₀ 0 (t + 1)) *ᵥ v‖ := abs_apply_le_norm _ s
    _ ≤ ∑ t ∈ range T, ‖linKernel M π μ η₀ 0 (t + 1) *ᵥ v‖ := by
        rw [sum_mulVec]; exact norm_sum_le _ _
    _ ≤ ∑ t ∈ range T, contrProd (linRate M μmin) (linStepSeq η₀) 1 (t + 1) * ‖v‖ :=
        sum_le_sum hterm
    _ = contrSum (linRate M μmin) (linStepSeq η₀) T 0 * ‖v‖ := by
        rw [← sum_mul, contrSum, range_eq_Ico]
    _ ≤ linWeightConst M μmin η₀ / η₀ * ‖v‖ := mul_le_mul_of_nonneg_right hσ (norm_nonneg v)
    _ = _ := by ring

/-! ## The martingale part -/

/-- The `k`-th martingale increment of `E_T(s)`:
`∑_u linWeight T k (s,u) ((A_x − A)(V − V^π))(u)`. -/
noncomputable def linMartTerm [DecidableEq State] (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) (η₀ : ℝ) (T : ℕ)
    (s : State) (k : ℕ) (V : State → ℝ) (x : Tuple State Action) : ℝ :=
  ∑ u, linWeight M π μ η₀ T k s u * prMartingaleTerm M π μ u k V x

theorem sum_tupleProb_mul_linMartTerm [DecidableEq State] (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) (η₀ : ℝ) (T : ℕ)
    (s : State) (k : ℕ) (V : State → ℝ) :
    ∑ x, tupleProb M π μ x * linMartTerm M π μ η₀ T s k V x = 0 := by
  simp only [linMartTerm, mul_sum]
  rw [sum_comm]
  refine sum_eq_zero fun u _ ↦ ?_
  simp_rw [mul_left_comm (tupleProb M π μ _)]
  rw [← mul_sum, sum_tupleProb_mul_prMartingaleTerm, mul_zero]

/-- One-step second moment of the increment: with `|w(u)| ≤ K`,
`E_x (∑_u w(u) ζ_x(u))² ≤ K² E_x (2Δ(s_x)² + 2Δ(s'_x)²)`. -/
theorem sum_tupleProb_mul_sq_linMartTerm_le [DecidableEq State] (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) (w : State → ℝ) {K : ℝ}
    (hw : ∀ u, |w u| ≤ K) (k : ℕ) (V : State → ℝ) :
    ∑ x, tupleProb M π μ x * (∑ u, w u * prMartingaleTerm M π μ u k V x) ^ 2 ≤
      K ^ 2 * ∑ x : Tuple State Action, tupleProb M π μ x *
        (2 * (V x.1 - M.valueFixedPoint π x.1) ^ 2 +
          2 * (V x.2.2 - M.valueFixedPoint π x.2.2) ^ 2) := by
  have hγ0 := M.discount_nonneg
  have hγ1 := M.discount_lt_one
  set g : Tuple State Action → ℝ :=
    fun x ↦ ∑ u, w u * sampleA M x (V - M.valueFixedPoint π) u with hg
  have hgx : ∀ x : Tuple State Action, g x = w x.1 * ((V x.1 - M.valueFixedPoint π x.1) -
      M.discount * (V x.2.2 - M.valueFixedPoint π x.2.2)) := by
    intro x
    simp only [hg, sampleA_apply, Pi.sub_apply, mul_ite, mul_zero, sum_ite_eq', mem_univ,
      if_true]
  have hmean : ∑ x, tupleProb M π μ x * g x =
      ∑ u, w u * (tdA M π μ *ᵥ (V - M.valueFixedPoint π)) u := by
    simp only [hg, mul_sum]
    rw [sum_comm]
    refine sum_congr rfl fun u _ ↦ ?_
    simp_rw [mul_left_comm (tupleProb M π μ _)]
    rw [← mul_sum, sum_tupleProb_mul_sampleA]
  have hcent : ∀ x, ∑ u, w u * prMartingaleTerm M π μ u k V x =
      g x - ∑ x', tupleProb M π μ x' * g x' := by
    intro x
    rw [hmean]
    simp only [hg]
    rw [← sum_sub_distrib]
    refine sum_congr rfl fun u _ ↦ ?_
    simp only [prMartingaleTerm]
    ring
  calc ∑ x, tupleProb M π μ x * (∑ u, w u * prMartingaleTerm M π μ u k V x) ^ 2
      = ∑ x, tupleProb M π μ x * (g x - ∑ x', tupleProb M π μ x' * g x') ^ 2 :=
        sum_congr rfl fun x _ ↦ by rw [hcent x]
    _ ≤ ∑ x, tupleProb M π μ x * g x ^ 2 := sum_mul_sq_sub_mean_le (sum_tupleProb M π μ) g
    _ ≤ _ := by
        rw [mul_sum]
        refine sum_le_sum fun x _ ↦ ?_
        rw [hgx, mul_left_comm]
        refine mul_le_mul_of_nonneg_left ?_ (tupleProb_nonneg M π μ x)
        have hK : w x.1 ^ 2 ≤ K ^ 2 := by
          rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hw x.1) 2
        set d₁ := V x.1 - M.valueFixedPoint π x.1
        set d₂ := V x.2.2 - M.valueFixedPoint π x.2.2
        have hd : (d₁ - M.discount * d₂) ^ 2 ≤ 2 * d₁ ^ 2 + 2 * d₂ ^ 2 := by
          nlinarith [sq_nonneg (d₁ + M.discount * d₂),
            mul_le_mul_of_nonneg_right (mul_le_mul hγ1.le hγ1.le hγ0 zero_le_one) (sq_nonneg d₂)]
        rw [mul_pow]
        exact mul_le_mul hK hd (sq_nonneg _) (sq_nonneg _)

/-- Averaging the bound over the length-`k` path law: `≤ 4Q` when `q_k ≤ Q` coordinatewise. -/
theorem sum_pathWeight_mul_sum_tupleProb_sq_le [DecidableEq State]
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (μ : FiniteDistribution State) (η₀ : ℝ) (V₀ : State → ℝ) (k : ℕ) {Q : ℝ}
    (hQ : ∀ u, tdSecondMoment M π μ η₀ V₀ k u ≤ Q) :
    ∑ ω : Fin k → Tuple State Action, pathWeight M π μ ω *
      ∑ x : Tuple State Action, tupleProb M π μ x *
        (2 * (tdIter M η₀ V₀ ω k x.1 - M.valueFixedPoint π x.1) ^ 2 +
          2 * (tdIter M η₀ V₀ ω k x.2.2 - M.valueFixedPoint π x.2.2) ^ 2) ≤ 4 * Q := by
  have e : ∑ ω : Fin k → Tuple State Action, pathWeight M π μ ω *
      ∑ x : Tuple State Action, tupleProb M π μ x *
        (2 * (tdIter M η₀ V₀ ω k x.1 - M.valueFixedPoint π x.1) ^ 2 +
          2 * (tdIter M η₀ V₀ ω k x.2.2 - M.valueFixedPoint π x.2.2) ^ 2) =
      ∑ x : Tuple State Action, tupleProb M π μ x *
        (2 * tdSecondMoment M π μ η₀ V₀ k x.1 + 2 * tdSecondMoment M π μ η₀ V₀ k x.2.2) := by
    simp only [tdSecondMoment, mul_sum, mul_add]
    rw [sum_comm]
    refine sum_congr rfl fun x _ ↦ ?_
    rw [← sum_add_distrib]
    refine sum_congr rfl fun ω _ ↦ ?_
    ring
  rw [e]
  calc _ ≤ ∑ x : Tuple State Action, tupleProb M π μ x * (4 * Q) := by
        refine sum_le_sum fun x _ ↦ mul_le_mul_of_nonneg_left ?_ (tupleProb_nonneg M π μ x)
        linarith [hQ x.1, hQ x.2.2]
    _ = 4 * Q := by rw [← sum_mul, sum_tupleProb, one_mul]

/-- `E(∑_k linMartTerm_k)² ≤ 4K_β²(D² + 3Cη₀u_T)`. -/
theorem sum_pathWeight_mul_sq_linMart_le [DecidableEq State] (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) {η₀ : ℝ} (h0 : 0 < η₀)
    (h1 : η₀ ≤ 1) (V₀ : State → ℝ) {μmin : ℝ} (hμmin0 : 0 < μmin)
    (hμmin : ∀ s, μmin ≤ μ.prob s) {T : ℕ} (hT : 1 ≤ T) (s : State) :
    ∑ ω : Fin T → Tuple State Action, pathWeight M π μ ω *
        (∑ k : Fin T, linMartTerm M π μ η₀ T s k (tdIter M η₀ V₀ ω k) (ω k)) ^ 2 ≤
      4 * linWeightConst M μmin η₀ ^ 2 * (tdPathBound M π V₀ ^ 2 +
        3 * tdMomentConst M π V₀ μmin η₀ * η₀ * natCubeRoot T) := by
  set K := linWeightConst M μmin η₀
  set D := tdPathBound M π V₀
  set C := tdMomentConst M π V₀ μmin η₀
  have hK0 : 0 ≤ K := linWeightConst_nonneg M hμmin0 h0
  rw [sum_pathWeight_mul_sq_sum_eq M π μ η₀ V₀ (fun k V x ↦ linMartTerm M π μ η₀ T s k V x)
    (fun k V ↦ sum_tupleProb_mul_linMartTerm M π μ η₀ T s k V) T]
  have hstep : ∀ k (Q : ℝ), (∀ u, tdSecondMoment M π μ η₀ V₀ k u ≤ Q) →
      ∑ ω : Fin k → Tuple State Action, pathWeight M π μ ω *
        ∑ x, tupleProb M π μ x * linMartTerm M π μ η₀ T s k (tdIter M η₀ V₀ ω k) x ^ 2 ≤
        4 * K ^ 2 * Q := by
    intro k Q hQ
    have hw : ∀ u, |linWeight M π μ η₀ T k s u| ≤ K :=
      abs_apply_le_of_norm_mulVec_le _ hK0
        (norm_linWeight_mulVec_le M π μ h0 h1 hμmin0 hμmin T k) s
    calc _ ≤ ∑ ω : Fin k → Tuple State Action, pathWeight M π μ ω *
          (K ^ 2 * ∑ x : Tuple State Action, tupleProb M π μ x *
            (2 * (tdIter M η₀ V₀ ω k x.1 - M.valueFixedPoint π x.1) ^ 2 +
              2 * (tdIter M η₀ V₀ ω k x.2.2 - M.valueFixedPoint π x.2.2) ^ 2)) :=
          sum_le_sum fun ω _ ↦ mul_le_mul_of_nonneg_left
            (sum_tupleProb_mul_sq_linMartTerm_le M π μ _ hw k _) (pathWeight_nonneg M π μ ω)
      _ = K ^ 2 * ∑ ω : Fin k → Tuple State Action, pathWeight M π μ ω *
          ∑ x : Tuple State Action, tupleProb M π μ x *
            (2 * (tdIter M η₀ V₀ ω k x.1 - M.valueFixedPoint π x.1) ^ 2 +
              2 * (tdIter M η₀ V₀ ω k x.2.2 - M.valueFixedPoint π x.2.2) ^ 2) := by
          rw [mul_sum]; exact sum_congr rfl fun ω _ ↦ by ring
      _ ≤ K ^ 2 * (4 * Q) := mul_le_mul_of_nonneg_left
          (sum_pathWeight_mul_sum_tupleProb_sq_le M π μ η₀ V₀ k hQ) (sq_nonneg K)
      _ = 4 * K ^ 2 * Q := by ring
  obtain ⟨n, rfl⟩ : ∃ n, T = n + 1 := ⟨T - 1, by omega⟩
  rw [sum_range_succ']
  have h0term := hstep 0 (D ^ 2) fun s' ↦ tdSecondMoment_le_sq M π μ h0.le h1 V₀ 0 s'
  have hrest : ∑ k ∈ range n, ∑ ω : Fin (k + 1) → Tuple State Action, pathWeight M π μ ω *
        ∑ x, tupleProb M π μ x *
          linMartTerm M π μ η₀ (n + 1) s (k + 1) (tdIter M η₀ V₀ ω (k + 1)) x ^ 2 ≤
      ∑ k ∈ range n, 4 * K ^ 2 * (C * stepSize η₀ (k + 1)) := by
    refine sum_le_sum fun k _ ↦ ?_
    exact hstep (k + 1) (C * stepSize η₀ (k + 1)) fun s' ↦
      tdSecondMoment_le M π μ h0 h1 V₀ hμmin0 hμmin (Nat.le_add_left 1 k) s'
  have hsum := sum_range_stepSize_succ_le h0.le n
  have hC : 0 ≤ C := tdMomentConst_nonneg M π V₀ hμmin0
  have hcube : natCubeRoot n ≤ natCubeRoot (n + 1) := natCubeRoot_mono (Nat.le_succ n)
  have hr2 : ∑ k ∈ range n, 4 * K ^ 2 * (C * stepSize η₀ (k + 1)) =
      4 * K ^ 2 * C * ∑ k ∈ range n, stepSize η₀ (k + 1) := by
    rw [mul_sum]; exact sum_congr rfl fun k _ ↦ by ring
  have hKC : 0 ≤ 4 * K ^ 2 * C := by positivity
  have : 4 * K ^ 2 * C * ∑ k ∈ range n, stepSize η₀ (k + 1) ≤
      4 * K ^ 2 * (3 * C * η₀ * natCubeRoot (n + 1)) := by
    have := mul_le_mul_of_nonneg_left hsum hKC
    have := mul_le_mul_of_nonneg_left hcube (by positivity : (0 : ℝ) ≤ 4 * K ^ 2 * (3 * C * η₀))
    nlinarith
  nlinarith

/-! ## The remainder bound -/

/-- `K_E = K_β (D/η₀ + 2D + 2√(3Cη₀))`. -/
noncomputable def linRemainderConst (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (V₀ : State → ℝ) (μmin η₀ : ℝ) : ℝ :=
  linWeightConst M μmin η₀ * (tdPathBound M π V₀ / η₀ + 2 * tdPathBound M π V₀ +
    2 * Real.sqrt (3 * tdMomentConst M π V₀ μmin η₀ * η₀))

/-- The pointwise form of the remainder, coordinate `s`. -/
theorem scaledError_sub_linPart_apply [DecidableEq State] (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) (η₀ : ℝ) (V₀ : State → ℝ)
    {T : ℕ} (hT : 1 ≤ T) (ω : Fin T → Tuple State Action) (s : State) :
    scaledError M π η₀ V₀ ω s - linPart M π μ η₀ ω s = (Real.sqrt T)⁻¹ *
      (((∑ t ∈ range T, linKernel M π μ η₀ 0 (t + 1)) *ᵥ (V₀ - M.valueFixedPoint π)) s -
        ∑ k : Fin T, linMartTerm M π μ η₀ T s k (tdIter M η₀ V₀ ω k) (ω k)) := by
  have h := congrFun (scaledError_sub_linPart_eq M π μ η₀ V₀ hT ω) s
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_apply] at h
  rw [h]
  congr 2

/-- **B4: the linearisation remainder in `L²`.** For `0 < η₀ ≤ 1`, `0 < μmin ≤ μ(s)` for all
`s`, `T ≥ 1`, every `V₀` and every state `s`,
`‖(√TΔ̄_T − linPart)(s)‖_{L²} ≤ K_E T^{-1/3}` with the `T`-free `K_E = linRemainderConst`. -/
theorem weightedL2_scaledError_sub_linPart_le [DecidableEq State]
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (μ : FiniteDistribution State) {η₀ : ℝ} (h0 : 0 < η₀) (h1 : η₀ ≤ 1) (V₀ : State → ℝ)
    {μmin : ℝ} (hμmin0 : 0 < μmin) (hμmin : ∀ s, μmin ≤ μ.prob s) {T : ℕ} (hT : 1 ≤ T)
    (s : State) :
    weightedL2 (pathWeight M π μ) (fun ω : Fin T → Tuple State Action ↦
        scaledError M π η₀ V₀ ω s - linPart M π μ η₀ ω s) ≤
      linRemainderConst M π V₀ μmin η₀ * (T : ℝ) ^ (-(1 / 3 : ℝ)) := by
  have hw := pathWeight_nonneg M π μ (T := T)
  set K := linWeightConst M μmin η₀
  set D := tdPathBound M π V₀
  set C := tdMomentConst M π V₀ μmin η₀
  set u := natCubeRoot T
  set tr := ((∑ t ∈ range T, linKernel M π μ η₀ 0 (t + 1)) *ᵥ (V₀ - M.valueFixedPoint π)) s
  have hK0 : 0 ≤ K := linWeightConst_nonneg M hμmin0 h0
  have hD0 : 0 ≤ D := tdPathBound_nonneg M π V₀
  have hC0 : 0 ≤ C := tdMomentConst_nonneg M π V₀ hμmin0
  have hT0 : (0 : ℝ) < T := by exact_mod_cast hT
  have hsT : 0 < Real.sqrt T := Real.sqrt_pos.2 hT0
  have hu0 : 0 ≤ u := natCubeRoot_nonneg T
  rw [show (fun ω : Fin T → Tuple State Action ↦ scaledError M π η₀ V₀ ω s - linPart M π μ η₀ ω s)
      = fun ω ↦ (Real.sqrt T)⁻¹ * (tr -
        ∑ k : Fin T, linMartTerm M π μ η₀ T s k (tdIter M η₀ V₀ ω k) (ω k)) from
      funext fun ω ↦ scaledError_sub_linPart_apply M π μ η₀ V₀ hT ω s,
    weightedL2_const_mul, abs_of_nonneg (inv_nonneg.2 hsT.le)]
  -- the deterministic transient
  have htr : |tr| ≤ K * D / η₀ := by
    refine (abs_linTransient_le M π μ h0 h1 hμmin0 hμmin T _ s).trans ?_
    have : ‖V₀ - M.valueFixedPoint π‖ ≤ D := le_max_left _ _
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left this hK0) h0.le
  have hKD : 0 ≤ K * D / η₀ := by positivity
  have hsplit : (fun ω : Fin T → Tuple State Action ↦ tr -
      ∑ k : Fin T, linMartTerm M π μ η₀ T s k (tdIter M η₀ V₀ ω k) (ω k)) =
      (fun _ ↦ tr) + fun ω ↦ -∑ k : Fin T, linMartTerm M π μ η₀ T s k (tdIter M η₀ V₀ ω k) (ω k) := by
    funext ω; simp only [Pi.add_apply]; ring
  have hL2tr : weightedL2 (pathWeight M π μ) (fun _ : Fin T → Tuple State Action ↦ tr) ≤
      K * D / η₀ :=
    weightedL2_le_of_abs_le hw (sum_pathWeight M π μ T) hKD fun _ ↦ htr
  have hL2M : weightedL2 (pathWeight M π μ) (fun ω : Fin T → Tuple State Action ↦
      ∑ k : Fin T, linMartTerm M π μ η₀ T s k (tdIter M η₀ V₀ ω k) (ω k)) ≤
      2 * K * (D + Real.sqrt (3 * C * η₀) * Real.sqrt u) := by
    refine (weightedL2_le_sqrt (sum_pathWeight_mul_sq_linMart_le M π μ h0 h1 V₀ hμmin0 hμmin hT s)).trans ?_
    have hq : 0 ≤ 3 * C * η₀ := by positivity
    have hs1 := Real.sq_sqrt hq
    have hs2 := Real.sq_sqrt hu0
    have hs10 := Real.sqrt_nonneg (3 * C * η₀)
    have hs20 := Real.sqrt_nonneg u
    refine (Real.sqrt_le_sqrt ?_).trans_eq (Real.sqrt_sq (by positivity))
    have : 3 * C * η₀ * u = (Real.sqrt (3 * C * η₀) * Real.sqrt u) ^ 2 := by
      rw [mul_pow, hs1, hs2]
    nlinarith [mul_nonneg (mul_nonneg hD0 hs10) hs20, sq_nonneg K]
  have htot : weightedL2 (pathWeight M π μ) (fun ω : Fin T → Tuple State Action ↦ tr -
      ∑ k : Fin T, linMartTerm M π μ η₀ T s k (tdIter M η₀ V₀ ω k) (ω k)) ≤
      K * D / η₀ + 2 * K * (D + Real.sqrt (3 * C * η₀) * Real.sqrt u) := by
    rw [hsplit]
    refine (weightedL2_add_le hw _ _).trans (add_le_add hL2tr ?_)
    rw [weightedL2_neg]
    exact hL2M
  have hrate1 := inv_sqrt_le_rpow hT
  have hrate2 := inv_sqrt_mul_sqrt_natCubeRoot hT
  have hr0 : 0 ≤ (T : ℝ) ^ (-(1 / 3 : ℝ)) := Real.rpow_nonneg hT0.le _
  have hi0 : 0 ≤ (Real.sqrt T)⁻¹ := inv_nonneg.2 hsT.le
  calc (Real.sqrt T)⁻¹ * weightedL2 (pathWeight M π μ) _
      ≤ (Real.sqrt T)⁻¹ * (K * D / η₀ + 2 * K * (D + Real.sqrt (3 * C * η₀) * Real.sqrt u)) :=
        mul_le_mul_of_nonneg_left htot hi0
    _ = (Real.sqrt T)⁻¹ * (K * D / η₀ + 2 * K * D) +
          2 * K * Real.sqrt (3 * C * η₀) * ((Real.sqrt T)⁻¹ * Real.sqrt u) := by ring
    _ ≤ (T : ℝ) ^ (-(1 / 3 : ℝ)) * (K * D / η₀ + 2 * K * D) +
          2 * K * Real.sqrt (3 * C * η₀) * (T : ℝ) ^ (-(1 / 3 : ℝ)) := by
        rw [hrate2]
        have hX : 0 ≤ K * D / η₀ + 2 * K * D := by positivity
        linarith [mul_le_mul_of_nonneg_right hrate1 hX]
    _ = linRemainderConst M π V₀ μmin η₀ * (T : ℝ) ^ (-(1 / 3 : ℝ)) := by
        unfold linRemainderConst; ring

end StatisticalRL.Ch7Rest.TDInference
