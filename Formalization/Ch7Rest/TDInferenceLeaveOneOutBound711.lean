import Formalization.Ch7Rest.TDInferenceLeaveOneOut711
import Formalization.Ch7Rest.TDInferenceSmooth711

/-!
# Theorem 7.11 support (M8, H3): the leave-one-out `L²` bound and the Chen–Shao sum

Source: `chapters/inference.tex:52–64` (i.i.d. sampling), :72 (update), :82, :88 (`V̄_T`, `Δ̄_T`),
:104–117 (`A`), :134 (`η_t = η₀ t^{-2/3}`). Library infrastructure for the Chen–Shao step of the
half-space route of the corrected Theorem 7.11; no source result is claimed.

Write `η'_i = stepSize η₀ (i+1)` (the step that uses tuple `i`), `K_β = linWeightConst`,
`B = tdNoiseBound`, `D = tdPathBound`, `C = tdMomentConst`, `S = |State|`.

* `sum_pathWeight_sq_tdError_le`: `E Δ_i(s)² ≤ C' η'_i` for every `i ≤ T`, `C' = 2C + D²/η₀`
  (`looMomentConst`; `tdSecondMoment_le` plus `η_i ≤ 2η_{i+1}`).
* `abs_looDiff_succ_self_le`: pathwise `|δ_{i+1}(s)| ≤ c η'_i`, `c = 2B + 4D` (`looJumpConst`).
* `weightedL2_looRemainder_le` (**H3**): for `0 < η₀ ≤ 1`, `0 < μmin ≤ μ(s)`, every `V₀`, `i`, `x⋆`
  and `s`, `‖looRemainder_i(·)(s)‖_{L²} ≤ K_loo T^{-1/2} √η'_i` with the `i`-, `T`-, `x⋆`- and
  `s`-free `K_loo = √(16K_β²SC') + √(4K_β³c²)` (`looConst`). Proof: the exact cancellation
  `looRemainder_eq`; the first term is `O(√η'_i)` by `E‖Δ_i‖² ≲ η'_i`; the martingale sum over
  `k > i` is handled by orthogonality and the zero-noise decay `max_secondMoment_zeroNoise_le`
  (`E δ_k(s)² ≤ p_{i+1,k}(cη'_i)²`), so its square is `≤ 4K_β²c²η'_i² σ_i ≤ 4K_β³c²η'_i`.
* `sum_range_sqrt_stepSize_le`: `∑_{i<n} √η'_i ≤ (3/2)√η₀ n^{2/3}`.
* `sum_looChenShao_le`: the TD side of the Chen–Shao leave-one-out term,
  `∑_i E|uᵀlinSummand_i(ω i) · uᵀlooRemainder_i(ω)| ≤ ‖u‖₁² K_CS T^{-1/3}`, for any replacement
  tuples `x⋆_i`, with `K_CS = K_β B K_loo (3/2)√η₀` (`looChenShaoConst`).

No `Γ ≻ 0` hypothesis and no stationarity hypothesis is used.
-/

open Finset Matrix
open scoped BigOperators

namespace StatisticalRL.Ch7Rest.TDInference

open StatisticalRL.Probability StatisticalRL.Analysis

variable {State Action : Type} [Fintype State] [Fintype Action]

/-! ## Schedule facts -/

/-- `η_i ≤ 2 η_{i+1}` for `i ≥ 1`. -/
theorem stepSize_le_two_mul_succ {η₀ : ℝ} (h0 : 0 ≤ η₀) {i : ℕ} (hi : 1 ≤ i) :
    stepSize η₀ i ≤ 2 * stepSize η₀ (i + 1) := by
  have hx := natCubeRoot_pos hi
  have hy := natCubeRoot_pos (Nat.le_add_left 1 i)
  have hx3 : natCubeRoot i ^ 3 = i := natCubeRoot_cube i
  have hy3 : natCubeRoot (i + 1) ^ 3 = natCubeRoot i ^ 3 + 1 := by
    have := natCubeRoot_succ_cube_sub i; linarith
  have hi' : (1 : ℝ) ≤ natCubeRoot i ^ 3 := by rw [hx3]; exact_mod_cast hi
  have hy2 : natCubeRoot (i + 1) ^ 2 ≤ 2 * natCubeRoot i ^ 2 := by
    by_contra h
    push_neg at h
    have h3 := pow_lt_pow_left₀ h (by positivity) (by norm_num : (3 : ℕ) ≠ 0)
    have e1 : (natCubeRoot (i + 1) ^ 2) ^ 3 = (natCubeRoot i ^ 3 + 1) ^ 2 := by
      rw [← hy3]; ring
    have e2 : (2 * natCubeRoot i ^ 2) ^ 3 = 8 * (natCubeRoot i ^ 3) ^ 2 := by ring
    rw [e1, e2] at h3
    nlinarith
  rw [stepSize_eq, stepSize_eq, mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_left hy2 h0]

/-- `∑_{i<n} √η_{i+1} ≤ (3/2) √η₀ n^{2/3}` (from `u_{t+1}³ − u_t³ = 1`, `u_t = t^{1/3}`). -/
theorem sum_range_sqrt_stepSize_le (η₀ : ℝ) (n : ℕ) :
    ∑ t ∈ range n, Real.sqrt (stepSize η₀ (t + 1)) ≤ 3 / 2 * Real.sqrt η₀ * natCubeRoot n ^ 2 := by
  have hterm : ∀ t ∈ range n, Real.sqrt (stepSize η₀ (t + 1)) ≤
      3 / 2 * Real.sqrt η₀ * (natCubeRoot (t + 1) ^ 2 - natCubeRoot t ^ 2) := by
    intro t _
    have hy := natCubeRoot_pos (Nat.le_add_left 1 t)
    have hx := natCubeRoot_nonneg t
    have hxy := natCubeRoot_mono (Nat.le_succ t)
    have hc := natCubeRoot_succ_cube_sub t
    have hs0 := Real.sqrt_nonneg η₀
    have hsq : Real.sqrt (stepSize η₀ (t + 1)) = Real.sqrt η₀ / natCubeRoot (t + 1) := by
      rw [stepSize_eq, Real.sqrt_div' _ (by positivity), Real.sqrt_sq hy.le]
    have key : 1 ≤ 3 / 2 * (natCubeRoot (t + 1) ^ 2 - natCubeRoot t ^ 2) * natCubeRoot (t + 1) := by
      nlinarith [mul_nonneg (sq_nonneg (natCubeRoot (t + 1) - natCubeRoot t))
        (by linarith : (0 : ℝ) ≤ natCubeRoot (t + 1) + 2 * natCubeRoot t)]
    rw [hsq, div_le_iff₀ hy]
    nlinarith [mul_le_mul_of_nonneg_left key hs0]
  refine (sum_le_sum hterm).trans (le_of_eq ?_)
  rw [← mul_sum, sum_range_sub (fun t ↦ natCubeRoot t ^ 2)]
  simp [natCubeRoot]

/-! ## Constants -/

/-- `C' = 2C + D²/η₀`, so that `E Δ_i(s)² ≤ C' η'_i` for all `i ≥ 0`. -/
noncomputable def looMomentConst (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (V₀ : State → ℝ) (μmin η₀ : ℝ) : ℝ :=
  2 * tdMomentConst M π V₀ μmin η₀ + tdPathBound M π V₀ ^ 2 / η₀

/-- `c = 2B + 4D`, so that `|δ_{i+1}(s)| ≤ c η'_i` pathwise. -/
noncomputable def looJumpConst (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (V₀ : State → ℝ) : ℝ :=
  2 * tdNoiseBound M π + 4 * tdPathBound M π V₀

/-- `K_loo = √(16 K_β² S C') + √(4 K_β³ c²)`, free of `i`, `T`, `x⋆` and the coordinate. -/
noncomputable def looConst (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (V₀ : State → ℝ) (μmin η₀ : ℝ) : ℝ :=
  Real.sqrt (16 * linWeightConst M μmin η₀ ^ 2 * Fintype.card State *
      looMomentConst M π V₀ μmin η₀) +
    Real.sqrt (4 * linWeightConst M μmin η₀ ^ 3 * looJumpConst M π V₀ ^ 2)

/-- `K_CS = K_β B K_loo (3/2)√η₀`. -/
noncomputable def looChenShaoConst (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (V₀ : State → ℝ) (μmin η₀ : ℝ) : ℝ :=
  linWeightConst M μmin η₀ * tdNoiseBound M π * looConst M π V₀ μmin η₀ *
    (3 / 2 * Real.sqrt η₀)

theorem looConst_nonneg (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (V₀ : State → ℝ) (μmin η₀ : ℝ) : 0 ≤ looConst M π V₀ μmin η₀ :=
  add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

/-! ## Moments and pathwise bounds -/

/-- `E Δ_i(s)² ≤ C' η'_i` under the length-`T` path law, for every `i ≤ T`. -/
theorem sum_pathWeight_sq_tdError_le [DecidableEq State] (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) {η₀ : ℝ} (h0 : 0 < η₀)
    (h1 : η₀ ≤ 1) (V₀ : State → ℝ) {μmin : ℝ} (hμmin0 : 0 < μmin)
    (hμmin : ∀ s, μmin ≤ μ.prob s) {T i : ℕ} (hi : i ≤ T) (s : State) :
    ∑ ω : Fin T → Tuple State Action, pathWeight M π μ ω * tdError M π η₀ V₀ ω i s ^ 2 ≤
      looMomentConst M π V₀ μmin η₀ * stepSize η₀ (i + 1) := by
  have e := sum_pathWeight_mul_tdIter_of_le M π μ η₀ V₀
    (fun V ↦ (V s - M.valueFixedPoint π s) ^ 2) hi
  have e' : ∑ ω : Fin T → Tuple State Action, pathWeight M π μ ω * tdError M π η₀ V₀ ω i s ^ 2 =
      tdSecondMoment M π μ η₀ V₀ i s := by
    simpa only [tdError, Pi.sub_apply, tdSecondMoment] using e
  rw [e']
  have hC := tdMomentConst_nonneg M π V₀ (η₀ := η₀) hμmin0
  have hη := stepSize_pos h0 (Nat.le_add_left 1 i)
  have hDη : 0 ≤ tdPathBound M π V₀ ^ 2 / η₀ * stepSize η₀ (i + 1) := by positivity
  rcases Nat.eq_zero_or_pos i with rfl | hi1
  · have h1' : stepSize η₀ (0 + 1) = η₀ := by simp [stepSize]
    calc tdSecondMoment M π μ η₀ V₀ 0 s ≤ tdPathBound M π V₀ ^ 2 :=
          tdSecondMoment_le_sq M π μ h0.le h1 V₀ 0 s
      _ ≤ looMomentConst M π V₀ μmin η₀ * stepSize η₀ (0 + 1) := by
          rw [looMomentConst, add_mul, h1', div_mul_cancel₀ _ h0.ne']
          nlinarith
  · calc tdSecondMoment M π μ η₀ V₀ i s ≤ tdMomentConst M π V₀ μmin η₀ * stepSize η₀ i :=
          tdSecondMoment_le M π μ h0 h1 V₀ hμmin0 hμmin hi1 s
      _ ≤ tdMomentConst M π V₀ μmin η₀ * (2 * stepSize η₀ (i + 1)) :=
          mul_le_mul_of_nonneg_left (stepSize_le_two_mul_succ h0.le hi1) hC
      _ ≤ looMomentConst M π V₀ μmin η₀ * stepSize η₀ (i + 1) := by
          rw [looMomentConst, add_mul]
          nlinarith

theorem norm_sampleA_le [DecidableEq State] (M : DiscountedMDP State Action)
    (x : Tuple State Action) (v : State → ℝ) : ‖sampleA M x v‖ ≤ |v x.1| + |v x.2.2| := by
  have hγ0 := M.discount_nonneg
  have hγ1 := M.discount_lt_one.le
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun u ↦ ?_
  rw [Real.norm_eq_abs, sampleA_apply]
  split_ifs with h
  · rw [h, abs_le]
    constructor <;> nlinarith [abs_nonneg (v x.1), abs_nonneg (v x.2.2), neg_abs_le (v x.1),
      le_abs_self (v x.1), mul_le_mul_of_nonneg_left (le_abs_self (v x.2.2)) hγ0,
      mul_le_mul_of_nonneg_left (neg_abs_le (v x.2.2)) hγ0,
      mul_le_mul_of_nonneg_right hγ1 (abs_nonneg (v x.2.2))]
  · simp only [abs_zero]; positivity

/-- Pathwise jump at the replaced index: `|δ_{i+1}(s)| ≤ (2B + 4D) η'_i`. -/
theorem abs_looDiff_succ_self_le [DecidableEq State] (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) {η₀ : ℝ} (h0 : 0 ≤ η₀) (h1 : η₀ ≤ 1)
    (V₀ : State → ℝ) {T : ℕ} (i : Fin T) (xs : Tuple State Action)
    (ω : Fin T → Tuple State Action) (s : State) :
    |looDiff M η₀ V₀ i xs (i + 1) ω s| ≤ looJumpConst M π V₀ * stepSize η₀ (i + 1) := by
  set D := tdPathBound M π V₀
  set B := tdNoiseBound M π
  set Δ := tdError M π η₀ V₀ ω i with hΔdef
  have hΔ : ∀ u, |Δ u| ≤ D := fun u ↦ abs_tdIter_sub_le M π h0 h1 V₀ ω i u
  have hA : ∀ x : Tuple State Action, |sampleA M x Δ s| ≤ 2 * D := fun x ↦
    (abs_apply_le_norm _ s).trans ((norm_sampleA_le M x Δ).trans (by linarith [hΔ x.1, hΔ x.2.2]))
  have hN : ∀ x : Tuple State Action, |noiseVec M π x s| ≤ B := fun x ↦
    (abs_apply_le_norm _ s).trans (norm_noiseVec_le M π x)
  have hη := stepSize_nonneg h0 (i + 1)
  rw [looDiff_succ_self M π η₀ V₀ i xs ω, ← hΔdef]
  simp only [Pi.neg_apply, Pi.smul_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul, abs_neg,
    abs_mul, abs_of_nonneg hη]
  rw [mul_comm]
  refine mul_le_mul_of_nonneg_right ?_ hη
  have h1' := hA (ω i)
  have h2' := hA xs
  have h3' := hN (ω i)
  have h4' := hN xs
  calc |sampleA M (ω i) Δ s - sampleA M xs Δ s + (noiseVec M π (ω i) s - noiseVec M π xs s)|
      ≤ |sampleA M (ω i) Δ s| + |sampleA M xs Δ s| +
          (|noiseVec M π (ω i) s| + |noiseVec M π xs s|) :=
        (abs_add_le _ _).trans (add_le_add (abs_sub _ _) (abs_sub _ _))
    _ ≤ looJumpConst M π V₀ := by unfold looJumpConst; linarith

/-! ## The martingale part -/

/-- `∑ₓ p(x) (A_x − A)v = 0`. -/
theorem sum_tupleProb_mul_linMartVec [DecidableEq State] (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) (v : State → ℝ)
    (u : State) : ∑ x, tupleProb M π μ x * linMartVec M π μ x v u = 0 := by
  simp only [linMartVec, Pi.sub_apply, mul_sub, sum_sub_distrib, sum_tupleProb_mul_sampleA,
    ← sum_mul, sum_tupleProb, one_mul, sub_self]

/-- The `k`-th martingale increment of `looRemainder` at coordinate `s` (zero for `k ≤ i`). -/
noncomputable def looMartTerm [DecidableEq State] (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) (η₀ : ℝ)
    (V₀ : State → ℝ) {T : ℕ} (i : Fin T) (xs : Tuple State Action) (s : State) (k : Fin T)
    (ω : Fin T → Tuple State Action) : ℝ :=
  if i < k then
    ∑ u, linWeight M π μ η₀ T k s u * linMartVec M π μ (ω k) (looDiff M η₀ V₀ i xs k ω) u
  else 0

/-- The pointwise form of `looRemainder_eq`. -/
theorem looRemainder_apply [DecidableEq State] (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) (η₀ : ℝ)
    (V₀ : State → ℝ) {T : ℕ} (i : Fin T) (xs : Tuple State Action)
    (ω : Fin T → Tuple State Action) (s : State) :
    looRemainder M π μ η₀ V₀ i xs ω s = -((Real.sqrt T)⁻¹ *
      ((linWeight M π μ η₀ T i *ᵥ
          (sampleA M (ω i) (tdError M π η₀ V₀ ω i) - sampleA M xs (tdError M π η₀ V₀ ω i))) s +
        ∑ k : Fin T, looMartTerm M π μ η₀ V₀ i xs s k ω)) := by
  rw [looRemainder_eq]
  simp only [Pi.neg_apply, Pi.smul_apply, Pi.add_apply, smul_eq_mul, Finset.sum_apply]
  congr 3
  refine sum_congr rfl fun k _ ↦ ?_
  simp only [looMartTerm]
  split_ifs <;> simp [mulVec, dotProduct]

/-- `E(∑_k looMartTerm_k)² ≤ 4K_β³c²η'_i`. -/
theorem sum_pathWeight_sq_looMart_le [DecidableEq State] (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) {η₀ : ℝ} (h0 : 0 < η₀)
    (h1 : η₀ ≤ 1) (V₀ : State → ℝ) {μmin : ℝ} (hμmin0 : 0 < μmin)
    (hμmin : ∀ s, μmin ≤ μ.prob s) {T : ℕ} (i : Fin T) (xs : Tuple State Action) (s : State) :
    ∑ ω : Fin T → Tuple State Action, pathWeight M π μ ω *
        (∑ k : Fin T, looMartTerm M π μ η₀ V₀ i xs s k ω) ^ 2 ≤
      4 * linWeightConst M μmin η₀ ^ 3 * looJumpConst M π V₀ ^ 2 * stepSize η₀ (i + 1) := by
  set K := linWeightConst M μmin η₀
  set c := looJumpConst M π V₀
  set η := stepSize η₀ (i + 1)
  set a := linRate M μmin
  set e := linStepSeq η₀
  have hK0 : 0 ≤ K := linWeightConst_nonneg M hμmin0 h0
  have hη0 : 0 ≤ η := stepSize_nonneg h0.le _
  have hc0 : 0 ≤ c := by
    have := tdNoiseBound_pos M π; have := tdPathBound_nonneg M π V₀
    simp only [c, looJumpConst]; positivity
  have hae : ∀ j, a * e j ≤ 1 := fun j ↦ linRate_mul_stepSize_le M μ hμmin0 hμmin h0.le h1 j
  -- independence and centring
  have hind : ∀ j k : Fin T, j < k → ∀ ω x,
      looMartTerm M π μ η₀ V₀ i xs s j (Function.update ω k x) =
        looMartTerm M π μ η₀ V₀ i xs s j ω := by
    intro j k hjk ω x
    simp only [looMartTerm, Function.update_of_ne (ne_of_lt hjk),
      looDiff_update_of_le M η₀ V₀ i xs ω k x (Fin.le_def.1 hjk.le)]
  have hcent : ∀ k ω, ∑ x, tupleProb M π μ x *
      looMartTerm M π μ η₀ V₀ i xs s k (Function.update ω k x) = 0 := by
    intro k ω
    simp only [looMartTerm, Function.update_self, looDiff_update_of_le M η₀ V₀ i xs ω k _ le_rfl]
    split_ifs
    · simp_rw [mul_sum]
      rw [sum_comm]
      refine sum_eq_zero fun u _ ↦ ?_
      simp_rw [mul_left_comm (tupleProb M π μ _)]
      rw [← mul_sum, sum_tupleProb_mul_linMartVec, mul_zero]
    · simp
  rw [sum_pathWeight_mul_sq_sum_adapted M π μ _ hind hcent]
  -- zero-noise decay of `δ_k`
  have hQ0 : ∀ s', ∑ ω : Fin T → Tuple State Action, pathWeight M π μ ω *
      looDiff M η₀ V₀ i xs (i + 1) ω s' ^ 2 ≤ (c * η) ^ 2 :=
    fun s' ↦ sum_mul_sq_le_of_abs_le (pathWeight_nonneg M π μ) (sum_pathWeight M π μ T)
      fun ω ↦ abs_looDiff_succ_self_le M π h0.le h1 V₀ i xs ω s'
  have hdecay := max_secondMoment_zeroNoise_le M π μ h0.le h1 hμmin
    (fun t ω ↦ looDiff M η₀ V₀ i xs t ω) (i + 1)
    (fun t ht hmt ω ↦ looDiff_succ_of_lt M π η₀ V₀ i xs ω ht (by omega))
    (fun t ht _ ω x ↦ looDiff_update_of_le M η₀ V₀ i xs ω ⟨t, ht⟩ x le_rfl) hQ0
  -- per-increment bound
  have hk : ∀ k : Fin T, ∑ ω : Fin T → Tuple State Action, pathWeight M π μ ω *
      looMartTerm M π μ η₀ V₀ i xs s k ω ^ 2 ≤
      if i < k then 4 * K ^ 2 * (c * η) ^ 2 * contrProd a e (i + 1) k else 0 := by
    intro k
    split_ifs with hik
    · set Q := contrProd a e (i + 1) k * (c * η) ^ 2
      have hQ : ∀ s', ∑ ω : Fin T → Tuple State Action, pathWeight M π μ ω *
          looDiff M η₀ V₀ i xs k ω s' ^ 2 ≤ Q :=
        hdecay k (Fin.lt_def.1 hik) k.2.le
      have hw : ∀ u, |linWeight M π μ η₀ T k s u| ≤ K :=
        abs_apply_le_of_norm_mulVec_le _ hK0
          (norm_linWeight_mulVec_le M π μ h0 h1 hμmin0 hμmin T k) s
      rw [sum_pathWeight_mul_eq_sum_update M π μ k]
      simp only [looMartTerm, if_pos hik, Function.update_self,
        looDiff_update_of_le M η₀ V₀ i xs _ k _ le_rfl]
      have hpm : ∀ (ω : Fin T → Tuple State Action) (x : Tuple State Action) (u : State),
          linMartVec M π μ x (looDiff M η₀ V₀ i xs k ω) u =
            prMartingaleTerm M π μ u k (looDiff M η₀ V₀ i xs k ω + M.valueFixedPoint π) x := by
        intro ω x u
        simp [prMartingaleTerm, linMartVec]
      simp_rw [hpm]
      calc ∑ ω : Fin T → Tuple State Action, pathWeight M π μ ω * ∑ x, tupleProb M π μ x *
            (∑ u, linWeight M π μ η₀ T k s u * prMartingaleTerm M π μ u k
              (looDiff M η₀ V₀ i xs k ω + M.valueFixedPoint π) x) ^ 2
          ≤ ∑ ω : Fin T → Tuple State Action, pathWeight M π μ ω * (K ^ 2 *
              ∑ x : Tuple State Action, tupleProb M π μ x *
                (2 * looDiff M η₀ V₀ i xs k ω x.1 ^ 2 + 2 * looDiff M η₀ V₀ i xs k ω x.2.2 ^ 2)) := by
            refine sum_le_sum fun ω _ ↦ mul_le_mul_of_nonneg_left ?_ (pathWeight_nonneg M π μ ω)
            have := sum_tupleProb_mul_sq_linMartTerm_le M π μ _ hw k
              (looDiff M η₀ V₀ i xs k ω + M.valueFixedPoint π)
            simpa only [Pi.add_apply, add_sub_cancel_right] using this
        _ = K ^ 2 * ∑ x : Tuple State Action, tupleProb M π μ x *
              (2 * ∑ ω : Fin T → Tuple State Action, pathWeight M π μ ω *
                  looDiff M η₀ V₀ i xs k ω x.1 ^ 2 +
                2 * ∑ ω : Fin T → Tuple State Action, pathWeight M π μ ω *
                  looDiff M η₀ V₀ i xs k ω x.2.2 ^ 2) := by
            simp only [mul_sum, mul_add]
            rw [sum_comm]
            refine sum_congr rfl fun x _ ↦ ?_
            rw [← sum_add_distrib]
            exact sum_congr rfl fun ω _ ↦ by ring
        _ ≤ K ^ 2 * ∑ x : Tuple State Action, tupleProb M π μ x * (4 * Q) := by
            refine mul_le_mul_of_nonneg_left (sum_le_sum fun x _ ↦
              mul_le_mul_of_nonneg_left ?_ (tupleProb_nonneg M π μ x)) (sq_nonneg K)
            linarith [hQ x.1, hQ x.2.2]
        _ = 4 * K ^ 2 * (c * η) ^ 2 * contrProd a e (i + 1) k := by
            rw [← sum_mul, sum_tupleProb, one_mul]
            simp only [Q]; ring
    · simp only [looMartTerm, if_neg hik]; simp
  -- summing the geometric decay
  have hg : ∀ n, 0 ≤ 4 * K ^ 2 * (c * η) ^ 2 * contrProd a e (i + 1) n := fun n ↦
    mul_nonneg (by positivity) (contrProd_nonneg hae _ _)
  have hsum : ∑ k : Fin T, (if i < k then 4 * K ^ 2 * (c * η) ^ 2 * contrProd a e (i + 1) k
      else 0) ≤ ∑ t ∈ Ico (i : ℕ) T, 4 * K ^ 2 * (c * η) ^ 2 * contrProd a e (i + 1) (t + 1) := by
    set g : ℕ → ℝ := fun n ↦ 4 * K ^ 2 * (c * η) ^ 2 * contrProd a e (i + 1) n with hgdef
    calc ∑ k : Fin T, (if i < k then 4 * K ^ 2 * (c * η) ^ 2 * contrProd a e (i + 1) k else 0)
        = ∑ k : Fin T, (fun n : ℕ ↦ if (i : ℕ) < n then g n else 0) k :=
          sum_congr rfl fun k _ ↦ by simp only [Fin.lt_def, hgdef]
      _ = ∑ k ∈ range T, (if (i : ℕ) < k then g k else 0) :=
          Fin.sum_univ_eq_sum_range (fun n : ℕ ↦ if (i : ℕ) < n then g n else 0) T
      _ = ∑ k ∈ (range T).filter (fun k ↦ (i : ℕ) < k), g k := (sum_filter _ _).symm
      _ ≤ ∑ k ∈ Ico ((i : ℕ) + 1) (T + 1), g k :=
          sum_le_sum_of_subset_of_nonneg (by intro k hk; simp at hk ⊢; omega)
            (fun k _ _ ↦ hg k)
      _ = ∑ t ∈ Ico (i : ℕ) T, g (t + 1) := (sum_Ico_add' g (i : ℕ) T 1).symm
  have hσ : e i * contrSum a e T i ≤ K := linStepSeq_mul_contrSum_le M μ hμmin0 hμmin h0 h1 T i
  have hσ0 : 0 ≤ contrSum a e T i := contrSum_nonneg hae T i
  calc ∑ k : Fin T, ∑ ω : Fin T → Tuple State Action, pathWeight M π μ ω *
        looMartTerm M π μ η₀ V₀ i xs s k ω ^ 2
      ≤ ∑ k : Fin T, (if i < k then 4 * K ^ 2 * (c * η) ^ 2 * contrProd a e (i + 1) k else 0) :=
        sum_le_sum fun k _ ↦ hk k
    _ ≤ ∑ t ∈ Ico (i : ℕ) T, 4 * K ^ 2 * (c * η) ^ 2 * contrProd a e (i + 1) (t + 1) := hsum
    _ = 4 * K ^ 2 * c ^ 2 * η * (e i * contrSum a e T i) := by
        rw [← mul_sum, contrSum]
        simp only [e, linStepSeq, η]
        ring
    _ ≤ 4 * K ^ 2 * c ^ 2 * η * K := mul_le_mul_of_nonneg_left hσ (by positivity)
    _ = 4 * K ^ 3 * c ^ 2 * η := by ring

/-! ## The leave-one-out `L²` bound (H3) -/

/-- `E(linWeight_i (A_{ω i} − A_{x⋆})Δ_i)(s)² ≤ 16K_β² S C' η'_i`. -/
theorem sum_pathWeight_sq_looFirst_le [DecidableEq State] (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) {η₀ : ℝ} (h0 : 0 < η₀)
    (h1 : η₀ ≤ 1) (V₀ : State → ℝ) {μmin : ℝ} (hμmin0 : 0 < μmin)
    (hμmin : ∀ s, μmin ≤ μ.prob s) {T : ℕ} (i : Fin T) (xs : Tuple State Action) (s : State) :
    ∑ ω : Fin T → Tuple State Action, pathWeight M π μ ω *
        ((linWeight M π μ η₀ T i *ᵥ
          (sampleA M (ω i) (tdError M π η₀ V₀ ω i) - sampleA M xs (tdError M π η₀ V₀ ω i))) s) ^ 2 ≤
      16 * linWeightConst M μmin η₀ ^ 2 * Fintype.card State * looMomentConst M π V₀ μmin η₀ *
        stepSize η₀ (i + 1) := by
  set K := linWeightConst M μmin η₀
  have hK0 : 0 ≤ K := linWeightConst_nonneg M hμmin0 h0
  have hpt : ∀ ω : Fin T → Tuple State Action,
      ((linWeight M π μ η₀ T i *ᵥ
        (sampleA M (ω i) (tdError M π η₀ V₀ ω i) - sampleA M xs (tdError M π η₀ V₀ ω i))) s) ^ 2 ≤
      16 * K ^ 2 * ∑ u, tdError M π η₀ V₀ ω i u ^ 2 := by
    intro ω
    set Δ := tdError M π η₀ V₀ ω i
    set P := |Δ (ω i).1| + |Δ (ω i).2.2| + |Δ xs.1| + |Δ xs.2.2| with hP
    have hP0 : 0 ≤ P := by positivity
    have habs : |(linWeight M π μ η₀ T i *ᵥ
        (sampleA M (ω i) Δ - sampleA M xs Δ)) s| ≤ K * P := by
      refine (abs_apply_le_norm _ s).trans ((norm_linWeight_mulVec_le M π μ h0 h1 hμmin0 hμmin
        T i _).trans (mul_le_mul_of_nonneg_left ?_ hK0))
      refine (norm_sub_le _ _).trans ?_
      have := norm_sampleA_le M (ω i) Δ
      have := norm_sampleA_le M xs Δ
      linarith
    have hsq : P ^ 2 ≤ 4 * (Δ (ω i).1 ^ 2 + Δ (ω i).2.2 ^ 2 + Δ xs.1 ^ 2 + Δ xs.2.2 ^ 2) := by
      simp only [hP]
      rw [← sq_abs (Δ (ω i).1), ← sq_abs (Δ (ω i).2.2), ← sq_abs (Δ xs.1), ← sq_abs (Δ xs.2.2)]
      nlinarith [sq_nonneg (|Δ (ω i).1| - |Δ (ω i).2.2|), sq_nonneg (|Δ (ω i).1| - |Δ xs.1|),
        sq_nonneg (|Δ (ω i).1| - |Δ xs.2.2|), sq_nonneg (|Δ (ω i).2.2| - |Δ xs.1|),
        sq_nonneg (|Δ (ω i).2.2| - |Δ xs.2.2|), sq_nonneg (|Δ xs.1| - |Δ xs.2.2|)]
    have hS : ∀ a : State, Δ a ^ 2 ≤ ∑ u, Δ u ^ 2 := fun a ↦
      single_le_sum (f := fun u ↦ Δ u ^ 2) (fun _ _ ↦ sq_nonneg _) (mem_univ a)
    calc ((linWeight M π μ η₀ T i *ᵥ (sampleA M (ω i) Δ - sampleA M xs Δ)) s) ^ 2
        ≤ (K * P) ^ 2 := by
          rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) habs 2
      _ = K ^ 2 * P ^ 2 := by ring
      _ ≤ K ^ 2 * (4 * (4 * ∑ u, Δ u ^ 2)) := by
          refine mul_le_mul_of_nonneg_left (hsq.trans ?_) (sq_nonneg K)
          linarith [hS (ω i).1, hS (ω i).2.2, hS xs.1, hS xs.2.2]
      _ = 16 * K ^ 2 * ∑ u, Δ u ^ 2 := by ring
  calc ∑ ω : Fin T → Tuple State Action, pathWeight M π μ ω *
        ((linWeight M π μ η₀ T i *ᵥ
          (sampleA M (ω i) (tdError M π η₀ V₀ ω i) - sampleA M xs (tdError M π η₀ V₀ ω i))) s) ^ 2
      ≤ ∑ ω : Fin T → Tuple State Action, pathWeight M π μ ω *
          (16 * K ^ 2 * ∑ u, tdError M π η₀ V₀ ω i u ^ 2) :=
        sum_le_sum fun ω _ ↦ mul_le_mul_of_nonneg_left (hpt ω) (pathWeight_nonneg M π μ ω)
    _ = 16 * K ^ 2 * ∑ u, ∑ ω : Fin T → Tuple State Action, pathWeight M π μ ω *
          tdError M π η₀ V₀ ω i u ^ 2 := by
        simp only [mul_sum]
        rw [sum_comm]
        exact sum_congr rfl fun u _ ↦ sum_congr rfl fun ω _ ↦ by ring
    _ ≤ 16 * K ^ 2 * ∑ _u : State, looMomentConst M π V₀ μmin η₀ * stepSize η₀ (i + 1) :=
        mul_le_mul_of_nonneg_left (sum_le_sum fun u _ ↦
          sum_pathWeight_sq_tdError_le M π μ h0 h1 V₀ hμmin0 hμmin i.2.le u) (by positivity)
    _ = _ := by
        rw [sum_const, card_univ, nsmul_eq_mul]
        ring

/-- **H3: leave-one-out stability of the TD remainder.** For `0 < η₀ ≤ 1`, `0 < μmin ≤ μ(s)`
for all `s`, every `V₀`, every sample index `i : Fin T`, every replacement tuple `x⋆` and every
state `s`,
`‖(E_T(ω) − E_T(ω[i ↦ x⋆]))(s)‖_{L²} ≤ K_loo T^{-1/2} √η'_i`, where
`E_T = √TΔ̄_T − linPart`, `η'_i = stepSize η₀ (i+1)` and `K_loo = looConst` is free of `i`, `T`,
`x⋆` and `s`. -/
theorem weightedL2_looRemainder_le [DecidableEq State] (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) {η₀ : ℝ} (h0 : 0 < η₀)
    (h1 : η₀ ≤ 1) (V₀ : State → ℝ) {μmin : ℝ} (hμmin0 : 0 < μmin)
    (hμmin : ∀ s, μmin ≤ μ.prob s) {T : ℕ} (i : Fin T) (xs : Tuple State Action) (s : State) :
    weightedL2 (pathWeight M π μ)
        (fun ω : Fin T → Tuple State Action ↦ looRemainder M π μ η₀ V₀ i xs ω s) ≤
      looConst M π V₀ μmin η₀ * ((Real.sqrt T)⁻¹ * Real.sqrt (stepSize η₀ (i + 1))) := by
  have hw := pathWeight_nonneg M π μ (T := T)
  set η := stepSize η₀ (i + 1)
  have hη0 : 0 ≤ η := stepSize_nonneg h0.le _
  set A : (Fin T → Tuple State Action) → ℝ := fun ω ↦ (linWeight M π μ η₀ T i *ᵥ
    (sampleA M (ω i) (tdError M π η₀ V₀ ω i) - sampleA M xs (tdError M π η₀ V₀ ω i))) s with hA
  set Bm : (Fin T → Tuple State Action) → ℝ := fun ω ↦
    ∑ k : Fin T, looMartTerm M π μ η₀ V₀ i xs s k ω with hBm
  have hrw : (fun ω : Fin T → Tuple State Action ↦ looRemainder M π μ η₀ V₀ i xs ω s) =
      fun ω ↦ -((Real.sqrt T)⁻¹ * (A + Bm) ω) := by
    funext ω
    rw [looRemainder_apply]
    rfl
  have hsT : 0 ≤ (Real.sqrt T)⁻¹ := inv_nonneg.2 (Real.sqrt_nonneg _)
  rw [hrw, weightedL2_neg, weightedL2_const_mul, abs_of_nonneg hsT]
  have hLA : weightedL2 (pathWeight M π μ) A ≤
      Real.sqrt (16 * linWeightConst M μmin η₀ ^ 2 * Fintype.card State *
        looMomentConst M π V₀ μmin η₀) * Real.sqrt η := by
    rw [← Real.sqrt_mul' _ hη0]
    exact weightedL2_le_sqrt (sum_pathWeight_sq_looFirst_le M π μ h0 h1 V₀ hμmin0 hμmin i xs s)
  have hLB : weightedL2 (pathWeight M π μ) Bm ≤
      Real.sqrt (4 * linWeightConst M μmin η₀ ^ 3 * looJumpConst M π V₀ ^ 2) * Real.sqrt η := by
    rw [← Real.sqrt_mul' _ hη0]
    exact weightedL2_le_sqrt (sum_pathWeight_sq_looMart_le M π μ h0 h1 V₀ hμmin0 hμmin i xs s)
  calc (Real.sqrt T)⁻¹ * weightedL2 (pathWeight M π μ) (A + Bm)
      ≤ (Real.sqrt T)⁻¹ * (weightedL2 (pathWeight M π μ) A + weightedL2 (pathWeight M π μ) Bm) :=
        mul_le_mul_of_nonneg_left (weightedL2_add_le hw A Bm) hsT
    _ ≤ (Real.sqrt T)⁻¹ * (looConst M π V₀ μmin η₀ * Real.sqrt η) := by
        refine mul_le_mul_of_nonneg_left ?_ hsT
        rw [looConst, add_mul]
        exact add_le_add hLA hLB
    _ = looConst M π V₀ μmin η₀ * ((Real.sqrt T)⁻¹ * Real.sqrt η) := by ring

/-- **H3, projected.** `‖uᵀ(E_T(ω) − E_T(ω[i ↦ x⋆]))‖_{L²} ≤ ‖u‖₁ K_loo T^{-1/2} √η'_i`. -/
theorem weightedL2_proj_looRemainder_le [DecidableEq State] (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) {η₀ : ℝ} (h0 : 0 < η₀)
    (h1 : η₀ ≤ 1) (V₀ : State → ℝ) {μmin : ℝ} (hμmin0 : 0 < μmin)
    (hμmin : ∀ s, μmin ≤ μ.prob s) {T : ℕ} (i : Fin T) (xs : Tuple State Action)
    (u : State → ℝ) :
    weightedL2 (pathWeight M π μ)
        (fun ω : Fin T → Tuple State Action ↦ ∑ s, u s * looRemainder M π μ η₀ V₀ i xs ω s) ≤
      (∑ s, |u s|) *
        (looConst M π V₀ μmin η₀ * ((Real.sqrt T)⁻¹ * Real.sqrt (stepSize η₀ (i + 1)))) := by
  have hw := pathWeight_nonneg M π μ (T := T)
  refine (weightedL2_sum_le hw univ
    (fun s ω ↦ u s * looRemainder M π μ η₀ V₀ i xs ω s)).trans ?_
  rw [sum_mul]
  refine sum_le_sum fun s _ ↦ ?_
  rw [weightedL2_const_mul]
  exact mul_le_mul_of_nonneg_left
    (weightedL2_looRemainder_le M π μ h0 h1 V₀ hμmin0 hμmin i xs s) (abs_nonneg _)

/-! ## The Chen–Shao leave-one-out sum -/

/-- `|uᵀ linSummand_k(x)| ≤ ‖u‖₁ T^{-1/2} K_β B` (CHECK-plan F7: through `‖u‖₁`). -/
theorem abs_proj_linSummand_le [DecidableEq State] (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) {η₀ : ℝ} (h0 : 0 < η₀)
    (h1 : η₀ ≤ 1) {μmin : ℝ} (hμmin0 : 0 < μmin) (hμmin : ∀ s, μmin ≤ μ.prob s) (T k : ℕ)
    (x : Tuple State Action) (u : State → ℝ) :
    |∑ s, u s * linSummand M π μ η₀ T k x s| ≤
      (∑ s, |u s|) * ((Real.sqrt T)⁻¹ * (linWeightConst M μmin η₀ * tdNoiseBound M π)) := by
  have hsT : 0 ≤ (Real.sqrt T)⁻¹ := inv_nonneg.2 (Real.sqrt_nonneg _)
  have hK0 := linWeightConst_nonneg M hμmin0 h0
  have hpt : ∀ s, |linSummand M π μ η₀ T k x s| ≤
      (Real.sqrt T)⁻¹ * (linWeightConst M μmin η₀ * tdNoiseBound M π) := by
    intro s
    simp only [linSummand, Pi.neg_apply, Pi.smul_apply, smul_eq_mul, abs_neg, abs_mul,
      abs_of_nonneg hsT]
    refine mul_le_mul_of_nonneg_left ((abs_apply_le_norm _ s).trans ?_) hsT
    exact (norm_linWeight_mulVec_le M π μ h0 h1 hμmin0 hμmin T k _).trans
      (mul_le_mul_of_nonneg_left (norm_noiseVec_le M π x) hK0)
  refine (abs_sum_le_sum_abs _ _).trans ?_
  rw [sum_mul]
  refine sum_le_sum fun s _ ↦ ?_
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (hpt s) (abs_nonneg _)

/-- `E|b| ≤ ‖b‖_{L²}` on the path law. -/
theorem sum_pathWeight_mul_abs_le_weightedL2 (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) {T : ℕ}
    (b : (Fin T → Tuple State Action) → ℝ) :
    ∑ ω, pathWeight M π μ ω * |b ω| ≤ weightedL2 (pathWeight M π μ) b := by
  have h := sum_mul_mul_le_weightedL2 (pathWeight_nonneg M π μ) (fun _ ↦ (1 : ℝ))
    (fun ω ↦ |b ω|)
  have h1 : weightedL2 (pathWeight M π μ) (fun _ : Fin T → Tuple State Action ↦ (1 : ℝ)) = 1 := by
    simp [weightedL2, sum_pathWeight]
  rw [h1, one_mul, weightedL2_abs] at h
  simpa only [one_mul] using h

/-- **The TD side of the Chen–Shao leave-one-out term.** For `0 < η₀ ≤ 1`, `0 < μmin ≤ μ(s)`,
`T ≥ 1`, every `V₀`, every direction `u` and every family of replacement tuples `x⋆_i`,
`∑_i E|uᵀlinSummand_i(ω i) · uᵀ(E_T(ω) − E_T(ω[i ↦ x⋆_i]))| ≤ ‖u‖₁² K_CS T^{-1/3}`
with the `T`-free `K_CS = looChenShaoConst`. -/
theorem sum_looChenShao_le [DecidableEq State] (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) {η₀ : ℝ} (h0 : 0 < η₀)
    (h1 : η₀ ≤ 1) (V₀ : State → ℝ) {μmin : ℝ} (hμmin0 : 0 < μmin)
    (hμmin : ∀ s, μmin ≤ μ.prob s) {T : ℕ} (hT : 1 ≤ T) (u : State → ℝ)
    (xs : Fin T → Tuple State Action) :
    ∑ i : Fin T, ∑ ω : Fin T → Tuple State Action, pathWeight M π μ ω *
        |(∑ s, u s * linSummand M π μ η₀ T i (ω i) s) *
          (∑ s, u s * looRemainder M π μ η₀ V₀ i (xs i) ω s)| ≤
      (∑ s, |u s|) ^ 2 * looChenShaoConst M π V₀ μmin η₀ * (T : ℝ) ^ (-(1 / 3 : ℝ)) := by
  set U := ∑ s, |u s|
  set K := linWeightConst M μmin η₀
  set B := tdNoiseBound M π
  set L := looConst M π V₀ μmin η₀
  have hU : 0 ≤ U := sum_nonneg fun s _ ↦ abs_nonneg _
  have hK0 : 0 ≤ K := linWeightConst_nonneg M hμmin0 h0
  have hB0 : 0 < B := tdNoiseBound_pos M π
  have hL0 : 0 ≤ L := looConst_nonneg M π V₀ μmin η₀
  have hT0 : (0 : ℝ) < T := by exact_mod_cast hT
  have hsT : 0 ≤ (Real.sqrt T)⁻¹ := inv_nonneg.2 (Real.sqrt_nonneg _)
  have hsTT : (Real.sqrt T)⁻¹ * (Real.sqrt T)⁻¹ = (T : ℝ)⁻¹ := by
    rw [← mul_inv, Real.mul_self_sqrt hT0.le]
  have hi : ∀ i : Fin T, ∑ ω : Fin T → Tuple State Action, pathWeight M π μ ω *
      |(∑ s, u s * linSummand M π μ η₀ T i (ω i) s) *
        (∑ s, u s * looRemainder M π μ η₀ V₀ i (xs i) ω s)| ≤
      U ^ 2 * (K * B * L) * ((T : ℝ)⁻¹ * Real.sqrt (stepSize η₀ (i + 1))) := by
    intro i
    set Ma := U * ((Real.sqrt T)⁻¹ * (K * B))
    have hMa : 0 ≤ Ma := by positivity
    calc ∑ ω : Fin T → Tuple State Action, pathWeight M π μ ω *
          |(∑ s, u s * linSummand M π μ η₀ T i (ω i) s) *
            (∑ s, u s * looRemainder M π μ η₀ V₀ i (xs i) ω s)|
        ≤ ∑ ω : Fin T → Tuple State Action, pathWeight M π μ ω *
            (Ma * |∑ s, u s * looRemainder M π μ η₀ V₀ i (xs i) ω s|) := by
          refine sum_le_sum fun ω _ ↦ mul_le_mul_of_nonneg_left ?_ (pathWeight_nonneg M π μ ω)
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_right
            (abs_proj_linSummand_le M π μ h0 h1 hμmin0 hμmin T i (ω i) u) (abs_nonneg _)
      _ = Ma * ∑ ω : Fin T → Tuple State Action, pathWeight M π μ ω *
            |∑ s, u s * looRemainder M π μ η₀ V₀ i (xs i) ω s| := by
          rw [mul_sum]; exact sum_congr rfl fun ω _ ↦ by ring
      _ ≤ Ma * (U * (L * ((Real.sqrt T)⁻¹ * Real.sqrt (stepSize η₀ (i + 1))))) :=
          mul_le_mul_of_nonneg_left ((sum_pathWeight_mul_abs_le_weightedL2 M π μ _).trans
            (weightedL2_proj_looRemainder_le M π μ h0 h1 V₀ hμmin0 hμmin i (xs i) u)) hMa
      _ = U ^ 2 * (K * B * L) * (((Real.sqrt T)⁻¹ * (Real.sqrt T)⁻¹) *
            Real.sqrt (stepSize η₀ (i + 1))) := by ring
      _ = U ^ 2 * (K * B * L) * ((T : ℝ)⁻¹ * Real.sqrt (stepSize η₀ (i + 1))) := by rw [hsTT]
  have hC : 0 ≤ U ^ 2 * (K * B * L) * (T : ℝ)⁻¹ := by positivity
  calc ∑ i : Fin T, ∑ ω : Fin T → Tuple State Action, pathWeight M π μ ω *
        |(∑ s, u s * linSummand M π μ η₀ T i (ω i) s) *
          (∑ s, u s * looRemainder M π μ η₀ V₀ i (xs i) ω s)|
      ≤ ∑ i : Fin T, U ^ 2 * (K * B * L) * ((T : ℝ)⁻¹ * Real.sqrt (stepSize η₀ (i + 1))) :=
        sum_le_sum fun i _ ↦ hi i
    _ = U ^ 2 * (K * B * L) * (T : ℝ)⁻¹ *
          ∑ i ∈ range T, Real.sqrt (stepSize η₀ (i + 1)) := by
        rw [← Fin.sum_univ_eq_sum_range (fun i ↦ Real.sqrt (stepSize η₀ (i + 1))), mul_sum]
        exact sum_congr rfl fun i _ ↦ by ring
    _ ≤ U ^ 2 * (K * B * L) * (T : ℝ)⁻¹ * (3 / 2 * Real.sqrt η₀ * natCubeRoot T ^ 2) :=
        mul_le_mul_of_nonneg_left (sum_range_sqrt_stepSize_le η₀ T) hC
    _ = U ^ 2 * (K * B * L * (3 / 2 * Real.sqrt η₀)) * (natCubeRoot T ^ 2 / T) := by ring
    _ = U ^ 2 * looChenShaoConst M π V₀ μmin η₀ * (T : ℝ) ^ (-(1 / 3 : ℝ)) := by
        rw [natCubeRoot_sq_div hT]
        simp only [looChenShaoConst, K, B, L]

/-! ## The projected remainder (for the `E|WΔ|` term) -/

/-- **B4, projected.** `‖uᵀ(√TΔ̄_T − linPart)‖_{L²} ≤ ‖u‖₁ K_E T^{-1/3}` (from the per-coordinate
`weightedL2_scaledError_sub_linPart_le` by Minkowski). With `Δ := uᵀ(√TΔ̄_T − linPart)/σ`
(transient included) the Chen–Shao term `E|WΔ| ≤ ‖Δ‖_{L²}` is `O(T^{-1/3})`, and
`Δ(ω) − Δ(ω[i ↦ x⋆]) = uᵀlooRemainder_i/σ`. -/
theorem weightedL2_proj_scaledError_sub_linPart_le [DecidableEq State]
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (μ : FiniteDistribution State) {η₀ : ℝ} (h0 : 0 < η₀) (h1 : η₀ ≤ 1) (V₀ : State → ℝ)
    {μmin : ℝ} (hμmin0 : 0 < μmin) (hμmin : ∀ s, μmin ≤ μ.prob s) {T : ℕ} (hT : 1 ≤ T)
    (u : State → ℝ) :
    weightedL2 (pathWeight M π μ) (fun ω : Fin T → Tuple State Action ↦
        ∑ s, u s * (scaledError M π η₀ V₀ ω s - linPart M π μ η₀ ω s)) ≤
      (∑ s, |u s|) * (linRemainderConst M π V₀ μmin η₀ * (T : ℝ) ^ (-(1 / 3 : ℝ))) := by
  have hw := pathWeight_nonneg M π μ (T := T)
  refine (weightedL2_sum_le hw univ
    (fun s ω ↦ u s * (scaledError M π η₀ V₀ ω s - linPart M π μ η₀ ω s))).trans ?_
  rw [sum_mul]
  refine sum_le_sum fun s _ ↦ ?_
  rw [weightedL2_const_mul]
  exact mul_le_mul_of_nonneg_left
    (weightedL2_scaledError_sub_linPart_le M π μ h0 h1 V₀ hμmin0 hμmin hT s) (abs_nonneg _)

end StatisticalRL.Ch7Rest.TDInference
