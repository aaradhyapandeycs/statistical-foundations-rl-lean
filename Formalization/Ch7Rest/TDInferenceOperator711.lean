import Formalization.Ch7Rest.TDInferenceNoise711

/-!
# Theorem 7.11 support (M3): the mean operator `A = diag(μ)(I − γP_π)` and the sample operators

Source: `inference.tex:99–117` (`A = diag(μ)(I − γP_π)`), update :72.

* `tdA_mulVec_apply`: `(A v)(s) = μ(s)(v(s) − γ (P_π v)(s))`.
* `sampleA x v = (v(s) − γ v(s')) e_s` and `noiseVec x = ξ(x) e_s` for `x = (s,a,s')`:
  `tdStep_sub_value_eq`: `V' − V^π = Δ − η (A_x Δ + ξ_x)` exactly;
  `sum_tupleProb_mul_sampleA`: `E_x A_x v = A v`; `sum_tupleProb_mul_noiseVec`: `E_x ξ_x = 0`.
* `mul_norm_le_norm_tdA_mulVec`: `(1−γ) μmin ‖v‖_∞ ≤ ‖A v‖_∞` (strict diagonal dominance), hence
  `tdA_isUnit` and `norm_tdA_inv_mulVec_le`: `‖A⁻¹ y‖_∞ ≤ ‖y‖_∞ / ((1−γ) μmin)`.
-/

open Finset Matrix
open scoped BigOperators

namespace StatisticalRL.Ch7Rest.TDInference

variable {State Action : Type} [Fintype State] [Fintype Action]

theorem tdA_mulVec_apply [DecidableEq State] (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) (v : State → ℝ)
    (s : State) :
    (tdA M π μ *ᵥ v) s =
      μ.prob s * (v s - M.discount * (M.policyTransition π s).expectation v) := by
  rw [tdA, ← Matrix.mulVec_mulVec, Matrix.mulVec_diagonal, Matrix.sub_mulVec, Matrix.one_mulVec]
  simp only [Pi.sub_apply, Matrix.mulVec, dotProduct, policyMatrix, Matrix.smul_apply,
    Matrix.of_apply, smul_eq_mul, FiniteDistribution.expectation]
  congr 2
  rw [mul_sum]
  exact sum_congr rfl fun x _ ↦ by ring

/-- The sample operator `A_x v = (v(s) − γ v(s')) e_s` of the tuple `x = (s, a, s')`. -/
noncomputable def sampleA [DecidableEq State] (M : DiscountedMDP State Action)
    (x : Tuple State Action) (v : State → ℝ) : State → ℝ :=
  Pi.single x.1 (v x.1 - M.discount * v x.2.2)

/-- The noise vector `ξ_x = ξ(x) e_s` of the tuple `x = (s, a, s')`. -/
noncomputable def noiseVec [DecidableEq State] (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (x : Tuple State Action) : State → ℝ :=
  Pi.single x.1 (tdNoise M π x)

theorem sampleA_apply [DecidableEq State] (M : DiscountedMDP State Action)
    (x : Tuple State Action) (v : State → ℝ) (s : State) :
    sampleA M x v s = if s = x.1 then v s - M.discount * v x.2.2 else 0 := by
  unfold sampleA
  rw [Pi.single_apply]
  split_ifs with h
  · subst h; rfl
  · rfl

theorem noiseVec_apply [DecidableEq State] (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (x : Tuple State Action) (s : State) :
    noiseVec M π x s = if s = x.1 then tdNoise M π (s, x.2.1, x.2.2) else 0 := by
  unfold noiseVec
  rw [Pi.single_apply]
  split_ifs with h
  · subst h; rfl
  · rfl

/-- The exact error recursion `V' − V^π = Δ − η(A_x Δ + ξ_x)`. -/
theorem tdStep_sub_value_eq [DecidableEq State] (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (η : ℝ) (V : State → ℝ) (x : Tuple State Action) :
    tdStep M η V x - M.valueFixedPoint π =
      (V - M.valueFixedPoint π) -
        η • (sampleA M x (V - M.valueFixedPoint π) + noiseVec M π x) := by
  funext s
  rw [Pi.sub_apply, tdStep_sub_value_apply M π]
  simp only [Pi.sub_apply, Pi.smul_apply, Pi.add_apply, sampleA_apply, noiseVec_apply,
    smul_eq_mul]
  split_ifs with h
  · subst h; ring
  · ring

/-- `E_x A_x v = A v`. -/
theorem sum_tupleProb_mul_sampleA [DecidableEq State] (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) (v : State → ℝ)
    (s : State) :
    ∑ x, tupleProb M π μ x * sampleA M x v s = (tdA M π μ *ᵥ v) s := by
  simp_rw [sampleA_apply]
  rw [sum_tupleProb_mul_ite_zero M π μ s (fun _ s' ↦ v s - M.discount * v s'),
    tdA_mulVec_apply]
  congr 1
  have h := tupleCondExp_affine M π s (v s) (-M.discount) 0 v (fun _ _ ↦ 0)
  simp only [zero_mul, add_zero] at h
  rw [show (fun (_ : Action) (s' : State) ↦ v s - M.discount * v s') =
    fun _ s' ↦ v s + -M.discount * v s' by funext a s'; ring, h]
  ring

/-- `E_x ξ_x = 0` (Bellman). -/
theorem sum_tupleProb_mul_noiseVec [DecidableEq State] (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) (s : State) :
    ∑ x, tupleProb M π μ x * noiseVec M π x s = 0 := by
  simp_rw [noiseVec_apply]
  rw [sum_tupleProb_mul_ite_zero M π μ s (fun a s' ↦ tdNoise M π (s, a, s')),
    tupleCondExp_tdNoise, mul_zero]

/-- `E_x ξ_x(s)² = Γ_true(s)` and `E_x ξ_x(s) ξ_x(s') = 0` for `s ≠ s'`: the noise covariance
is `diag(Γ_true)` (C43). -/
theorem sum_tupleProb_mul_noiseVec_mul [DecidableEq State] (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) (s s' : State) :
    ∑ x, tupleProb M π μ x * (noiseVec M π x s * noiseVec M π x s') =
      if s = s' then trueGamma M π μ s else 0 := by
  split_ifs with h
  · subst h
    have e : ∀ x : Tuple State Action, noiseVec M π x s * noiseVec M π x s =
        if s = x.1 then tdNoise M π (s, x.2.1, x.2.2) ^ 2 else 0 := by
      intro x; rw [noiseVec_apply]; split_ifs <;> ring
    simp_rw [e]
    rw [sum_tupleProb_mul_ite_zero M π μ s (fun a s' ↦ tdNoise M π (s, a, s') ^ 2),
      trueGamma_eq]
  · refine sum_eq_zero fun x _ ↦ ?_
    rw [noiseVec_apply, noiseVec_apply]
    split_ifs with h1 h2 <;> simp_all

/-! ## Diagonal dominance of `A` -/

/-- `(1−γ) μmin ‖v‖_∞ ≤ ‖A v‖_∞` when `μmin ≤ μ(s)` for all `s`. -/
theorem mul_norm_le_norm_tdA_mulVec [DecidableEq State] (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) {μmin : ℝ}
    (hμmin0 : 0 ≤ μmin) (hμmin : ∀ s, μmin ≤ μ.prob s) (v : State → ℝ) :
    (1 - M.discount) * μmin * ‖v‖ ≤ ‖tdA M π μ *ᵥ v‖ := by
  have hγ0 := M.discount_nonneg
  have hγ1 : 0 ≤ 1 - M.discount := by linarith [M.discount_lt_one]
  rcases isEmpty_or_nonempty State with hS | hS
  · simp [Subsingleton.elim v 0]
  obtain ⟨s, -, hs⟩ := Finset.exists_max_image Finset.univ (fun s ↦ |v s|) Finset.univ_nonempty
  have hnorm : ‖v‖ ≤ |v s| :=
    (pi_norm_le_iff_of_nonneg (abs_nonneg _)).2 fun s' ↦ by
      rw [Real.norm_eq_abs]; exact hs s' (Finset.mem_univ _)
  have hE : |(M.policyTransition π s).expectation v| ≤ |v s| :=
    (M.policyTransition π s).abs_expectation_le fun s' ↦ hs s' (Finset.mem_univ _)
  have hAs : (1 - M.discount) * μmin * |v s| ≤ |(tdA M π μ *ᵥ v) s| := by
    rw [tdA_mulVec_apply, abs_mul, abs_of_nonneg (μ.prob_nonneg s)]
    have h1 : (1 - M.discount) * |v s| ≤ |v s - M.discount * (M.policyTransition π s).expectation v| := by
      have := abs_sub_abs_le_abs_sub (v s) (M.discount * (M.policyTransition π s).expectation v)
      rw [abs_mul, abs_of_nonneg hγ0] at this
      nlinarith [mul_le_mul_of_nonneg_left hE hγ0]
    have h2 : μmin * ((1 - M.discount) * |v s|) ≤
        μ.prob s * |v s - M.discount * (M.policyTransition π s).expectation v| :=
      mul_le_mul (hμmin s) h1 (by positivity) (μ.prob_nonneg s)
    linarith
  calc (1 - M.discount) * μmin * ‖v‖ ≤ (1 - M.discount) * μmin * |v s| :=
        mul_le_mul_of_nonneg_left hnorm (by positivity)
    _ ≤ |(tdA M π μ *ᵥ v) s| := hAs
    _ ≤ ‖tdA M π μ *ᵥ v‖ := abs_apply_le_norm _ s

/-- `A = diag(μ)(I − γP_π)` is invertible when `μ > 0`. -/
theorem tdA_isUnit [DecidableEq State] (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) {μmin : ℝ}
    (hμmin0 : 0 < μmin) (hμmin : ∀ s, μmin ≤ μ.prob s) : IsUnit (tdA M π μ) := by
  rw [← Matrix.mulVec_injective_iff_isUnit]
  intro v w hvw
  have hc : 0 < (1 - M.discount) * μmin := mul_pos (by linarith [M.discount_lt_one]) hμmin0
  have h := mul_norm_le_norm_tdA_mulVec M π μ hμmin0.le hμmin (v - w)
  rw [Matrix.mulVec_sub, hvw, sub_self, norm_zero] at h
  have : ‖v - w‖ = 0 := le_antisymm (by nlinarith [norm_nonneg (v - w)]) (norm_nonneg _)
  exact sub_eq_zero.1 (norm_eq_zero.1 this)

theorem tdA_mulVec_inv_mulVec [DecidableEq State] (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) {μmin : ℝ}
    (hμmin0 : 0 < μmin) (hμmin : ∀ s, μmin ≤ μ.prob s) (y : State → ℝ) :
    tdA M π μ *ᵥ ((tdA M π μ)⁻¹ *ᵥ y) = y := by
  have hdet := (Matrix.isUnit_iff_isUnit_det _).1 (tdA_isUnit M π μ hμmin0 hμmin)
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]

theorem tdA_inv_mulVec_tdA_mulVec [DecidableEq State] (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) {μmin : ℝ}
    (hμmin0 : 0 < μmin) (hμmin : ∀ s, μmin ≤ μ.prob s) (v : State → ℝ) :
    (tdA M π μ)⁻¹ *ᵥ (tdA M π μ *ᵥ v) = v := by
  have hdet := (Matrix.isUnit_iff_isUnit_det _).1 (tdA_isUnit M π μ hμmin0 hμmin)
  rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mulVec]

/-- `‖A⁻¹ y‖_∞ ≤ ‖y‖_∞ / ((1−γ) μmin)`. -/
theorem norm_tdA_inv_mulVec_le [DecidableEq State] (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) {μmin : ℝ}
    (hμmin0 : 0 < μmin) (hμmin : ∀ s, μmin ≤ μ.prob s) (y : State → ℝ) :
    ‖(tdA M π μ)⁻¹ *ᵥ y‖ ≤ ‖y‖ / ((1 - M.discount) * μmin) := by
  have hc : 0 < (1 - M.discount) * μmin := mul_pos (by linarith [M.discount_lt_one]) hμmin0
  have h := mul_norm_le_norm_tdA_mulVec M π μ hμmin0.le hμmin ((tdA M π μ)⁻¹ *ᵥ y)
  rw [tdA_mulVec_inv_mulVec M π μ hμmin0 hμmin] at h
  rw [le_div_iff₀ hc]
  linarith

end StatisticalRL.Ch7Rest.TDInference
