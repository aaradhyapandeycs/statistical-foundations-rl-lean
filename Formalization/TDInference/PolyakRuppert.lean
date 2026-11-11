import Formalization.TDInference.Martingale
import Formalization.TDInference.Operator

/-!
# Theorem 7.11 support (M3): the Polyak–Ruppert decomposition with an explicit `L²` remainder

Source: `inference.tex:80–117` (`V̄_T`, `Δ̄_T`, `A`, `Γ`), the theorem :132–141.

With `Δ_t = V_t − V^π`, `ξ_k = ξ_{x_{k+1}}`, `A_k = A_{x_{k+1}}`, `η_t = η₀ t^{-2/3}`,
`w_t = 1/η_t` (`invStepSize`, `w_0 = 0`), summing the exact recursion
`Δ_{k+1} = Δ_k − η_{k+1}(A_k Δ_k + ξ_k)` gives the pathwise identity (`prResidual_apply`)

`A ∑_{k<T} Δ_{k+1} + ∑_k ξ_k = −∑_k (A_k − A)Δ_k − w_T Δ_T + ∑_{k<T}(w_{k+1} − w_k)Δ_k + A(Δ_T − Δ_0)`,

so `√T Δ̄_T = W_T + T^{-1/2} A⁻¹ R_T` with the i.i.d. Gaussian-approximable part
`W_T = −A⁻¹ T^{-1/2} ∑_k ξ_k` (`prGaussPart`) and the residual `R_T` (`prResidual`)
(`scaledError_sub_prGaussPart`).

Main bounds, proved in `TDInference/PolyakRuppertRemainder.lean` (with `B, D, C` of
`TDInference/Noise.lean`, `u_T = T^{1/3}`):
* `weightedL2_prResidual_le`: `‖R_T(s)‖_{L²} ≤ √(4D² + 12Cη₀u_T) + 4√C u_T/√η₀ + D/η₀ + 4D`;
* `weightedL2_scaledError_sub_prGaussPart_le`:
  `‖(√T Δ̄_T − W_T)(s)‖_{L²} ≤ S · (that bound) / ((1−γ) μmin √T)`, `S = |State|`;
* `weightedL2_scaledError_sub_prGaussPart_le_rpow`: `≤ S K_R / ((1−γ)μmin) · T^{-1/6}` with
  `K_R = 2D + √(12Cη₀) + 4√(C/η₀) + D/η₀ + 4D` (`prRemainderConst`).
* `sum_pathWeight_mul_prNoiseSum`: `E (∑_k ξ_k)(s) = 0`;
  `sum_pathWeight_mul_prNoiseSum_mul`: `E[(∑_k ξ_k)(s) (∑_k ξ_k)(s')] = T · 1{s = s'} Γ_true(s)`;
  `sum_pathWeight_mul_prGaussPart` and `sum_pathWeight_mul_prGaussPart_mul`: `E W_T = 0` and
  `E[W_T(s) W_T(s')] = (A⁻¹ diag(Γ_true) A⁻ᵀ)(s,s')` for `T ≥ 1` (C43: the true covariance is `Γ_true`).
* `tendsto_weightedL2_scaledError_sub_prGaussPart`: `‖(√T Δ̄_T − W_T)(s)‖_{L²} → 0`.

Coefficient caveats (CHECK F6): the rate `T^{-1/6}` is the crude telescoping rate (the plan's sharp
`T^{-1/3}` needs a second-order expansion, open); the factor `S` comes from `‖·‖_∞ ≤ ∑|·|`;
`K_R` depends on `‖V₀ − V^π‖_∞` and `‖V^π‖_∞` through `D`, `B`, `C`, not only on `Γ_true`.
-/

open Finset Matrix
open scoped BigOperators

namespace StatisticalRL.Ch7Rest.TDInference

open StatisticalRL.Probability

variable {State Action : Type} [Fintype State] [Fintype Action]

/-! ## A scalar summation identity -/

/-- Summation by parts for the Polyak–Ruppert decomposition: if
`b_k + ξ_k = w_{k+1}(d_k − d_{k+1})` for `k < n` and `w_0 = 0`, then
`∑_{k<n} a_{k+1} + ∑_{k<n} ξ_k =
  −∑_{k<n}(b_k − a_k) − w_n d_n + ∑_{k<n}(w_{k+1} − w_k) d_k + (a_n − a_0)`. -/
theorem sum_range_add_sum_range_eq_of_step (n : ℕ) (a b ξ d w : ℕ → ℝ) (hw0 : w 0 = 0)
    (hstep : ∀ k < n, b k + ξ k = w (k + 1) * (d k - d (k + 1))) :
    ∑ k ∈ range n, a (k + 1) + ∑ k ∈ range n, ξ k =
      -∑ k ∈ range n, (b k - a k) - w n * d n + ∑ k ∈ range n, (w (k + 1) - w k) * d k +
        (a n - a 0) := by
  induction n with
  | zero => simp [hw0]
  | succ n ih =>
    have h1 := ih fun k hk ↦ hstep k (by omega)
    have h2 := hstep n (by omega)
    simp only [sum_range_succ]
    linarith

theorem sum_fin_eq_sum_range_dite {X : Type*} {T : ℕ} (G : ℕ → X → ℝ) (ω : Fin T → X) :
    ∑ k : Fin T, G k (ω k) = ∑ k ∈ range T, if h : k < T then G k (ω ⟨k, h⟩) else 0 := by
  rw [← Fin.sum_univ_eq_sum_range]
  exact sum_congr rfl fun k _ ↦ by simp [k.2]

/-! ## The objects -/

/-- `Δ_t = V_t − V^π` along the sample path `ω`. -/
noncomputable def tdError [DecidableEq State] (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (η₀ : ℝ) (V₀ : State → ℝ) {T : ℕ}
    (ω : Fin T → Tuple State Action) (t : ℕ) : State → ℝ :=
  tdIter M η₀ V₀ ω t - M.valueFixedPoint π

/-- The noise sum `∑_{k<T} ξ_{x_{k+1}}`. -/
noncomputable def prNoiseSum [DecidableEq State] (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) {T : ℕ} (ω : Fin T → Tuple State Action) :
    State → ℝ :=
  ∑ k : Fin T, noiseVec M π (ω k)

/-- The leading (i.i.d.-sum) term `W_T = −A⁻¹ T^{-1/2} ∑_k ξ_k`. Here `(tdA M π μ)⁻¹` is
`Matrix.inv`, which is the junk value `0` if `A` is singular (e.g. `μ` without full support); every
theorem that relates `W_T` to the TD iterates assumes `0 < μmin ≤ μ(s)`, under which `A` is
invertible (`tdA_isUnit`). -/
noncomputable def prGaussPart [DecidableEq State] (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) {T : ℕ}
    (ω : Fin T → Tuple State Action) : State → ℝ :=
  -((Real.sqrt T)⁻¹ • ((tdA M π μ)⁻¹ *ᵥ prNoiseSum M π ω))

/-- The residual `R_T = A ∑_{k<T} Δ_{k+1} + ∑_k ξ_k` (no inverse involved; `√T Δ̄_T − W_T =
T^{-1/2} A⁻¹ R_T` is `scaledError_sub_prGaussPart`, under `0 < μmin ≤ μ(s)`). -/
noncomputable def prResidual [DecidableEq State] (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) (η₀ : ℝ)
    (V₀ : State → ℝ) {T : ℕ} (ω : Fin T → Tuple State Action) : State → ℝ :=
  tdA M π μ *ᵥ (∑ k ∈ range T, tdError M π η₀ V₀ ω (k + 1)) + prNoiseSum M π ω

/-- The martingale increment `((A_x − A)(V − V^π))(s)`. The time index `_k` is unused; it is
present only to fit the `f : ℕ → (State → ℝ) → Tuple → ℝ` shape of
`sum_pathWeight_mul_sq_sum_eq`. -/
noncomputable def prMartingaleTerm [DecidableEq State] (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) (s : State) (_k : ℕ)
    (V : State → ℝ) (x : Tuple State Action) : ℝ :=
  sampleA M x (V - M.valueFixedPoint π) s - (tdA M π μ *ᵥ (V - M.valueFixedPoint π)) s

theorem scaledError_eq [DecidableEq State] (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (η₀ : ℝ) (V₀ : State → ℝ) {T : ℕ} (hT : 1 ≤ T)
    (ω : Fin T → Tuple State Action) :
    scaledError M π η₀ V₀ ω = (Real.sqrt T)⁻¹ • ∑ k ∈ range T, tdError M π η₀ V₀ ω (k + 1) := by
  have hT0 : (0 : ℝ) < T := by exact_mod_cast hT
  have hs : (0 : ℝ) < Real.sqrt T := Real.sqrt_pos.2 hT0
  have hss : Real.sqrt T * Real.sqrt T = T := Real.mul_self_sqrt hT0.le
  funext s
  simp only [scaledError, prAverage, tdError, Pi.smul_apply, Pi.sub_apply, Finset.sum_apply,
    smul_eq_mul, Finset.sum_sub_distrib, sum_const, card_range, nsmul_eq_mul]
  have key : (Real.sqrt T)⁻¹ = Real.sqrt T * (T : ℝ)⁻¹ := by
    calc (Real.sqrt T)⁻¹ = Real.sqrt T * (Real.sqrt T * Real.sqrt T)⁻¹ := by field_simp
      _ = _ := by rw [hss]
  rw [key]
  field_simp
  rfl

/-- `√T Δ̄_T − W_T = T^{-1/2} A⁻¹ R_T`. -/
theorem scaledError_sub_prGaussPart [DecidableEq State] (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) {μmin : ℝ}
    (hμmin0 : 0 < μmin) (hμmin : ∀ s, μmin ≤ μ.prob s) (η₀ : ℝ) (V₀ : State → ℝ) {T : ℕ}
    (hT : 1 ≤ T) (ω : Fin T → Tuple State Action) :
    scaledError M π η₀ V₀ ω - prGaussPart M π μ ω =
      (Real.sqrt T)⁻¹ • ((tdA M π μ)⁻¹ *ᵥ prResidual M π μ η₀ V₀ ω) := by
  rw [prResidual, Matrix.mulVec_add, tdA_inv_mulVec_tdA_mulVec M π μ hμmin0 hμmin,
    scaledError_eq M π η₀ V₀ hT, prGaussPart, smul_add]
  abel

/-- The pathwise Polyak–Ruppert identity, coordinatewise. -/
theorem prResidual_apply [DecidableEq State] (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) {η₀ : ℝ} (h0 : 0 < η₀)
    (V₀ : State → ℝ) {T : ℕ} (ω : Fin T → Tuple State Action) (s : State) :
    prResidual M π μ η₀ V₀ ω s =
      -∑ k : Fin T, prMartingaleTerm M π μ s k (tdIter M η₀ V₀ ω k) (ω k) -
        invStepSize η₀ T * tdError M π η₀ V₀ ω T s +
        ∑ k ∈ range T, (invStepSize η₀ (k + 1) - invStepSize η₀ k) * tdError M π η₀ V₀ ω k s +
        (tdA M π μ *ᵥ (tdError M π η₀ V₀ ω T - tdError M π η₀ V₀ ω 0)) s := by
  set a : ℕ → ℝ := fun k ↦ (tdA M π μ *ᵥ tdError M π η₀ V₀ ω k) s
  set d : ℕ → ℝ := fun k ↦ tdError M π η₀ V₀ ω k s
  set b : ℕ → ℝ := fun k ↦ if h : k < T then sampleA M (ω ⟨k, h⟩) (tdError M π η₀ V₀ ω k) s else 0
  set ξ : ℕ → ℝ := fun k ↦ if h : k < T then noiseVec M π (ω ⟨k, h⟩) s else 0
  have hstep : ∀ k < T, b k + ξ k = invStepSize η₀ (k + 1) * (d k - d (k + 1)) := by
    intro k hk
    simp only [b, ξ, d, dif_pos hk]
    have hη := stepSize_pos h0 (Nat.le_add_left 1 k)
    have hrec : tdError M π η₀ V₀ ω (k + 1) = tdError M π η₀ V₀ ω k -
        stepSize η₀ (k + 1) • (sampleA M (ω ⟨k, hk⟩) (tdError M π η₀ V₀ ω k) +
          noiseVec M π (ω ⟨k, hk⟩)) := by
      simp only [tdError]
      rw [tdIter, dif_pos hk, tdStep_sub_value_eq]
    rw [hrec, invStepSize_eq_inv h0 (Nat.le_add_left 1 k)]
    simp only [Pi.sub_apply, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    field_simp
    ring
  have hid := sum_range_add_sum_range_eq_of_step T a b ξ d (invStepSize η₀) (invStepSize_zero η₀)
    hstep
  have hA : (tdA M π μ *ᵥ ∑ k ∈ range T, tdError M π η₀ V₀ ω (k + 1)) s =
      ∑ k ∈ range T, a (k + 1) := by
    rw [Matrix.mulVec_sum, Finset.sum_apply]
  have hN : prNoiseSum M π ω s = ∑ k ∈ range T, ξ k := by
    rw [prNoiseSum, Finset.sum_apply]
    exact sum_fin_eq_sum_range_dite (fun k x ↦ noiseVec M π x s) ω
  have hM : ∑ k : Fin T, prMartingaleTerm M π μ s k (tdIter M η₀ V₀ ω k) (ω k) =
      ∑ k ∈ range T, (b k - a k) := by
    rw [sum_fin_eq_sum_range_dite
      (fun k x ↦ prMartingaleTerm M π μ s k (tdIter M η₀ V₀ ω k) x) ω]
    refine sum_congr rfl fun k hk ↦ ?_
    have hk' : k < T := mem_range.1 hk
    simp only [b, a, dif_pos hk', prMartingaleTerm, tdError]
  have hE : (tdA M π μ *ᵥ (tdError M π η₀ V₀ ω T - tdError M π η₀ V₀ ω 0)) s = a T - a 0 := by
    rw [Matrix.mulVec_sub, Pi.sub_apply]
  rw [prResidual, Pi.add_apply, hA, hN, hid, hM, hE]

end StatisticalRL.Ch7Rest.TDInference
