import Formalization.TDInference.PathMarginals
import Formalization.TDInference.StepSize
import Formalization.Probability.WeightedL2

/-!
# Theorem 7.11 support (M3): TD noise at `V^π`, pathwise bounds and second moments

Source: `chapters/inference.tex:47–117` (i.i.d. `μ`-sampling, asynchronous TD update :72, `A`, `Γ`
:99–117); `P_π`, `r_π` are `prelim.tex:405–419`. Objects of `TDInference/Definitions.lean` (M1).

For a tuple `x = (s, a, s')` write `Δ = V − V^π` and
`ξ(x) = V^π(s) − r(s,a) − γ V^π(s')` (`tdNoise`). Exactly (`tdStep_sub_value_apply`):

`(TDstep_η V x)(s) − V^π(s) = (1−η)Δ(s) + ηγΔ(s') − η ξ(x)` if `s = x.1`, and `Δ(s)` otherwise,

i.e. `Δ' = Δ − η(A_x Δ + ξ_x)` with `A_x = e_s(e_s − γ e_{s'})ᵀ`, `ξ_x = ξ(x) e_s`.

Main results (all constants explicit):
* `tupleCondExp_tdNoise`: `E[ξ | s] = 0` (Bellman equation for `V^π`); `trueGamma_eq`:
  `trueGamma s = μ(s) E[ξ² | s]`, the per-sample noise covariance (diagonal, C43).
* `abs_tdNoise_le`: `|ξ| ≤ B := 1 + (1+γ)‖V^π‖_∞` (`tdNoiseBound`).
* `abs_tdIter_sub_le`: for `0 ≤ η₀ ≤ 1`, pathwise `‖V_t − V^π‖_∞ ≤ D := max(‖V₀ − V^π‖_∞, B/(1−γ))`
  (`tdPathBound`), for every sample path and every `t`.
* `tdSecondMoment_succ_le`: with `q_t(s) = E (V_t(s) − V^π(s))²`, if `q_t ≤ Q` coordinatewise then
  `q_{t+1}(s) ≤ (1 − μmin(1−γ)η_{t+1}) Q + η_{t+1}² (B² + 2BD)` whenever `μmin ≤ μ(s)`.
* `tdSecondMoment_le`: for `0 < η₀ ≤ 1`, `0 < μmin ≤ min_s μ(s)` and every `t ≥ 1`,
  `E (V_t(s) − V^π(s))² ≤ C · η₀ t^{-2/3}` with the explicit
  `C = max(2(B² + 2BD)/(μmin(1−γ)), D²/η_{t₁})`, `t₁ = ⌈(2/(μmin(1−γ)η₀))³⌉ + 1` (`tdMomentConst`).

Coefficient caveat: `C` is not on the noise scale `Tr Γ_true`; it carries `B` and `D` (hence
`‖V₀ − V^π‖_∞`) and a polynomial transient factor in `1/(μmin(1−γ)η₀)`.
-/

open Finset
open scoped BigOperators

namespace StatisticalRL.Ch7Rest.TDInference

open StatisticalRL.Probability

variable {State Action : Type} [Fintype State] [Fintype Action]

/-! ## The TD noise at `V^π` -/

/-- The TD error of the tuple `x = (s,a,s')` at the true value function,
`ξ(x) = V^π(s) − r(s,a) − γ V^π(s')`. -/
noncomputable def tdNoise (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (x : Tuple State Action) : ℝ :=
  M.valueFixedPoint π x.1 - M.reward x.1 x.2.1 - M.discount * M.valueFixedPoint π x.2.2

/-- The explicit bound `B = 1 + (1+γ)‖V^π‖_∞` on the TD noise. -/
noncomputable def tdNoiseBound (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) : ℝ :=
  1 + (1 + M.discount) * ‖M.valueFixedPoint π‖

theorem tdNoiseBound_pos (M : DiscountedMDP State Action) (π : StationaryPolicy State Action) :
    0 < tdNoiseBound M π := by
  have := M.discount_nonneg
  unfold tdNoiseBound; positivity

theorem abs_apply_le_norm (V : State → ℝ) (s : State) : |V s| ≤ ‖V‖ := by
  simpa [Real.norm_eq_abs] using norm_le_pi_norm V s

theorem abs_tdNoise_le (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (x : Tuple State Action) : |tdNoise M π x| ≤ tdNoiseBound M π := by
  have h1 := abs_apply_le_norm (M.valueFixedPoint π) x.1
  have h2 := abs_apply_le_norm (M.valueFixedPoint π) x.2.2
  have hr0 := M.reward_nonneg x.1 x.2.1
  have hr1 := M.reward_le_one x.1 x.2.1
  have hγ := M.discount_nonneg
  have hγ2 : M.discount * |M.valueFixedPoint π x.2.2| ≤ M.discount * ‖M.valueFixedPoint π‖ :=
    mul_le_mul_of_nonneg_left h2 hγ
  rw [abs_le] at h1 h2 ⊢
  unfold tdNoise tdNoiseBound
  constructor <;> nlinarith [abs_le.mp (le_refl |M.valueFixedPoint π x.2.2|),
    mul_le_mul_of_nonneg_left h2.2 hγ, mul_le_mul_of_nonneg_left (neg_le.mp h2.1) hγ]

/-- The conditional expectation over `(a, s') ∼ π(·|s) ⊗ P(·|s,a)` given the state `s`. -/
noncomputable def tupleCondExp (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (s : State) (h : Action → State → ℝ) : ℝ :=
  (π s).expectation fun a ↦ (M.transition s a).expectation (h a)

/-- Affine combinations of a next-state function and a tuple function. -/
theorem tupleCondExp_affine (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (s : State) (c₀ c₁ c₂ : ℝ) (f : State → ℝ) (g : Action → State → ℝ) :
    tupleCondExp M π s (fun a s' ↦ c₀ + c₁ * f s' + c₂ * g a s') =
      c₀ + c₁ * (M.policyTransition π s).expectation f + c₂ * tupleCondExp M π s g := by
  unfold tupleCondExp
  rw [DiscountedMDP.policyTransition, FiniteDistribution.expectation_bind]
  simp only [FiniteDistribution.expectation, mul_add, sum_add_distrib, ← sum_mul,
    (M.transition _ _).sum_prob, (π s).sum_prob, one_mul, mul_sum]
  congr 1
  · congr 1
    refine sum_congr rfl fun a _ ↦ sum_congr rfl fun s' _ ↦ by ring
  · refine sum_congr rfl fun a _ ↦ sum_congr rfl fun s' _ ↦ by ring

theorem tupleCondExp_mono (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (s : State) {g h : Action → State → ℝ} (hgh : ∀ a s', g a s' ≤ h a s') :
    tupleCondExp M π s g ≤ tupleCondExp M π s h :=
  (π s).expectation_mono fun a ↦ (M.transition s a).expectation_mono (hgh a)

/-- The TD noise is conditionally centred: `E[ξ | s] = 0` (the Bellman equation for `V^π`). -/
theorem tupleCondExp_tdNoise (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (s : State) : tupleCondExp M π s (fun a s' ↦ tdNoise M π (s, a, s')) = 0 := by
  have hB := congrFun (M.valueFixedPoint_spec π) s
  unfold DiscountedMDP.valueBellman at hB
  have e : (fun a s' ↦ tdNoise M π (s, a, s')) = fun a s' ↦ M.valueFixedPoint π s +
      (-M.discount) * M.valueFixedPoint π s' + (-1) * (fun a (_ : State) ↦ M.reward s a) a s' := by
    funext a s'; simp only [tdNoise]; ring
  have hr : tupleCondExp M π s (fun a (_ : State) ↦ M.reward s a) =
      (π s).expectation (M.reward s) := by
    simp [tupleCondExp]
  rw [e, tupleCondExp_affine, hr]
  linarith

/-- The per-sample noise covariance (diagonal entry, C43): `Γ_true(s) = μ(s) E[ξ² | s]`. -/
theorem trueGamma_eq (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (μ : FiniteDistribution State) (s : State) :
    trueGamma M π μ s = μ.prob s * tupleCondExp M π s (fun a s' ↦ tdNoise M π (s, a, s') ^ 2) :=
  rfl

theorem tupleCondExp_sub_const (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (s : State) (h : Action → State → ℝ) (c : ℝ) :
    tupleCondExp M π s (fun a s' ↦ h a s' - c) = tupleCondExp M π s h - c := by
  simp only [tupleCondExp, FiniteDistribution.expectation, mul_sub, sum_sub_distrib, ← sum_mul,
    FiniteDistribution.sum_prob, one_mul]

/-- `E[1{s₀ = s} g(a,s')] = μ(s) E[g | s]`. -/
theorem sum_tupleProb_mul_ite_zero (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) [DecidableEq State]
    (s : State) (g : Action → State → ℝ) :
    ∑ x : Tuple State Action, tupleProb M π μ x * (if s = x.1 then g x.2.1 x.2.2 else 0) =
      μ.prob s * tupleCondExp M π s g := by
  rw [Fintype.sum_prod_type, Finset.sum_eq_single s]
  · simp [Fintype.sum_prod_type, tupleProb, tupleCondExp, FiniteDistribution.expectation,
      mul_sum, mul_assoc]
  · intro b _ hb
    simp [Ne.symm hb]
  · simp

/-- Integrating a function that is constant `c` off the state `s`:
`E[1{s₀ = s} h(a,s') + 1{s₀ ≠ s} c] = (1 − μ(s)) c + μ(s) E[h | s]`. -/
theorem sum_tupleProb_mul_ite (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (μ : FiniteDistribution State) [DecidableEq State] (s : State) (h : Action → State → ℝ)
    (c : ℝ) :
    ∑ x : Tuple State Action, tupleProb M π μ x * (if s = x.1 then h x.2.1 x.2.2 else c) =
      (1 - μ.prob s) * c + μ.prob s * tupleCondExp M π s h := by
  have e : ∀ x : Tuple State Action, tupleProb M π μ x * (if s = x.1 then h x.2.1 x.2.2 else c) =
      tupleProb M π μ x * c +
        tupleProb M π μ x * (if s = x.1 then h x.2.1 x.2.2 - c else 0) := by
    intro x; split_ifs <;> ring
  simp_rw [e]
  have h0 := sum_tupleProb_mul_ite_zero M π μ s (fun a s' ↦ h a s' - c)
  beta_reduce at h0
  rw [sum_add_distrib, ← sum_mul, sum_tupleProb, h0, tupleCondExp_sub_const]
  ring

/-! ## The exact error recursion and the pathwise bound -/

/-- The exact one-step error recursion of asynchronous TD at `V^π`
(`Δ' = Δ − η(A_x Δ + ξ_x)`, coordinatewise). -/
theorem tdStep_sub_value_apply [DecidableEq State] (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (η : ℝ) (V : State → ℝ) (x : Tuple State Action)
    (s : State) :
    tdStep M η V x s - M.valueFixedPoint π s =
      if s = x.1 then (1 - η) * (V s - M.valueFixedPoint π s) +
          η * M.discount * (V x.2.2 - M.valueFixedPoint π x.2.2) - η * tdNoise M π x
      else V s - M.valueFixedPoint π s := by
  unfold tdStep
  rw [Function.update_apply]
  split_ifs with h
  · subst h; unfold tdNoise; ring
  · rfl

/-- The pathwise radius `D = max(‖V₀ − V^π‖_∞, B/(1−γ))`. -/
noncomputable def tdPathBound (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (V₀ : State → ℝ) : ℝ :=
  max ‖V₀ - M.valueFixedPoint π‖ (tdNoiseBound M π / (1 - M.discount))

theorem tdPathBound_nonneg (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (V₀ : State → ℝ) : 0 ≤ tdPathBound M π V₀ :=
  le_max_of_le_left (norm_nonneg _)

/-- One TD step with `η ∈ [0,1]` keeps `|V − V^π| ≤ D` whenever `B/(1−γ) ≤ D`. -/
theorem abs_tdStep_sub_le [DecidableEq State] (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) {η D : ℝ} (h0 : 0 ≤ η) (h1 : η ≤ 1)
    (hD : tdNoiseBound M π / (1 - M.discount) ≤ D) {V : State → ℝ}
    (hV : ∀ s, |V s - M.valueFixedPoint π s| ≤ D) (x : Tuple State Action) (s : State) :
    |tdStep M η V x s - M.valueFixedPoint π s| ≤ D := by
  rw [tdStep_sub_value_apply M π]
  split_ifs with h
  · have hγ0 := M.discount_nonneg
    have hγ1 := M.discount_lt_one
    have hB : tdNoiseBound M π ≤ (1 - M.discount) * D := by
      rwa [div_le_iff₀ (by linarith), mul_comm] at hD
    have ha := abs_le.mp (hV s)
    have hb := abs_le.mp (hV x.2.2)
    have hξ := abs_le.mp (abs_tdNoise_le M π x)
    have hηγ : 0 ≤ η * M.discount := mul_nonneg h0 hγ0
    rw [abs_le]
    constructor <;> nlinarith [mul_le_mul_of_nonneg_left ha.2 (sub_nonneg.2 h1),
      mul_le_mul_of_nonneg_left ha.1 (sub_nonneg.2 h1), mul_le_mul_of_nonneg_left hb.2 hηγ,
      mul_le_mul_of_nonneg_left hb.1 hηγ, mul_le_mul_of_nonneg_left hξ.2 h0,
      mul_le_mul_of_nonneg_left hξ.1 h0, mul_le_mul_of_nonneg_left hB h0]
  · exact hV s

/-- Pathwise bound: for `0 ≤ η₀ ≤ 1`, every iterate satisfies `|V_t(s) − V^π(s)| ≤ D`. -/
theorem abs_tdIter_sub_le [DecidableEq State] (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) {η₀ : ℝ} (h0 : 0 ≤ η₀) (h1 : η₀ ≤ 1) (V₀ : State → ℝ)
    {T : ℕ} (ω : Fin T → Tuple State Action) (t : ℕ) (s : State) :
    |tdIter M η₀ V₀ ω t s - M.valueFixedPoint π s| ≤ tdPathBound M π V₀ := by
  induction t generalizing s with
  | zero =>
    have := abs_apply_le_norm (V₀ - M.valueFixedPoint π) s
    simp only [Pi.sub_apply] at this
    exact this.trans (le_max_left _ _)
  | succ t ih =>
    rw [tdIter]
    split_ifs with h
    · exact abs_tdStep_sub_le M π (stepSize_nonneg h0 _)
        ((stepSize_le h0 (Nat.le_add_left 1 t)).trans h1) (le_max_right _ _) ih _ s
    · exact ih s

/-! ## Second moments -/

/-- The scalar inequality behind the one-step bound:
`((1−η)d + ηγe − ηξ)² ≤ (1−η(1−γ))(1−η)d² + η²(B² + 2BD) + (1−η(1−γ))ηγ e² − 2η(1−η)dξ`
whenever `0 ≤ η ≤ 1`, `0 ≤ γ`, `ξ² ≤ B²` and `−γeξ ≤ BD`. -/
theorem sq_tdStep_error_le {η γ d e ξ B D : ℝ} (h0 : 0 ≤ η) (h1 : η ≤ 1) (hγ0 : 0 ≤ γ)
    (hξ2 : ξ ^ 2 ≤ B ^ 2) (heξ : -(γ * e * ξ) ≤ B * D) :
    ((1 - η) * d + η * γ * e - η * ξ) ^ 2 ≤
      (1 - η * (1 - γ)) * (1 - η) * d ^ 2 + η ^ 2 * (B ^ 2 + 2 * B * D) +
        (1 - η * (1 - γ)) * (η * γ) * e ^ 2 + -(2 * η * (1 - η) * d) * ξ := by
  have k1 : 0 ≤ (1 - η) * (η * γ) * (d - e) ^ 2 :=
    mul_nonneg (mul_nonneg (by linarith) (mul_nonneg h0 hγ0)) (sq_nonneg _)
  have k2 : 0 ≤ η ^ 2 * (B ^ 2 - ξ ^ 2) := mul_nonneg (sq_nonneg _) (by linarith)
  have k3 : 0 ≤ η ^ 2 * (B * D + γ * e * ξ) := mul_nonneg (sq_nonneg _) (by linarith)
  have e : (1 - η * (1 - γ)) * (1 - η) * d ^ 2 + η ^ 2 * (B ^ 2 + 2 * B * D) +
      (1 - η * (1 - γ)) * (η * γ) * e ^ 2 + -(2 * η * (1 - η) * d) * ξ -
        ((1 - η) * d + η * γ * e - η * ξ) ^ 2 =
      (1 - η) * (η * γ) * (d - e) ^ 2 + η ^ 2 * (B ^ 2 - ξ ^ 2) +
        2 * (η ^ 2 * (B * D + γ * e * ξ)) := by ring
  linarith

/-- One-step conditional second moment at coordinate `s`, for `η ∈ [0,1]` and `|V − V^π| ≤ D`:
`E_x (TDstep_η V x)(s) − V^π(s))² ≤ (1−μ(s))Δ(s)² + μ(s)[(1−η(1−γ))((1−η)Δ(s)² + ηγ E_{P_π}Δ²)
+ η²(B² + 2BD)]`. -/
theorem sum_tupleProb_mul_sq_tdStep_sub_le [DecidableEq State] (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) {η D : ℝ} (h0 : 0 ≤ η)
    (h1 : η ≤ 1) {V : State → ℝ} (hV : ∀ s, |V s - M.valueFixedPoint π s| ≤ D) (s : State) :
    ∑ x, tupleProb M π μ x * (tdStep M η V x s - M.valueFixedPoint π s) ^ 2 ≤
      (1 - μ.prob s) * (V s - M.valueFixedPoint π s) ^ 2 +
        μ.prob s * ((1 - η * (1 - M.discount)) * ((1 - η) * (V s - M.valueFixedPoint π s) ^ 2 +
          η * M.discount * (M.policyTransition π s).expectation
            (fun s' ↦ (V s' - M.valueFixedPoint π s') ^ 2)) +
          η ^ 2 * (tdNoiseBound M π ^ 2 + 2 * tdNoiseBound M π * D)) := by
  set B := tdNoiseBound M π with hBdef
  set Vπ := M.valueFixedPoint π
  set γ := M.discount with hγdef
  set c₀ := (1 - η * (1 - γ)) * (1 - η) * (V s - Vπ s) ^ 2 + η ^ 2 * (B ^ 2 + 2 * B * D)
  set c₁ := (1 - η * (1 - γ)) * (η * γ)
  set c₂ := -(2 * η * (1 - η) * (V s - Vπ s))
  set H : Action → State → ℝ := fun a s' ↦
    c₀ + c₁ * (V s' - Vπ s') ^ 2 + c₂ * tdNoise M π (s, a, s') with hH
  have hγ0 : 0 ≤ γ := M.discount_nonneg
  have hγ1 : γ < 1 := M.discount_lt_one
  have hpt : ∀ x : Tuple State Action, (tdStep M η V x s - Vπ s) ^ 2 ≤
      if s = x.1 then H x.2.1 x.2.2 else (V s - Vπ s) ^ 2 := by
    rintro ⟨s₀, a, s'⟩
    rw [tdStep_sub_value_apply M π]
    dsimp only
    split_ifs with h
    · subst h
      set d := V s - Vπ s
      set e := V s' - Vπ s'
      set ξ := tdNoise M π (s, a, s')
      have he := abs_le.mp (hV s')
      have hξ := abs_tdNoise_le M π (s, a, s')
      have hξ2 : ξ ^ 2 ≤ B ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hξ 2
      have heξ : -(γ * e * ξ) ≤ B * D := by
        have h1' : |e| * |ξ| ≤ D * B :=
          mul_le_mul (hV s') hξ (abs_nonneg _) ((abs_nonneg _).trans (hV s'))
        have h2' : -(γ * e * ξ) ≤ |e| * |ξ| := by
          calc -(γ * e * ξ) ≤ |γ * e * ξ| := neg_le_abs _
            _ = γ * (|e| * |ξ|) := by rw [abs_mul, abs_mul, abs_of_nonneg hγ0, mul_assoc]
            _ ≤ 1 * (|e| * |ξ|) := by
                exact mul_le_mul_of_nonneg_right hγ1.le (mul_nonneg (abs_nonneg _) (abs_nonneg _))
            _ = |e| * |ξ| := one_mul _
        linarith
      simp only [hH, c₀, c₁, c₂]
      exact sq_tdStep_error_le h0 h1 hγ0 hξ2 heξ
    · exact le_rfl
  calc ∑ x, tupleProb M π μ x * (tdStep M η V x s - Vπ s) ^ 2
      ≤ ∑ x : Tuple State Action, tupleProb M π μ x *
          (if s = x.1 then H x.2.1 x.2.2 else (V s - Vπ s) ^ 2) :=
        sum_le_sum fun x _ ↦ mul_le_mul_of_nonneg_left (hpt x) (tupleProb_nonneg M π μ x)
    _ = (1 - μ.prob s) * (V s - Vπ s) ^ 2 + μ.prob s * tupleCondExp M π s H :=
        sum_tupleProb_mul_ite M π μ s H _
    _ = _ := by
        rw [hH, tupleCondExp_affine, tupleCondExp_tdNoise]
        simp only [c₀, c₁, c₂]
        ring

/-- A weighted average of an affine expression, with weights summing to one. -/
theorem sum_mul_affine_eq {Ω ι : Type*} [Fintype Ω] [Fintype ι] {w : Ω → ℝ}
    (hw : ∑ ω, w ω = 1) (α β κ : ℝ) (p : ι → ℝ) (F : Ω → ℝ) (G : Ω → ι → ℝ) :
    ∑ ω, w ω * (α * F ω + β * ∑ i, p i * G ω i + κ) =
      α * ∑ ω, w ω * F ω + β * ∑ i, p i * ∑ ω, w ω * G ω i + κ := by
  simp only [mul_add, sum_add_distrib, mul_sum]
  congr 1
  · congr 1
    · exact sum_congr rfl fun ω _ ↦ by ring
    · rw [sum_comm]
      exact sum_congr rfl fun i _ ↦ sum_congr rfl fun ω _ ↦ by ring
  · rw [← sum_mul, hw, one_mul]

/-- `q_t(s) = E (V_t(s) − V^π(s))²` under the length-`t` i.i.d. path law. -/
noncomputable def tdSecondMoment [DecidableEq State] (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) (η₀ : ℝ)
    (V₀ : State → ℝ) (t : ℕ) (s : State) : ℝ :=
  ∑ ω : Fin t → Tuple State Action,
    pathWeight M π μ ω * (tdIter M η₀ V₀ ω t s - M.valueFixedPoint π s) ^ 2

theorem tdSecondMoment_nonneg [DecidableEq State] (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) (η₀ : ℝ)
    (V₀ : State → ℝ) (t : ℕ) (s : State) : 0 ≤ tdSecondMoment M π μ η₀ V₀ t s :=
  sum_nonneg fun ω _ ↦ mul_nonneg (pathWeight_nonneg M π μ ω) (sq_nonneg _)

theorem tdSecondMoment_le_sq [DecidableEq State] (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) {η₀ : ℝ} (h0 : 0 ≤ η₀)
    (h1 : η₀ ≤ 1) (V₀ : State → ℝ) (t : ℕ) (s : State) :
    tdSecondMoment M π μ η₀ V₀ t s ≤ tdPathBound M π V₀ ^ 2 :=
  sum_mul_sq_le_of_abs_le (pathWeight_nonneg M π μ) (sum_pathWeight M π μ t)
    fun ω ↦ abs_tdIter_sub_le M π h0 h1 V₀ ω t s

/-- `μ(s) ≤ 1`. (Duplicates `DiscountedMDP.finiteDistribution_prob_le_one` in
`Formalization/MDP/DiscountedOccupancy.lean`; to be deduplicated at integration.) -/
theorem prob_le_one (μ : FiniteDistribution State) (s : State) : μ.prob s ≤ 1 := by
  rw [← μ.sum_prob]
  exact Finset.single_le_sum (fun s _ ↦ μ.prob_nonneg s) (Finset.mem_univ s)

/-- The second-moment recursion: if `q_t ≤ Q` coordinatewise and `μmin ≤ μ(s)`, then
`q_{t+1}(s) ≤ (1 − μmin(1−γ)η_{t+1}) Q + (B² + 2BD) η_{t+1}²`. -/
theorem tdSecondMoment_succ_le [DecidableEq State] (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) {η₀ : ℝ} (h0 : 0 ≤ η₀)
    (h1 : η₀ ≤ 1) (V₀ : State → ℝ) {μmin Q : ℝ} (t : ℕ)
    (hQ : ∀ s, tdSecondMoment M π μ η₀ V₀ t s ≤ Q) (s : State) (hμmin : μmin ≤ μ.prob s) :
    tdSecondMoment M π μ η₀ V₀ (t + 1) s ≤
      (1 - μmin * (1 - M.discount) * stepSize η₀ (t + 1)) * Q +
        (tdNoiseBound M π ^ 2 + 2 * tdNoiseBound M π * tdPathBound M π V₀) *
          stepSize η₀ (t + 1) ^ 2 := by
  set η := stepSize η₀ (t + 1)
  set Vπ := M.valueFixedPoint π
  set γ := M.discount
  set K := tdNoiseBound M π ^ 2 + 2 * tdNoiseBound M π * tdPathBound M π V₀
  have hη0 : 0 ≤ η := stepSize_nonneg h0 _
  have hη1 : η ≤ 1 := (stepSize_le h0 (Nat.le_add_left 1 t)).trans h1
  have hγ0 : 0 ≤ γ := M.discount_nonneg
  have hγ1 : γ < 1 := M.discount_lt_one
  have hμ1 := prob_le_one μ s
  have hμ0 := μ.prob_nonneg s
  have hK : 0 ≤ K := by
    have := tdNoiseBound_pos M π; have := tdPathBound_nonneg M π V₀; positivity
  have hQ0 : 0 ≤ Q := (tdSecondMoment_nonneg M π μ η₀ V₀ t s).trans (hQ s)
  set α := (1 - μ.prob s) + μ.prob s * ((1 - η * (1 - γ)) * (1 - η))
  set β := μ.prob s * ((1 - η * (1 - γ)) * (η * γ))
  have hα : 0 ≤ α := by
    have : 0 ≤ 1 - η * (1 - γ) := by nlinarith
    have : 0 ≤ 1 - η := by linarith
    have : 0 ≤ 1 - μ.prob s := by linarith
    positivity
  have hβ : 0 ≤ β := by
    have : 0 ≤ 1 - η * (1 - γ) := by nlinarith
    positivity
  unfold tdSecondMoment
  rw [sum_pathWeight_mul_tdIter_succ M π μ η₀ V₀ (fun V ↦ (V s - Vπ s) ^ 2) t]
  calc ∑ ω : Fin t → Tuple State Action, pathWeight M π μ ω *
        ∑ x, tupleProb M π μ x * (tdStep M η (tdIter M η₀ V₀ ω t) x s - Vπ s) ^ 2
      ≤ ∑ ω : Fin t → Tuple State Action, pathWeight M π μ ω *
          (α * (tdIter M η₀ V₀ ω t s - Vπ s) ^ 2 +
            β * ∑ s', (M.policyTransition π s).prob s' * (tdIter M η₀ V₀ ω t s' - Vπ s') ^ 2 +
            μ.prob s * (η ^ 2 * K)) := by
        refine sum_le_sum fun ω _ ↦ mul_le_mul_of_nonneg_left ?_ (pathWeight_nonneg M π μ ω)
        refine (sum_tupleProb_mul_sq_tdStep_sub_le M π μ hη0 hη1
          (abs_tdIter_sub_le M π h0 h1 V₀ ω t) s).trans (le_of_eq ?_)
        rw [FiniteDistribution.expectation]
        simp only [α, β, K]
        ring
    _ = α * tdSecondMoment M π μ η₀ V₀ t s +
          β * ∑ s', (M.policyTransition π s).prob s' * tdSecondMoment M π μ η₀ V₀ t s' +
          μ.prob s * (η ^ 2 * K) :=
        sum_mul_affine_eq (sum_pathWeight M π μ t) _ _ _ _ _ _
    _ ≤ α * Q + β * ∑ s', (M.policyTransition π s).prob s' * Q + μ.prob s * (η ^ 2 * K) := by
        have hsum : ∑ s', (M.policyTransition π s).prob s' * tdSecondMoment M π μ η₀ V₀ t s' ≤
            ∑ s', (M.policyTransition π s).prob s' * Q :=
          sum_le_sum fun s' _ ↦
            mul_le_mul_of_nonneg_left (hQ s') ((M.policyTransition π s).prob_nonneg s')
        nlinarith [mul_le_mul_of_nonneg_left (hQ s) hα, mul_le_mul_of_nonneg_left hsum hβ]
    _ ≤ (1 - μmin * (1 - γ) * η) * Q + K * η ^ 2 := by
        rw [← sum_mul, (M.policyTransition π s).sum_prob, one_mul]
        have hηc : η * (1 - γ) ≤ 1 := by nlinarith
        have hηc0 : 0 ≤ η * (1 - γ) := by nlinarith
        have e1 : α + β = 1 - μ.prob s * (η * (1 - γ)) * (2 - η * (1 - γ)) := by
          simp only [α, β]; ring
        have e2 : μmin * (1 - γ) * η ≤ μ.prob s * (η * (1 - γ)) * (2 - η * (1 - γ)) := by
          have : μmin * (η * (1 - γ)) ≤ μ.prob s * (η * (1 - γ)) :=
            mul_le_mul_of_nonneg_right hμmin hηc0
          nlinarith [mul_nonneg (mul_nonneg hμ0 hηc0) (sub_nonneg.2 hηc)]
        have e3 : μ.prob s * (η ^ 2 * K) ≤ K * η ^ 2 := by
          nlinarith [mul_nonneg (sq_nonneg η) hK]
        nlinarith [mul_le_mul_of_nonneg_right e2 hQ0]

/-! ## The `O(η_t)` second-moment bound with explicit constants -/

/-- The noise constant `K = B² + 2BD` of the second-moment recursion. -/
noncomputable def tdMomentNoise (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (V₀ : State → ℝ) : ℝ :=
  tdNoiseBound M π ^ 2 + 2 * tdNoiseBound M π * tdPathBound M π V₀

/-- The burn-in time `t₁ = ⌈(2/(μmin(1−γ)η₀))³⌉ + 1`, after which the schedule varies slowly
relative to the contraction rate `μmin(1−γ)`. -/
noncomputable def tdBurnIn (M : DiscountedMDP State Action) (μmin η₀ : ℝ) : ℕ :=
  ⌈(2 / (μmin * (1 - M.discount) * η₀)) ^ 3⌉₊ + 1

/-- The explicit constant `C = max(2K/(μmin(1−γ)), D²/η_{t₁})` of `tdSecondMoment_le`. -/
noncomputable def tdMomentConst (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (V₀ : State → ℝ) (μmin η₀ : ℝ) : ℝ :=
  max (2 * tdMomentNoise M π V₀ / (μmin * (1 - M.discount)))
    (tdPathBound M π V₀ ^ 2 / stepSize η₀ (tdBurnIn M μmin η₀))

theorem tdMomentNoise_nonneg (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (V₀ : State → ℝ) : 0 ≤ tdMomentNoise M π V₀ := by
  have := tdNoiseBound_pos M π; have := tdPathBound_nonneg M π V₀
  unfold tdMomentNoise; positivity

theorem tdMomentConst_nonneg (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (V₀ : State → ℝ) {μmin η₀ : ℝ} (hμ : 0 < μmin) :
    0 ≤ tdMomentConst M π V₀ μmin η₀ := by
  have := tdMomentNoise_nonneg M π V₀
  have : 0 < 1 - M.discount := by linarith [M.discount_lt_one]
  exact le_max_of_le_left (by positivity)

/-- **Second moments of asynchronous TD under i.i.d. `μ`-sampling.** For `0 < η₀ ≤ 1`,
`0 < μmin ≤ μ(s)` for all `s`, every `t ≥ 1` and every state `s`,
`E (V_t(s) − V^π(s))² ≤ C η₀ t^{-2/3}` with `C = tdMomentConst M π V₀ μmin η₀
= max(2(B² + 2BD)/(μmin(1−γ)), D²/η_{t₁})`, `B = 1 + (1+γ)‖V^π‖_∞`,
`D = max(‖V₀ − V^π‖_∞, B/(1−γ))`, `t₁ = ⌈(2/(μmin(1−γ)η₀))³⌉ + 1`. -/
theorem tdSecondMoment_le [DecidableEq State] (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) {η₀ : ℝ} (h0 : 0 < η₀)
    (h1 : η₀ ≤ 1) (V₀ : State → ℝ) {μmin : ℝ} (hμmin0 : 0 < μmin)
    (hμmin : ∀ s, μmin ≤ μ.prob s) {t : ℕ} (ht : 1 ≤ t) (s : State) :
    tdSecondMoment M π μ η₀ V₀ t s ≤ tdMomentConst M π V₀ μmin η₀ * stepSize η₀ t := by
  set a := μmin * (1 - M.discount) with ha
  set K := tdMomentNoise M π V₀
  set t₁ := tdBurnIn M μmin η₀ with ht₁
  set C := tdMomentConst M π V₀ μmin η₀ with hC
  set D := tdPathBound M π V₀
  have hγ1 : 0 < 1 - M.discount := by linarith [M.discount_lt_one]
  have ha0 : 0 < a := mul_pos hμmin0 hγ1
  have hK : 0 ≤ K := tdMomentNoise_nonneg M π V₀
  have hC0 : 0 ≤ C := tdMomentConst_nonneg M π V₀ hμmin0
  have ht₁1 : 1 ≤ t₁ := Nat.le_add_left 1 _
  have hηt₁ : 0 < stepSize η₀ t₁ := stepSize_pos h0 ht₁1
  have hearly : ∀ n, 1 ≤ n → n ≤ t₁ → ∀ s, tdSecondMoment M π μ η₀ V₀ n s ≤ C * stepSize η₀ n := by
    intro n hn hnt s
    calc tdSecondMoment M π μ η₀ V₀ n s ≤ D ^ 2 := tdSecondMoment_le_sq M π μ h0.le h1 V₀ n s
      _ = D ^ 2 / stepSize η₀ t₁ * stepSize η₀ t₁ := by field_simp
      _ ≤ C * stepSize η₀ n := by
          refine mul_le_mul (le_max_right _ _) (stepSize_anti h0.le hn hnt) hηt₁.le hC0
  induction t, ht using Nat.le_induction generalizing s with
  | base => exact hearly 1 le_rfl ht₁1 s
  | succ n hn ih =>
    by_cases hn1 : n + 1 ≤ t₁
    · exact hearly (n + 1) (Nat.le_add_left 1 n) hn1 s
    push_neg at hn1
    have hnt : t₁ ≤ n := by omega
    -- the schedule varies slowly after the burn-in
    have hcube : 2 / (a * η₀) ≤ natCubeRoot (n + 1) := by
      refine le_of_pow_le_pow_left₀ (by norm_num : (3 : ℕ) ≠ 0) (natCubeRoot_nonneg _) ?_
      rw [natCubeRoot_cube]
      have h3 : (2 / (a * η₀)) ^ 3 ≤ (t₁ : ℝ) := by
        rw [ht₁, tdBurnIn]
        push_cast
        have := Nat.le_ceil ((2 / (μmin * (1 - M.discount) * η₀)) ^ 3)
        linarith
      have : (t₁ : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast (Nat.le_succ_of_le hnt)
      linarith
    have hslow := stepSize_sub_succ_le h0 ha0 hn hcube
    have hμs := hμmin s
    have haη : a * stepSize η₀ (n + 1) ≤ 1 := by
      have h2 : stepSize η₀ (n + 1) ≤ 1 := (stepSize_le h0.le (Nat.le_add_left 1 n)).trans h1
      have h3 : a ≤ 1 := by
        have := prob_le_one μ s
        have : 1 - M.discount ≤ 1 := by linarith [M.discount_nonneg]
        rw [ha]; nlinarith
      nlinarith [stepSize_nonneg h0.le (n + 1)]
    have hbC : 2 * K ≤ a * C := by
      have : 2 * K / a ≤ C := le_max_left _ _
      rw [div_le_iff₀ ha0] at this
      nlinarith
    refine (tdSecondMoment_succ_le M π μ h0.le h1 V₀ n ih s hμs).trans ?_
    exact stepRecursion_le (stepSize_nonneg h0.le _) haη hC0 hbC
      (stepSize_succ_le_stepSize h0.le hn) hslow le_rfl

end StatisticalRL.Ch7Rest.TDInference
