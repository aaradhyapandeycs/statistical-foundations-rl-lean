import Formalization.TDInference.PolyakRuppert
import Formalization.Analysis.MatrixContractionSup

/-!
# Theorem 7.11 support (M5): the linearised TD process and its exact decomposition

Source: `chapters/inference.tex:52–64` (i.i.d. sampling), :72 (update), :82, :88 (`V̄_T`, `Δ̄_T`),
:104–117 (`A`, `Λ⋆ = A⁻¹ΓA⁻ᵀ`, `Γ`), :134 (`η_t = η₀ t^{-2/3}`); `Γ := Γ_true` (SOURCE-ISSUES C43).
Library infrastructure only (route D′ of the corrected-7.11 plan); no source result is claimed.

Indexing matches `tdIter`: the tuple `ω t` drives `V_t → V_{t+1}` with `η'_t = stepSize η₀ (t+1)`.
With `Δ_t = V_t − V^π`, `ξ_t = noiseVec (ω t)`, `ζ_t = (A_{ω t} − A)Δ_t` (`linMartVec`):

  `Δ_{t+1} = (I − η'_t A) Δ_t − η'_t ξ_t − η'_t ζ_t`.

* `linStep t = I − η'_t A`; `linKernel m t = (I − η'_{t−1}A) ⋯ (I − η'_m A)` (`matProd`).
* `linWeight T k = η'_k ∑_{t ∈ [k,T)} linKernel (k+1) (t+1)`; in the plan's notation
  `β_{k,T} = −linWeight` (sign convention: `linWeight` is the positive weight).
* `linIter`: the linearised process `Δ^lin_{t+1} = (I − η'_t A)Δ^lin_t − η'_t ξ_t`, `Δ^lin_0 = 0`;
  `linPart = T^{-1/2} ∑_{t<T} Δ^lin_{t+1}` (the analogue of `scaledError`).
* `linSummand T k x = −T^{-1/2} linWeight T k ξ_x`: `linPart_eq_sum` shows
  `linPart ω = ∑_k linSummand T k (ω k)`, an independent sum with deterministic weights.
* `linCov T = T⁻¹ ∑_{k<T} linWeight T k diag(Γ_true) linWeight T kᵀ`.
* `scaledError_sub_linPart_eq` (B3): `√TΔ̄_T − linPart = T^{-1/2}[(∑_{t<T} linKernel 0 (t+1)) Δ_0
  − ∑_k linWeight T k ζ_k]`, pathwise, for every `V₀` and `T ≥ 1`.
* `linWeight_last`: `linWeight T (T−1) = η_T • 1` for `T ≥ 1`.
-/

open Finset Matrix
open scoped BigOperators

namespace StatisticalRL.Ch7Rest.TDInference

open StatisticalRL.Probability StatisticalRL.Analysis

variable {State Action : Type} [Fintype State] [Fintype Action]

/-- `I − η'_t A` with `η'_t = stepSize η₀ (t+1)`, the mean linear map of the update using `ω t`. -/
noncomputable def linStep [DecidableEq State] (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) (η₀ : ℝ) (t : ℕ) :
    Matrix State State ℝ :=
  1 - stepSize η₀ (t + 1) • tdA M π μ

/-- The deterministic kernel `G_{m,t} = (I − η'_{t−1}A) ⋯ (I − η'_m A)` (`1` if `t ≤ m`). -/
noncomputable def linKernel [DecidableEq State] (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) (η₀ : ℝ) (m t : ℕ) :
    Matrix State State ℝ :=
  matProd (linStep M π μ η₀) m t

/-- The weight `linWeight T k = η'_k ∑_{t ∈ [k,T)} G_{k+1,t+1}` of the `k`-th sample in
`∑_{t<T} Δ_{t+1}` (the plan's `−β_{k,T}`). -/
noncomputable def linWeight [DecidableEq State] (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) (η₀ : ℝ) (T k : ℕ) :
    Matrix State State ℝ :=
  stepSize η₀ (k + 1) • ∑ t ∈ Ico k T, linKernel M π μ η₀ (k + 1) (t + 1)

/-- The linearised process `Δ^lin_{t+1} = (I − η'_t A)Δ^lin_t − η'_t ξ_{ω t}`, `Δ^lin_0 = 0`
(frozen for `t ≥ T`). -/
noncomputable def linIter [DecidableEq State] (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) (η₀ : ℝ) {T : ℕ}
    (ω : Fin T → Tuple State Action) : ℕ → State → ℝ
  | 0 => 0
  | t + 1 =>
      if h : t < T then
        linStep M π μ η₀ t *ᵥ linIter M π μ η₀ ω t - stepSize η₀ (t + 1) • noiseVec M π (ω ⟨t, h⟩)
      else linIter M π μ η₀ ω t

/-- `X^lin_T = T^{-1/2} ∑_{t<T} Δ^lin_{t+1}`. -/
noncomputable def linPart [DecidableEq State] (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) (η₀ : ℝ) {T : ℕ}
    (ω : Fin T → Tuple State Action) : State → ℝ :=
  (Real.sqrt T)⁻¹ • ∑ t ∈ range T, linIter M π μ η₀ ω (t + 1)

/-- The `k`-th summand `−T^{-1/2} linWeight T k ξ_x` of `linPart`; it depends on the tuple `x`
only, through `ξ_x = noiseVec x`. -/
noncomputable def linSummand [DecidableEq State] (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) (η₀ : ℝ) (T k : ℕ)
    (x : Tuple State Action) : State → ℝ :=
  -((Real.sqrt T)⁻¹ • (linWeight M π μ η₀ T k *ᵥ noiseVec M π x))

/-- `Λ_T = T⁻¹ ∑_{k<T} linWeight T k diag(Γ_true) linWeight T kᵀ`, the exact covariance of
`linPart` (`sum_pathWeight_linPart_mul_linPart`). -/
noncomputable def linCov [DecidableEq State] (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) (η₀ : ℝ) (T : ℕ) :
    Matrix State State ℝ :=
  (T : ℝ)⁻¹ • ∑ k ∈ range T,
    linWeight M π μ η₀ T k * diagonal (trueGamma M π μ) * (linWeight M π μ η₀ T k)ᵀ

/-- The martingale increment `ζ = (A_x − A)Δ`. -/
noncomputable def linMartVec [DecidableEq State] (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) (x : Tuple State Action)
    (Δ : State → ℝ) : State → ℝ :=
  sampleA M x Δ - tdA M π μ *ᵥ Δ

theorem linKernel_self [DecidableEq State] (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) (η₀ : ℝ) (m : ℕ) :
    linKernel M π μ η₀ m m = 1 :=
  matProd_self _ m

theorem linKernel_succ [DecidableEq State] (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) (η₀ : ℝ) {m t : ℕ}
    (h : m ≤ t) : linKernel M π μ η₀ m (t + 1) = linStep M π μ η₀ t * linKernel M π μ η₀ m t :=
  matProd_succ _ h

/-- `linWeight_last`: the last sample has weight `η_T • I` (`β_{T,T} = −η_T I`). -/
theorem linWeight_last [DecidableEq State] (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) (η₀ : ℝ) {T : ℕ}
    (hT : 1 ≤ T) : linWeight M π μ η₀ T (T - 1) = stepSize η₀ T • (1 : Matrix State State ℝ) := by
  obtain ⟨n, rfl⟩ : ∃ n, T = n + 1 := ⟨T - 1, by omega⟩
  simp only [linWeight, Nat.add_sub_cancel, Nat.Ico_succ_singleton, sum_singleton,
    linKernel_self]

/-- The exact one-step error recursion in linearised form:
`Δ_{t+1} = (I − η'_t A)Δ_t − η'_t ξ_t − η'_t ζ_t`. -/
theorem tdError_succ [DecidableEq State] (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) (η₀ : ℝ) (V₀ : State → ℝ)
    {T : ℕ} (ω : Fin T → Tuple State Action) {t : ℕ} (ht : t < T) :
    tdError M π η₀ V₀ ω (t + 1) = linStep M π μ η₀ t *ᵥ tdError M π η₀ V₀ ω t -
      stepSize η₀ (t + 1) • noiseVec M π (ω ⟨t, ht⟩) -
      stepSize η₀ (t + 1) • linMartVec M π μ (ω ⟨t, ht⟩) (tdError M π η₀ V₀ ω t) := by
  have hrec : tdError M π η₀ V₀ ω (t + 1) = tdError M π η₀ V₀ ω t -
      stepSize η₀ (t + 1) • (sampleA M (ω ⟨t, ht⟩) (tdError M π η₀ V₀ ω t) +
        noiseVec M π (ω ⟨t, ht⟩)) := by
    simp only [tdError]
    rw [tdIter, dif_pos ht, tdStep_sub_value_eq]
  rw [hrec]
  funext s
  simp only [linStep, linMartVec, sub_mulVec, one_mulVec, smul_mulVec, Pi.sub_apply,
    Pi.smul_apply, Pi.add_apply, smul_eq_mul]
  ring

/-- **The linearised process is an independent sum with deterministic weights** (F3):
`linPart ω = ∑_k linSummand T k (ω k)`. -/
theorem linPart_eq_sum [DecidableEq State] (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) (η₀ : ℝ) {T : ℕ}
    (ω : Fin T → Tuple State Action) :
    linPart M π μ η₀ ω = ∑ k : Fin T, linSummand M π μ η₀ T k (ω k) := by
  set u : ℕ → State → ℝ := fun t ↦
    if h : t < T then -(stepSize η₀ (t + 1) • noiseVec M π (ω ⟨t, h⟩)) else 0 with hu
  have hx : ∀ t < T, linIter M π μ η₀ ω (t + 1) =
      linStep M π μ η₀ t *ᵥ linIter M π μ η₀ ω t + u t := by
    intro t ht
    rw [linIter, dif_pos ht, hu]
    simp only [dif_pos ht]
    abel
  have h := sum_linRec_eq (linStep M π μ η₀) (linIter M π μ η₀ ω) u hx
  rw [linPart, h]
  simp only [linIter, mulVec_zero, zero_add]
  rw [smul_sum, ← Fin.sum_univ_eq_sum_range (fun k ↦ (Real.sqrt T)⁻¹ •
    ((∑ t ∈ Ico k T, matProd (linStep M π μ η₀) (k + 1) (t + 1)) *ᵥ u k))]
  refine sum_congr rfl fun k _ ↦ ?_
  simp only [hu, dif_pos k.2, Fin.eta, linSummand, linWeight, linKernel, mulVec_neg,
    smul_mulVec, mulVec_smul, smul_neg]

/-- **B3: pathwise decomposition of the remainder.** For `T ≥ 1` and every `V₀`,
`√TΔ̄_T − linPart = T^{-1/2}[(∑_{t<T} G_{0,t+1}) Δ_0 − ∑_k linWeight T k ζ_k]`
with `ζ_k = (A_{ω k} − A)Δ_k`. -/
theorem scaledError_sub_linPart_eq [DecidableEq State] (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) (η₀ : ℝ) (V₀ : State → ℝ)
    {T : ℕ} (hT : 1 ≤ T) (ω : Fin T → Tuple State Action) :
    scaledError M π η₀ V₀ ω - linPart M π μ η₀ ω = (Real.sqrt T)⁻¹ •
      ((∑ t ∈ range T, linKernel M π μ η₀ 0 (t + 1)) *ᵥ (V₀ - M.valueFixedPoint π) -
        ∑ k : Fin T, linWeight M π μ η₀ T k *ᵥ
          linMartVec M π μ (ω k) (tdError M π η₀ V₀ ω k)) := by
  set D : ℕ → State → ℝ := fun t ↦ tdError M π η₀ V₀ ω t - linIter M π μ η₀ ω t with hD
  set u : ℕ → State → ℝ := fun t ↦
    if h : t < T then -(stepSize η₀ (t + 1) • linMartVec M π μ (ω ⟨t, h⟩)
      (tdError M π η₀ V₀ ω t)) else 0 with hu
  have hx : ∀ t < T, D (t + 1) = linStep M π μ η₀ t *ᵥ D t + u t := by
    intro t ht
    simp only [hD, hu, dif_pos ht]
    rw [tdError_succ M π μ η₀ V₀ ω ht, linIter, dif_pos ht, mulVec_sub]
    abel
  have h := sum_linRec_eq (linStep M π μ η₀) D u hx
  rw [scaledError_eq M π η₀ V₀ hT, linPart, ← smul_sub, ← sum_sub_distrib]
  have hDs : ∀ t ∈ range T, tdError M π η₀ V₀ ω (t + 1) - linIter M π μ η₀ ω (t + 1) = D (t + 1) :=
    fun t _ ↦ rfl
  rw [sum_congr rfl hDs, h]
  congr 1
  have hD0 : D 0 = V₀ - M.valueFixedPoint π := by
    simp [hD, linIter, tdError, tdIter]
  have hU : ∑ k ∈ range T, (∑ t ∈ Ico k T, matProd (linStep M π μ η₀) (k + 1) (t + 1)) *ᵥ u k =
      -∑ k : Fin T, linWeight M π μ η₀ T k *ᵥ linMartVec M π μ (ω k) (tdError M π η₀ V₀ ω k) := by
    rw [← Fin.sum_univ_eq_sum_range (fun k ↦
      (∑ t ∈ Ico k T, matProd (linStep M π μ η₀) (k + 1) (t + 1)) *ᵥ u k), ← sum_neg_distrib]
    refine sum_congr rfl fun k _ ↦ ?_
    simp only [hu, dif_pos k.2, Fin.eta, linWeight, linKernel, mulVec_neg, smul_mulVec,
      mulVec_smul]
  rw [hD0, hU]
  exact (sub_eq_add_neg _ _).symm

end StatisticalRL.Ch7Rest.TDInference
