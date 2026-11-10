import Formalization.RLHF.VPO.Confidence
import Formalization.RLHF.VPO.Elliptical

/-!
# Corrected Theorem 7.12: multiplicative concentration E₂

Event E₂. With `V_k = 4I + ∑_{j<k} d_j d_jᵀ` built from the realized
feature differences, `X_k = ‖d_k‖²_{V_k⁻¹} ∈ [0,1]` has conditional mean
`u_k = E_{x∼ρ, y,y'∼π_k} ‖φ(x,y) − φ(x,y')‖²_{V_k⁻¹}`; so `exp((1 − e⁻¹) u_k − X_k)` has
conditional mean at most one and, with the elliptical potential,
`∑_k u_k ≤ (e/(e−1)) (2 d log(1 + T/d) + log(2/δ))` off an event of probability `δ/2`.
-/

namespace StatisticalRL.Ch7Rest.Rlhf

open Finset Real

set_option linter.unusedSectionVars false

variable {X Y : Type} [Fintype X] [Fintype Y] {d : ℕ}

/-- Coordinates of a Euclidean vector. -/
def ev (a : EuclideanSpace ℝ (Fin d)) : Fin d → ℝ := fun i ↦ a i

theorem ev_dot (a b : EuclideanSpace ℝ (Fin d)) : ev a ⬝ᵥ ev b = inner ℝ a b := by
  simp only [ev, dotProduct, PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  exact sum_congr rfl fun i _ ↦ mul_comm _ _

theorem ev_sub (a b : EuclideanSpace ℝ (Fin d)) : ev (a - b) = ev a - ev b := by
  funext i; simp [ev]

/-- The realized feature differences as a sequence on `ℕ` (zero after round `T`). -/
noncomputable def dvec (φ : X → Y → EuclideanSpace ℝ (Fin d)) {T : ℕ}
    (h : Fin T → X × Y × Y × Bool) (n : ℕ) : Fin d → ℝ :=
  if hn : n < T then ev (dz φ (h ⟨n, hn⟩)) else 0

theorem dvec_val (φ : X → Y → EuclideanSpace ℝ (Fin d)) {T : ℕ} (h : Fin T → X × Y × Y × Bool)
    (k : Fin T) : dvec φ h k = ev (dz φ (h k)) := by
  simp [dvec, k.2]

theorem dz_norm_le (φ : X → Y → EuclideanSpace ℝ (Fin d)) (hφ : ∀ x y, ‖φ x y‖ ≤ 1)
    (ω : X × Y × Y × Bool) : ‖dz φ ω‖ ≤ 2 :=
  le_trans (norm_sub_le _ _) (by linarith [hφ ω.1 ω.2.1, hφ ω.1 ω.2.2.1])

theorem ev_dot_self_le (a : EuclideanSpace ℝ (Fin d)) {c : ℝ} (ha : ‖a‖ ≤ c) :
    ev a ⬝ᵥ ev a ≤ c ^ 2 := by
  rw [ev_dot, real_inner_self_eq_norm_sq]
  exact pow_le_pow_left₀ (norm_nonneg _) ha 2

theorem dvec_dot_le (φ : X → Y → EuclideanSpace ℝ (Fin d)) (hφ : ∀ x y, ‖φ x y‖ ≤ 1) {T : ℕ}
    (h : Fin T → X × Y × Y × Bool) (n : ℕ) : dvec φ h n ⬝ᵥ dvec φ h n ≤ 4 := by
  unfold dvec
  split_ifs
  · have := ev_dot_self_le _ (dz_norm_le φ hφ (h ⟨n, by assumption⟩)); norm_num at this ⊢
    linarith
  · simp

theorem gramMat_dvec_congr (φ : X → Y → EuclideanSpace ℝ (Fin d)) {T : ℕ}
    (h h' : Fin T → X × Y × Y × Bool) (k : Fin T) (hag : ∀ j, j < k → h j = h' j) :
    gramMat (dvec φ h) k = gramMat (dvec φ h') k := by
  unfold gramMat
  congr 1
  refine sum_congr rfl fun n hn ↦ ?_
  have hnk : n < k := mem_range.1 hn
  have hnT : n < T := lt_trans hnk k.2
  have : dvec φ h n = dvec φ h' n := by
    simp only [dvec, hnT, dif_pos]
    rw [hag ⟨n, hnT⟩ (Fin.lt_def.2 hnk)]
  rw [this]

section Stats

variable (ρ : X → ℝ) (π_ref : X → Y → ℝ) (φ : X → Y → EuclideanSpace ℝ (Fin d))
  (θstar : EuclideanSpace ℝ (Fin d)) (β : ℝ) (sel : List (X × Y × Y) → EuclideanSpace ℝ (Fin d))

/-- `u_k = E_{x∼ρ, y,y'∼π_k(·|x)} ‖φ(x,y) − φ(x,y')‖²_{V_k⁻¹}`. -/
noncomputable def uStat {T : ℕ} (h : Fin T → X × Y × Y × Bool) (k : Fin T) : ℝ :=
  ∑ x, ρ x * ∑ y1, ∑ y2, roundPolicy π_ref φ β sel h k x y1 *
    roundPolicy π_ref φ β sel h k x y2 *
      invNormSq (gramMat (dvec φ h) k) (ev (φ x y1 - φ x y2))

/-- `X_k = ‖d_k‖²_{V_k⁻¹}`. -/
noncomputable def xStat {T : ℕ} (h : Fin T → X × Y × Y × Bool) (k : Fin T) : ℝ :=
  invNormSq (gramMat (dvec φ h) k) (ev (dz φ (h k)))

theorem uStat_nonneg (hρ : ∀ x, 0 ≤ ρ x) (href : IsPositivePolicy π_ref) {T : ℕ}
    (h : Fin T → X × Y × Y × Bool) (k : Fin T) : 0 ≤ uStat ρ π_ref φ β sel h k := by
  unfold uStat roundPolicy
  have := gibbsPolicy_pos href (linReward φ (sel (vpoData h k))) β
  exact sum_nonneg fun x _ ↦ mul_nonneg (hρ x) (sum_nonneg fun y1 _ ↦ sum_nonneg fun y2 _ ↦
    mul_nonneg (mul_nonneg (this _ _).le (this _ _).le) (invNormSq_nonneg _ _ _))

theorem uStat_congr {T : ℕ} (h h' : Fin T → X × Y × Y × Bool) (k : Fin T)
    (hag : ∀ j, j < k → h j = h' j) :
    uStat ρ π_ref φ β sel h k = uStat ρ π_ref φ β sel h' k := by
  unfold uStat
  rw [roundPolicy_congr π_ref φ β sel h h' k hag, gramMat_dvec_congr φ h h' k hag]

theorem xStat_nonneg {T : ℕ} (h : Fin T → X × Y × Y × Bool) (k : Fin T) :
    0 ≤ xStat φ h k := invNormSq_nonneg _ _ _

theorem xStat_le_one (hφ : ∀ x y, ‖φ x y‖ ≤ 1) {T : ℕ} (h : Fin T → X × Y × Y × Bool)
    (k : Fin T) : xStat φ h k ≤ 1 := by
  refine le_trans (invNormSq_le _ _ _) ?_
  have := ev_dot_self_le _ (dz_norm_le φ hφ (h k))
  linarith

/-- The conditional mean of `X_k` is `u_k`. -/
theorem roundKernel_xStat {T : ℕ} (h : Fin T → X × Y × Y × Bool) (k : Fin T) :
    ∑ ω, roundKernel ρ π_ref φ θstar β sel k h ω *
        invNormSq (gramMat (dvec φ h) k) (ev (dz φ ω)) = uStat ρ π_ref φ β sel h k := by
  rw [roundKernel_sum_mul]
  unfold uStat
  refine sum_congr rfl fun x _ ↦ ?_
  congr 1
  refine sum_congr rfl fun y1 _ ↦ sum_congr rfl fun y2 _ ↦ ?_
  have hz : ∀ o : Bool, dz φ (x, y1, y2, o) = φ x y1 - φ x y2 := fun o ↦ rfl
  rw [hz true, hz false, ← add_mul, prefProb_add, one_mul]

/-- E₂: off an event of probability at most `δ/2`,
`(1 − e⁻¹) ∑_k u_k < ∑_k X_k + log(2/δ)`. -/
theorem e2_event (hρ : ∀ x, 0 ≤ ρ x) (hρ1 : ∑ x, ρ x = 1) (href : IsPositivePolicy π_ref)
    (hφ : ∀ x y, ‖φ x y‖ ≤ 1) {δ : ℝ} (hδ : 0 < δ) {T : ℕ} :
    ∑ h : Fin T → X × Y × Y × Bool, vpoTrajWeight ρ π_ref φ θstar β sel h *
      (if 2 / δ ≤ ∏ k, exp ((1 - exp (-1)) * uStat ρ π_ref φ β sel h k - xStat φ h k)
        then 1 else 0) ≤ δ / 2 := by
  have hc0 : 0 ≤ 1 - exp (-1) := by
    have : exp (-1) ≤ 1 := exp_le_one_iff.2 (by norm_num)
    linarith
  have h := adaptive_markov T (fun j h ω ↦ roundKernel ρ π_ref φ θstar β sel j h ω)
    (fun k h ↦ exp ((1 - exp (-1)) * uStat ρ π_ref φ β sel h k - xStat φ h k))
    (fun j h ω ↦ roundKernel_nonneg ρ π_ref φ θstar β sel hρ href j h ω)
    (fun j h h' hag ↦ roundKernel_congr ρ π_ref φ θstar β sel j h h' hag)
    (fun k h ↦ (exp_pos _).le)
    (fun k h h' hag ↦ by
      dsimp only
      rw [uStat_congr ρ π_ref φ β sel h h' k (fun j hj ↦ hag j hj.le)]
      unfold xStat
      rw [gramMat_dvec_congr φ h h' k (fun j hj ↦ hag j hj.le), hag k le_rfl])
    (fun k h ↦ ?_) (by positivity : (0 : ℝ) < 2 / δ)
  · refine le_trans h (le_of_eq ?_)
    field_simp
  · dsimp only
    have hupd : ∀ ω, uStat ρ π_ref φ β sel (Function.update h k ω) k = uStat ρ π_ref φ β sel h k :=
      fun ω ↦ uStat_congr ρ π_ref φ β sel _ _ k fun j hj ↦ by
        rw [Function.update_of_ne (ne_of_lt hj)]
    have hxupd : ∀ ω, xStat φ (Function.update h k ω) k =
        invNormSq (gramMat (dvec φ h) k) (ev (dz φ ω)) := by
      intro ω
      unfold xStat
      rw [gramMat_dvec_congr φ _ h k fun j hj ↦ by rw [Function.update_of_ne (ne_of_lt hj)],
        Function.update_self]
    simp only [hupd, hxupd]
    set u := uStat ρ π_ref φ β sel h k
    set c := 1 - exp (-1)
    have hpt : ∀ ω, roundKernel ρ π_ref φ θstar β sel k h ω *
        exp (c * u - invNormSq (gramMat (dvec φ h) k) (ev (dz φ ω))) ≤
        exp (c * u) * (roundKernel ρ π_ref φ θstar β sel k h ω -
          c * (roundKernel ρ π_ref φ θstar β sel k h ω *
            invNormSq (gramMat (dvec φ h) k) (ev (dz φ ω)))) := by
      intro ω
      have hX0 := invNormSq_nonneg (dvec φ h) k (ev (dz φ ω))
      have hX1 : invNormSq (gramMat (dvec φ h) k) (ev (dz φ ω)) ≤ 1 :=
        le_trans (invNormSq_le _ _ _) (by linarith [ev_dot_self_le _ (dz_norm_le φ hφ ω)])
      have he := exp_neg_le_affine hX0 hX1
      have hq := roundKernel_nonneg ρ π_ref φ θstar β sel hρ href k h ω
      rw [sub_eq_add_neg, exp_add]
      have := mul_le_mul_of_nonneg_left he (mul_nonneg hq (exp_pos (c * u)).le)
      nlinarith
    calc _ ≤ ∑ ω, exp (c * u) * (roundKernel ρ π_ref φ θstar β sel k h ω -
          c * (roundKernel ρ π_ref φ θstar β sel k h ω *
            invNormSq (gramMat (dvec φ h) k) (ev (dz φ ω)))) := sum_le_sum fun ω _ ↦ hpt ω
      _ = exp (c * u) * (1 - c * u) := by
          rw [← mul_sum, sum_sub_distrib, ← mul_sum,
            roundKernel_sum ρ π_ref φ θstar β sel hρ1 href k h,
            roundKernel_xStat ρ π_ref φ θstar β sel h k]
      _ ≤ exp (c * u) * exp (-(c * u)) := by
          refine mul_le_mul_of_nonneg_left ?_ (exp_pos _).le
          linarith [add_one_le_exp (-(c * u))]
      _ = 1 := by rw [← exp_add]; simp

/-- Off the E₂ event, `∑_k u_k ≤ Γ`. -/
theorem e2_consequence (hφ : ∀ x y, ‖φ x y‖ ≤ 1) (hd : 0 < d) {δ : ℝ} (hδ : 0 < δ) {T : ℕ}
    (h : Fin T → X × Y × Y × Bool)
    (hlt : ¬ 2 / δ ≤ ∏ k, exp ((1 - exp (-1)) * uStat ρ π_ref φ β sel h k - xStat φ h k)) :
    ∑ k, uStat ρ π_ref φ β sel h k ≤
      exp 1 / (exp 1 - 1) * (2 * d * log (1 + T / d) + log (2 / δ)) := by
  push_neg at hlt
  rw [← exp_sum, ← lt_log_iff_exp_lt (by positivity)] at hlt
  rw [sum_sub_distrib, ← mul_sum] at hlt
  have hX : ∑ k, xStat φ h k ≤ 2 * d * log (1 + T / d) := by
    have := elliptical_potential (dvec φ h) hd (dvec_dot_le φ hφ h) T
    refine le_trans (le_of_eq ?_) this
    rw [← Fin.sum_univ_eq_sum_range (fun n ↦ invNormSq (gramMat (dvec φ h) n) (dvec φ h n))]
    refine sum_congr rfl fun k _ ↦ ?_
    unfold xStat; rw [dvec_val]
  have he1 : 1 < exp 1 := one_lt_exp_iff.2 one_pos
  have hc : 1 - exp (-1) = (exp 1 - 1) / exp 1 := by
    rw [exp_neg]; field_simp
  rw [hc] at hlt
  have hpos : 0 < (exp 1 - 1) / exp 1 := div_pos (by linarith) (exp_pos 1)
  have : ∑ k, uStat ρ π_ref φ β sel h k ≤
      (2 * d * log (1 + T / d) + log (2 / δ)) / ((exp 1 - 1) / exp 1) := by
    rw [le_div_iff₀ hpos]; linarith
  refine le_trans this (le_of_eq ?_)
  field_simp

end Stats

end StatisticalRL.Ch7Rest.Rlhf
