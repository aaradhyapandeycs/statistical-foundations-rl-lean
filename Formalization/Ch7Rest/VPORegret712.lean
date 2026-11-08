import Formalization.Ch7Rest.VPOConcentration712

/-!
# Corrected Theorem 7.12: per-round regret and the regret bounds

The bound `T B′/α + K Γ α` and the local-curvature bound
`(e^{4R/β}/(4β)) (16R² + 16e^{4R}(B′ + 4Rα)) Γ`, both on the event
`E₁ ∩ E₂` of probability at least `1 − δ`.
-/

namespace StatisticalRL.Ch7Rest.Rlhf

open Finset Real Matrix

set_option linter.unusedSectionVars false

variable {X Y : Type} [Fintype X] [Fintype Y] {d : ℕ}

/-- AM–GM step: `Δ² ≤ P G u` implies `Δ ≤ ε G + (P/(4ε)) u`. -/
theorem le_of_sq_le_mul {Δ P G u ε : ℝ} (hP : 0 ≤ P) (hG : 0 ≤ G) (hu : 0 ≤ u) (hε : 0 < ε)
    (h : Δ ^ 2 ≤ P * G * u) : Δ ≤ ε * G + P / (4 * ε) * u := by
  have hR0 : 0 ≤ ε * G + P / (4 * ε) * u := by positivity
  rcases le_or_gt Δ 0 with hΔ | hΔ
  · linarith
  · have hsq : P * G * u ≤ (ε * G + P / (4 * ε) * u) ^ 2 := by
      have h1 : (ε * G + P / (4 * ε) * u) ^ 2 =
          (ε * G - P / (4 * ε) * u) ^ 2 + P * G * u := by
        field_simp; ring
      rw [h1]; nlinarith [sq_nonneg (ε * G - P / (4 * ε) * u)]
    exact (pow_le_pow_iff_left₀ hΔ.le hR0 (by norm_num : (2 : ℕ) ≠ 0)).1 (le_trans h hsq)

theorem vpoKappa_bound (π_ref π_cal : X → Y → ℝ) (href : IsPositivePolicy π_ref) (x : X) (y : Y) :
    π_cal x y ≤ vpoKappa π_ref π_cal * π_ref x y := by
  have h : π_cal x y / π_ref x y ≤ vpoKappa π_ref π_cal :=
    le_ciSup (f := fun p : X × Y ↦ π_cal p.1 p.2 / π_ref p.1 p.2)
      (Set.finite_range _).bddAbove (x, y)
  rwa [div_le_iff₀ (href.1 x y)] at h

theorem vpoKappa_nonneg (π_ref π_cal : X → Y → ℝ) (href : IsPositivePolicy π_ref)
    (hcal : IsCondPolicy π_cal) (x : X) (y : Y) : 0 ≤ vpoKappa π_ref π_cal := by
  have := vpoKappa_bound π_ref π_cal href x y
  have h1 := hcal.1 x y
  have h2 := href.1 x y
  by_contra hk; push_neg at hk
  nlinarith

theorem linReward_abs_le (φ : X → Y → EuclideanSpace ℝ (Fin d)) (hφ : ∀ x y, ‖φ x y‖ ≤ 1)
    (θ : EuclideanSpace ℝ (Fin d)) (x : X) (y : Y) : |linReward φ θ x y| ≤ ‖θ‖ := by
  unfold linReward
  refine le_trans (abs_real_inner_le_norm _ _) ?_
  calc ‖φ x y‖ * ‖θ‖ ≤ 1 * ‖θ‖ := mul_le_mul_of_nonneg_right (hφ x y) (norm_nonneg _)
    _ = ‖θ‖ := one_mul _

theorem linReward_sub (φ : X → Y → EuclideanSpace ℝ (Fin d)) (θ θ' : EuclideanSpace ℝ (Fin d))
    (x : X) (y : Y) : linReward φ θ x y - linReward φ θ' x y = linReward φ (θ - θ') x y := by
  unfold linReward; rw [inner_sub_right]

section Round

variable (ρ : X → ℝ) (π_ref π_cal : X → Y → ℝ) (φ : X → Y → EuclideanSpace ℝ (Fin d))
  (θstar : EuclideanSpace ℝ (Fin d)) (α β R : ℝ)
  (sel : List (X × Y × Y) → EuclideanSpace ℝ (Fin d))

/-- `wᵀ V_k w = 4‖w‖² + ∑_{j<k} ⟪d_j, w⟫²`. -/
theorem gram_quad_eq {T : ℕ} (h : Fin T → X × Y × Y × Bool) (k : Fin T)
    (w : EuclideanSpace ℝ (Fin d)) :
    ev w ⬝ᵥ (gramMat (dvec φ h) k *ᵥ ev w) =
      4 * ‖w‖ ^ 2 + ∑ j ∈ univ.filter (fun j ↦ j < k), inner ℝ (dz φ (h j)) w ^ 2 := by
  rw [quad_gramMat, ev_dot, real_inner_self_eq_norm_sq]
  congr 1
  rw [← sum_filter_lt_eq_sum_range k (fun n ↦ (dvec φ h n ⬝ᵥ ev w) ^ 2)]
  refine sum_congr rfl fun j _ ↦ ?_
  rw [dvec_val, ev_dot]

/-- `pairDisp ≤ (wᵀ V_k w) · u_k` (L10 summed). -/
theorem pairDisp_le_gram_mul (hρ : ∀ x, 0 ≤ ρ x) (href : IsPositivePolicy π_ref) {T : ℕ}
    (h : Fin T → X × Y × Y × Bool) (k : Fin T) (θ : EuclideanSpace ℝ (Fin d)) :
    pairDisp ρ (roundPolicy π_ref φ β sel h k)
        (fun x y ↦ linReward φ θ x y - linReward φ θstar x y) ≤
      ev (θ - θstar) ⬝ᵥ (gramMat (dvec φ h) k *ᵥ ev (θ - θstar)) *
        uStat ρ π_ref φ β sel h k := by
  set G := ev (θ - θstar) ⬝ᵥ (gramMat (dvec φ h) k *ᵥ ev (θ - θstar))
  unfold pairDisp uStat
  rw [mul_sum]
  refine sum_le_sum fun x _ ↦ ?_
  rw [mul_left_comm]
  refine mul_le_mul_of_nonneg_left ?_ (hρ x)
  rw [mul_sum]
  refine sum_le_sum fun y1 _ ↦ ?_
  rw [mul_sum]
  refine sum_le_sum fun y2 _ ↦ ?_
  have hp := gibbsPolicy_pos href (linReward φ (sel (vpoData h k))) β x
  have hw : 0 ≤ roundPolicy π_ref φ β sel h k x y1 * roundPolicy π_ref φ β sel h k x y2 :=
    mul_nonneg (hp y1).le (hp y2).le
  have hdiff : linReward φ θ x y1 - linReward φ θstar x y1 -
      (linReward φ θ x y2 - linReward φ θstar x y2) =
      ev (φ x y1 - φ x y2) ⬝ᵥ ev (θ - θstar) := by
    rw [ev_dot, linReward_sub, linReward_sub, ← linReward_diff]
  rw [hdiff]
  have hcs := dot_sq_le_invNormSq_mul (dvec φ h) k (ev (φ x y1 - φ x y2)) (ev (θ - θstar))
  calc _ ≤ roundPolicy π_ref φ β sel h k x y1 * roundPolicy π_ref φ β sel h k x y2 *
        (invNormSq (gramMat (dvec φ h) k) (ev (φ x y1 - φ x y2)) * G) :=
        mul_le_mul_of_nonneg_left hcs hw
    _ = _ := by ring

variable {ρ π_ref π_cal φ θstar α β R sel}

/-- Common facts for round `k`. -/
theorem round_setup (hρ : ∀ x, 0 ≤ ρ x) (href : IsPositivePolicy π_ref)
    (hcal : IsCondPolicy π_cal) (hφ : ∀ x y, ‖φ x y‖ ≤ 1) (hθs : ‖θstar‖ ≤ R) (hβ : 0 < β)
    (hsel : IsBallSelection ρ π_ref π_cal φ α β R sel) {T : ℕ} (h : Fin T → X × Y × Y × Bool)
    (k : Fin T) :
    let θ := sel (vpoData h k)
    ‖θ‖ ≤ R ∧
    nll (linReward φ θ) (vpoData h k) - α * optClosed ρ π_ref π_cal β (linReward φ θ) ≤
      nll (linReward φ θstar) (vpoData h k) -
        α * optClosed ρ π_ref π_cal β (linReward φ θstar) ∧
    (∀ x y, |linReward φ θ x y - linReward φ θstar x y| ≤ 2 * R) ∧
    optCalValue ρ π_ref π_cal β (linReward φ θstar) -
        calValue ρ π_ref π_cal β (linReward φ θstar) (roundPolicy π_ref φ β sel h k) =
      optClosed ρ π_ref π_cal β (linReward φ θstar) -
        calValue ρ π_ref π_cal β (linReward φ θstar) (roundPolicy π_ref φ β sel h k) ∧
    calValue ρ π_ref π_cal β (linReward φ θ) (roundPolicy π_ref φ β sel h k) =
      optClosed ρ π_ref π_cal β (linReward φ θ) := by
  intro θ
  have hθ : ‖θ‖ ≤ R := (hsel (vpoData h k)).1
  refine ⟨hθ, ?_, ?_, ?_, ?_⟩
  · have hopt := (hsel (vpoData h k)).2 θstar hθs
    rwa [vpoObjective_gibbs ρ href π_cal hcal.2 α hβ,
      vpoObjective_gibbs ρ href π_cal hcal.2 α hβ] at hopt
  · intro x y
    rw [linReward_sub]
    refine le_trans (linReward_abs_le φ hφ _ x y) ?_
    linarith [norm_sub_le θ θstar]
  · rw [optCalValue_eq ρ hρ href π_cal hβ]
  · exact calValue_gibbs ρ href π_cal hβ _

/-- Per-round bound (on `E₁` at this round). -/
theorem round_bound_kappa (hρ : ∀ x, 0 ≤ ρ x) (hρ1 : ∑ x, ρ x = 1)
    (href : IsPositivePolicy π_ref) (hcal : IsCondPolicy π_cal) (hφ : ∀ x y, ‖φ x y‖ ≤ 1)
    (hR : 0 < R) (hθs : ‖θstar‖ ≤ R) (hα : 0 < α) (hβ : 0 < β)
    (hsel : IsBallSelection ρ π_ref π_cal φ α β R sel) {T : ℕ} (h : Fin T → X × Y × Y × Bool)
    (k : Fin T) {B : ℝ}
    (hE1 : nll (linReward φ θstar) (vpoData h k) - nll (linReward φ (sel (vpoData h k)))
        (vpoData h k) ≤ B - cH R * ∑ j ∈ univ.filter (fun j ↦ j < k),
          inner ℝ (dz φ (h j)) (sel (vpoData h k) - θstar) ^ 2) :
    optCalValue ρ π_ref π_cal β (linReward φ θstar) -
        calValue ρ π_ref π_cal β (linReward φ θstar) (roundPolicy π_ref φ β sel h k) ≤
      (B + 1) / α + 2 * vpoKappa π_ref π_cal * exp (4 * R + 2 * R / β) * α *
        uStat ρ π_ref φ β sel h k := by
  obtain ⟨hθ, hopt, hg, hreg, hJ⟩ := round_setup hρ href hcal hφ hθs hβ hsel h k
  set θ := sel (vpoData h k)
  set pol := roundPolicy π_ref φ β sel h k
  have hpol : IsCondPolicy pol := gibbsPolicy_isCondPolicy href _ β
  set S := ∑ j ∈ univ.filter (fun j ↦ j < k), inner ℝ (dz φ (h j)) (θ - θstar) ^ 2
  set G := ev (θ - θstar) ⬝ᵥ (gramMat (dvec φ h) k *ᵥ ev (θ - θstar))
  set u := uStat ρ π_ref φ β sel h k
  have hu : 0 ≤ u := uStat_nonneg ρ π_ref φ β sel hρ href h k
  have hGeq : G = 4 * ‖θ - θstar‖ ^ 2 + S := gram_quad_eq φ h k (θ - θstar)
  have hG0 : 0 ≤ G := by rw [hGeq]; positivity
  have hw : ‖θ - θstar‖ ≤ 2 * R := by linarith [norm_sub_le θ θstar]
  have hGle : G ≤ 16 * R ^ 2 + S := by
    rw [hGeq]; nlinarith [norm_nonneg (θ - θstar)]
  have hD := pairDisp_le_gram_mul ρ π_ref φ θstar β sel hρ href h k θ
  set κ := vpoKappa π_ref π_cal
  obtain ⟨x₀, -⟩ : (univ : Finset X).Nonempty := by
    by_contra hX; rw [not_nonempty_iff_eq_empty.1 hX, sum_empty] at hρ1; exact zero_ne_one hρ1
  obtain ⟨y₀, -⟩ := univ_nonempty_of_pos href x₀
  have hκ := vpoKappa_nonneg π_ref π_cal href hcal x₀ y₀
  set K₀ := κ * exp (2 * R / β)
  have hK₀ : 0 ≤ K₀ := by positivity
  have hcalK : ∀ x y, π_cal x y ≤ K₀ * pol x y := by
    intro x y
    have h1 := vpoKappa_bound π_ref π_cal href x y
    have h2 := (gibbs_ratio_bounds href (linReward φ θ) hβ x
      (fun y ↦ le_trans (linReward_abs_le φ hφ θ x y) hθ) y).1
    calc π_cal x y ≤ κ * π_ref x y := h1
      _ ≤ κ * (exp (2 * R / β) * gibbsPolicy π_ref (linReward φ θ) β x y) :=
          mul_le_mul_of_nonneg_left h2 hκ
      _ = K₀ * pol x y := by simp only [K₀, pol, roundPolicy]; ring
  have hΔsq := calValue_sub_sq_le ρ hρ hρ1 π_ref π_cal
    hcal β (linReward φ θ) (linReward φ θstar) pol hpol K₀ hcalK
  set Δ := calValue ρ π_ref π_cal β (linReward φ θ) pol -
    calValue ρ π_ref π_cal β (linReward φ θstar) pol
  have hΔsq' : Δ ^ 2 ≤ K₀ / 2 * G * u := by
    calc Δ ^ 2 ≤ K₀ / 2 * pairDisp ρ pol (fun x y ↦ linReward φ θ x y - linReward φ θstar x y) :=
          hΔsq
      _ ≤ K₀ / 2 * (G * u) := mul_le_mul_of_nonneg_left hD (by positivity)
      _ = _ := by ring
  have hcH : 0 < cH R := by unfold cH; positivity
  have hε : 0 < cH R / α := div_pos hcH hα
  have hΔ := le_of_sq_le_mul (by positivity) hG0 hu hε hΔsq'
  have hKeq : K₀ / 2 / (4 * (cH R / α)) = 2 * κ * exp (4 * R + 2 * R / β) * α := by
    simp only [K₀, cH]
    rw [exp_add]
    field_simp
    ring
  rw [hKeq] at hΔ
  -- optimism + E₁
  have hJdiff : optClosed ρ π_ref π_cal β (linReward φ θstar) -
      optClosed ρ π_ref π_cal β (linReward φ θ) ≤ (B - cH R * S) / α := by
    rw [le_div_iff₀ hα]
    have := hE1
    linarith
  have h16 : cH R * (16 * R ^ 2) ≤ 1 := by
    unfold cH
    rw [div_mul_eq_mul_div, one_mul, div_le_one (by positivity)]
    linarith [sq_le_exp hR.le]
  have hGα : cH R / α * G ≤ cH R / α * (16 * R ^ 2 + S) :=
    mul_le_mul_of_nonneg_left hGle hε.le
  have hsum : (B - cH R * S) / α + cH R / α * (16 * R ^ 2 + S) = (B + cH R * (16 * R ^ 2)) / α := by
    field_simp; ring
  have hfin : (B + cH R * (16 * R ^ 2)) / α ≤ (B + 1) / α :=
    div_le_div_of_nonneg_right (by linarith) hα.le
  rw [hreg]
  have : optClosed ρ π_ref π_cal β (linReward φ θstar) -
      calValue ρ π_ref π_cal β (linReward φ θstar) pol =
      (optClosed ρ π_ref π_cal β (linReward φ θstar) -
        optClosed ρ π_ref π_cal β (linReward φ θ)) + Δ := by
    simp only [Δ]; rw [hJ]; ring
  rw [this]
  linarith

/-- Per-round local-curvature bound (local-curvature argument, on `E₁` at this round). -/
theorem round_bound_local (hρ : ∀ x, 0 ≤ ρ x) (hρ1 : ∑ x, ρ x = 1)
    (href : IsPositivePolicy π_ref) (hcal : IsCondPolicy π_cal) (hφ : ∀ x y, ‖φ x y‖ ≤ 1)
    (hR : 0 < R) (hθs : ‖θstar‖ ≤ R) (hα : 0 < α) (hβ : 0 < β)
    (hsel : IsBallSelection ρ π_ref π_cal φ α β R sel) {T : ℕ} (h : Fin T → X × Y × Y × Bool)
    (k : Fin T) {B : ℝ}
    (hE1 : nll (linReward φ θstar) (vpoData h k) - nll (linReward φ (sel (vpoData h k)))
        (vpoData h k) ≤ B - cH R * ∑ j ∈ univ.filter (fun j ↦ j < k),
          inner ℝ (dz φ (h j)) (sel (vpoData h k) - θstar) ^ 2) :
    optCalValue ρ π_ref π_cal β (linReward φ θstar) -
        calValue ρ π_ref π_cal β (linReward φ θstar) (roundPolicy π_ref φ β sel h k) ≤
      exp (4 * R / β) / (4 * β) *
        (16 * R ^ 2 + 16 * exp (4 * R) * (B + 1 + 4 * R * α)) * uStat ρ π_ref φ β sel h k := by
  obtain ⟨hθ, hopt, hg, hreg, hJ⟩ := round_setup hρ href hcal hφ hθs hβ hsel h k
  set θ := sel (vpoData h k)
  set pol := roundPolicy π_ref φ β sel h k
  have hpol : IsCondPolicy pol := gibbsPolicy_isCondPolicy href _ β
  set S := ∑ j ∈ univ.filter (fun j ↦ j < k), inner ℝ (dz φ (h j)) (θ - θstar) ^ 2
  set G := ev (θ - θstar) ⬝ᵥ (gramMat (dvec φ h) k *ᵥ ev (θ - θstar))
  set u := uStat ρ π_ref φ β sel h k
  have hu : 0 ≤ u := uStat_nonneg ρ π_ref φ β sel hρ href h k
  have hGeq : G = 4 * ‖θ - θstar‖ ^ 2 + S := gram_quad_eq φ h k (θ - θstar)
  have hw : ‖θ - θstar‖ ≤ 2 * R := by linarith [norm_sub_le θ θstar]
  have hGle : G ≤ 16 * R ^ 2 + S := by
    rw [hGeq]; nlinarith [norm_nonneg (θ - θstar)]
  have hD := pairDisp_le_gram_mul ρ π_ref φ θstar β sel hρ href h k θ
  -- per-round regret ≤ C · pairDisp
  have hloc := optClosed_sub_calValue_le ρ hρ href π_cal hβ (linReward φ θ) (linReward φ θstar) hg
  have hexp : exp (2 * (2 * R) / β) = exp (4 * R / β) := by ring_nf
  rw [hexp] at hloc
  -- `optClosed r_θ − optClosed r⋆ ≤ 4R`
  have hgap : optClosed ρ π_ref π_cal β (linReward φ θ) -
      optClosed ρ π_ref π_cal β (linReward φ θstar) ≤ 2 * (2 * R) := by
    have h1 := calValue_le_optClosed ρ hρ href π_cal hβ (linReward φ θstar) pol hpol
    have h2 := calValue_sub_le ρ hρ hρ1 π_ref π_cal hcal β
      (linReward φ θ) (linReward φ θstar) pol hpol hg
    rw [hJ] at h2
    linarith
  have hcH : 0 < cH R := by unfold cH; positivity
  have hS : cH R * S ≤ B + 4 * R * α := by
    have := mul_le_mul_of_nonneg_left hgap hα.le
    linarith
  have hS' : S ≤ 16 * exp (4 * R) * (B + 4 * R * α) := by
    unfold cH at hS
    rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)] at hS
    linarith
  have hGmax : G ≤ 16 * R ^ 2 + 16 * exp (4 * R) * (B + 1 + 4 * R * α) := by
    have : 16 * exp (4 * R) * (B + 4 * R * α) ≤ 16 * exp (4 * R) * (B + 1 + 4 * R * α) := by
      have := exp_pos (4 * R); nlinarith
    linarith
  have hC : 0 ≤ exp (4 * R / β) / (4 * β) := by positivity
  rw [hreg]
  calc _ ≤ exp (4 * R / β) / (4 * β) *
        pairDisp ρ pol (fun x y ↦ linReward φ θ x y - linReward φ θstar x y) := hloc
    _ ≤ exp (4 * R / β) / (4 * β) * (G * u) := mul_le_mul_of_nonneg_left hD hC
    _ ≤ exp (4 * R / β) / (4 * β) *
        ((16 * R ^ 2 + 16 * exp (4 * R) * (B + 1 + 4 * R * α)) * u) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hGmax hu) hC
    _ = _ := by ring

end Round

end StatisticalRL.Ch7Rest.Rlhf
