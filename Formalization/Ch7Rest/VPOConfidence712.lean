import Formalization.Ch7Rest.VPOTraj712
import Formalization.Ch7Rest.VPOGrid712

/-!
# Corrected Theorem 7.12: likelihood confidence event E₁

Event E₁. For a fixed parameter `θ'` and round `k`, the product of the
likelihood-ratio factors `√(p_{θ'}/p⋆)/BC` over the rounds `j < k` has conditional mean one, so by
the adaptive product lemma it exceeds `L` with probability at most `1/L`. Off this event,
`ℓ_k(θ⋆) − ℓ_k(θ') ≤ 2 log L − c_H ∑_{j<k} ⟪d_j, θ' − θ⋆⟫²` with `c_H = 1/(16 e^{4R})`. A union
over the rounds and the grid cells, and the Lipschitz transfer, give the uniform event.
-/

namespace StatisticalRL.Ch7Rest.Rlhf

open Finset Real

set_option linter.unusedSectionVars false

variable {X Y : Type} [Fintype X] [Fintype Y] {d : ℕ}

/-- Unordered feature difference `φ(x,y₁) − φ(x,y₂)` of a round outcome. -/
noncomputable def dz (φ : X → Y → EuclideanSpace ℝ (Fin d)) (ω : X × Y × Y × Bool) :
    EuclideanSpace ℝ (Fin d) :=
  φ ω.1 ω.2.1 - φ ω.1 ω.2.2.1

/-- Bhattacharyya coefficient of the two Bradley–Terry laws at the pair `(x, y₁, y₂)` of `ω`. -/
noncomputable def bcoef (r' r : X → Y → ℝ) (ω : X × Y × Y × Bool) : ℝ :=
  √(prefProb r' (ω.1, ω.2.1, ω.2.2.1, true) * prefProb r (ω.1, ω.2.1, ω.2.2.1, true)) +
    √(prefProb r' (ω.1, ω.2.1, ω.2.2.1, false) * prefProb r (ω.1, ω.2.1, ω.2.2.1, false))

/-- Likelihood-ratio factor `√(p'(ω) p(ω)) / (p(ω) · BC)`. -/
noncomputable def lrFac (r' r : X → Y → ℝ) (ω : X × Y × Y × Bool) : ℝ :=
  √(prefProb r' ω * prefProb r ω) / (prefProb r ω * bcoef r' r ω)

/-- `c_H = 1/(16 e^{4R})`. -/
noncomputable def cH (R : ℝ) : ℝ := 1 / (16 * exp (4 * R))

theorem bcoef_pos (r' r : X → Y → ℝ) (ω : X × Y × Y × Bool) : 0 < bcoef r' r ω := by
  unfold bcoef
  have := sqrt_pos.2 (mul_pos (prefProb_pos r' (ω.1, ω.2.1, ω.2.2.1, true))
    (prefProb_pos r (ω.1, ω.2.1, ω.2.2.1, true)))
  positivity

theorem lrFac_nonneg (r' r : X → Y → ℝ) (ω : X × Y × Y × Bool) : 0 ≤ lrFac r' r ω :=
  div_nonneg (sqrt_nonneg _) (mul_pos (prefProb_pos _ _) (bcoef_pos _ _ _)).le

theorem lrFac_mean (r' r : X → Y → ℝ) (x : X) (y1 y2 : Y) :
    prefProb r (x, y1, y2, true) * lrFac r' r (x, y1, y2, true) +
      prefProb r (x, y1, y2, false) * lrFac r' r (x, y1, y2, false) = 1 := by
  unfold lrFac
  have hb := bcoef_pos r' r (x, y1, y2, true)
  have hbf : bcoef r' r (x, y1, y2, false) = bcoef r' r (x, y1, y2, true) := rfl
  rw [hbf]
  have h1 := prefProb_pos r (x, y1, y2, true)
  have h2 := prefProb_pos r (x, y1, y2, false)
  field_simp
  unfold bcoef
  ring_nf

theorem log_lrFac (r' r : X → Y → ℝ) (ω : X × Y × Y × Bool) :
    log (lrFac r' r ω) =
      (log (prefProb r' ω) - log (prefProb r ω)) / 2 - log (bcoef r' r ω) := by
  unfold lrFac
  have h1 := prefProb_pos r' ω
  have h2 := prefProb_pos r ω
  have h3 := bcoef_pos r' r ω
  rw [log_div (sqrt_pos.2 (mul_pos h1 h2)).ne' (mul_pos h2 h3).ne', log_sqrt (mul_pos h1 h2).le,
    log_mul h1.ne' h2.ne', log_mul h2.ne' h3.ne']
  ring

theorem inner_sub_bound (φ : X → Y → EuclideanSpace ℝ (Fin d)) (hφ : ∀ x y, ‖φ x y‖ ≤ 1)
    (x : X) (y1 y2 : Y) (w : EuclideanSpace ℝ (Fin d)) :
    |inner ℝ (φ x y1 - φ x y2) w| ≤ 2 * ‖w‖ := by
  refine le_trans (abs_real_inner_le_norm _ _) ?_
  have : ‖φ x y1 - φ x y2‖ ≤ 2 := le_trans (norm_sub_le _ _) (by linarith [hφ x y1, hφ x y2])
  exact mul_le_mul_of_nonneg_right this (norm_nonneg _)

theorem linReward_diff (φ : X → Y → EuclideanSpace ℝ (Fin d)) (θ : EuclideanSpace ℝ (Fin d))
    (x : X) (y1 y2 : Y) :
    linReward φ θ x y1 - linReward φ θ x y2 = inner ℝ (φ x y1 - φ x y2) θ := by
  unfold linReward; rw [inner_sub_left]

/-- Hellinger lower bound: `−log BC ≥ c_H/2 · ⟪d, θ' − θ⋆⟫²` for `θ', θ⋆` in the ball. -/
theorem neg_log_bcoef_ge (φ : X → Y → EuclideanSpace ℝ (Fin d)) (hφ : ∀ x y, ‖φ x y‖ ≤ 1)
    {R : ℝ} (hR : 0 ≤ R) (θ' θstar : EuclideanSpace ℝ (Fin d)) (hθ' : ‖θ'‖ ≤ R)
    (hθs : ‖θstar‖ ≤ R) (ω : X × Y × Y × Bool) :
    cH R / 2 * inner ℝ (dz φ ω) (θ' - θstar) ^ 2 ≤
      -log (bcoef (linReward φ θ') (linReward φ θstar) ω) := by
  obtain ⟨x, y1, y2, o⟩ := ω
  set a' := linReward φ θ' x y1 - linReward φ θ' x y2
  set a := linReward φ θstar x y1 - linReward φ θstar x y2
  have ha' : |a'| ≤ 2 * R := by
    show |linReward φ θ' x y1 - linReward φ θ' x y2| ≤ 2 * R
    rw [linReward_diff]; exact le_trans (inner_sub_bound φ hφ x y1 y2 θ') (by linarith)
  have ha : |a| ≤ 2 * R := by
    show |linReward φ θstar x y1 - linReward φ θstar x y2| ≤ 2 * R
    rw [linReward_diff]; exact le_trans (inner_sub_bound φ hφ x y1 y2 θstar) (by linarith)
  have hdiff : a' - a = inner ℝ (dz φ (x, y1, y2, o)) (θ' - θstar) := by
    simp only [a', a, linReward_diff, dz, inner_sub_right]
  have hbc : bcoef (linReward φ θ') (linReward φ θstar) (x, y1, y2, o) =
      √(sigmoid a') * √(sigmoid a) + √(1 - sigmoid a') * √(1 - sigmoid a) := by
    unfold bcoef
    simp only [prefProb_true, prefProb_false]
    rw [sqrt_mul (sigmoid_pos _).le, sqrt_mul (by linarith [sigmoid_lt_one a'])]
  have hL6 := sq_sub_le_two_hellinger (sigmoid_pos a').le (sigmoid_le_one a')
    (sigmoid_pos a).le (sigmoid_le_one a)
  have hL7 := sq_sub_le_sigmoid (by linarith : (0 : ℝ) ≤ 2 * R) ha' ha
  have hbpos := bcoef_pos (linReward φ θ') (linReward φ θstar) (x, y1, y2, o)
  have hlog := log_le_sub_one_of_pos hbpos
  rw [hbc] at hlog hbpos
  rw [hbc, ← hdiff]
  have hE : 0 < exp (2 * (2 * R)) := exp_pos _
  have h4 : exp (4 * R) = exp (2 * (2 * R)) := by ring_nf
  unfold cH
  rw [h4]
  have : (a' - a) ^ 2 / (16 * exp (2 * (2 * R))) ≤ (sigmoid a' - sigmoid a) ^ 2 := by
    rw [div_le_iff₀ (by positivity)]; linarith
  have hfin : 1 / (16 * exp (2 * (2 * R))) / 2 * (a' - a) ^ 2 =
      (a' - a) ^ 2 / (16 * exp (2 * (2 * R))) / 2 := by ring
  rw [hfin]
  linarith

section Event

variable (ρ : X → ℝ) (π_ref : X → Y → ℝ) (φ : X → Y → EuclideanSpace ℝ (Fin d))
  (θstar : EuclideanSpace ℝ (Fin d)) (β : ℝ) (sel : List (X × Y × Y) → EuclideanSpace ℝ (Fin d))

/-- E₁ for one round `k` and one parameter `θ'`: `P(L ≤ ∏_{j<k} LR_j) ≤ 1/L`. -/
theorem e1_single (hρ : ∀ x, 0 ≤ ρ x) (hρ1 : ∑ x, ρ x = 1) (href : IsPositivePolicy π_ref)
    {T : ℕ} (θ' : EuclideanSpace ℝ (Fin d)) (k : Fin T) {L : ℝ} (hL : 0 < L) :
    ∑ h : Fin T → X × Y × Y × Bool, vpoTrajWeight ρ π_ref φ θstar β sel h *
      (if L ≤ ∏ j, (if j < k then lrFac (linReward φ θ') (linReward φ θstar) (h j) else 1)
        then 1 else 0) ≤ 1 / L := by
  refine adaptive_markov T (fun j h ω ↦ roundKernel ρ π_ref φ θstar β sel j h ω)
    (fun j h ↦ if j < k then lrFac (linReward φ θ') (linReward φ θstar) (h j) else 1)
    (fun j h ω ↦ roundKernel_nonneg ρ π_ref φ θstar β sel hρ href j h ω)
    (fun j h h' hag ↦ roundKernel_congr ρ π_ref φ θstar β sel j h h' hag)
    (fun j h ↦ by dsimp only; split_ifs; exact lrFac_nonneg _ _ _; norm_num)
    (fun j h h' hag ↦ by dsimp only; rw [hag j le_rfl])
    (fun j h ↦ ?_) hL
  dsimp only
  simp only [Function.update_self]
  split_ifs with hjk
  · rw [roundKernel_sum_mul]
    simp only [lrFac_mean, mul_one]
    have hp := gibbsPolicy_sum href (linReward φ (sel (vpoData h j))) β
    simp only [roundPolicy, ← mul_sum, hp, mul_one, hρ1, le_refl]
  · simp only [mul_one]
    rw [roundKernel_sum ρ π_ref φ θstar β sel hρ1 href j h]

/-- Deterministic consequence off the E₁ event for `(k, θ')`. -/
theorem e1_consequence (hφ : ∀ x y, ‖φ x y‖ ≤ 1) {R : ℝ} (hR : 0 ≤ R)
    (θ' : EuclideanSpace ℝ (Fin d)) (hθ' : ‖θ'‖ ≤ R) (hθs : ‖θstar‖ ≤ R) {T : ℕ}
    (h : Fin T → X × Y × Y × Bool) (k : Fin T) {L : ℝ}
    (hlt : ¬ L ≤ ∏ j, (if j < k then lrFac (linReward φ θ') (linReward φ θstar) (h j) else 1)) :
    nll (linReward φ θstar) (vpoData h k) - nll (linReward φ θ') (vpoData h k) ≤
      2 * log L - cH R * ∑ j ∈ univ.filter (fun j ↦ j < k),
        inner ℝ (dz φ (h j)) (θ' - θstar) ^ 2 := by
  push_neg at hlt
  rw [← prod_filter] at hlt
  set s := univ.filter (fun j : Fin T ↦ j < k)
  have hpos : ∀ j ∈ s, 0 < lrFac (linReward φ θ') (linReward φ θstar) (h j) := by
    intro j _
    unfold lrFac
    exact div_pos (sqrt_pos.2 (mul_pos (prefProb_pos _ _) (prefProb_pos _ _)))
      (mul_pos (prefProb_pos _ _) (bcoef_pos _ _ _))
  have hprod_pos := prod_pos hpos
  have hlog := log_lt_log hprod_pos hlt
  rw [log_prod (fun j hj ↦ (hpos j hj).ne')] at hlog
  simp only [log_lrFac] at hlog
  rw [nll_vpoData, nll_vpoData]
  have hH : ∀ j ∈ s, cH R / 2 * inner ℝ (dz φ (h j)) (θ' - θstar) ^ 2 ≤
      -log (bcoef (linReward φ θ') (linReward φ θstar) (h j)) :=
    fun j _ ↦ neg_log_bcoef_ge φ hφ hR θ' θstar hθ' hθs (h j)
  have hHs := sum_le_sum hH
  rw [← mul_sum, sum_neg_distrib] at hHs
  rw [sum_sub_distrib, ← sum_div, sum_sub_distrib] at hlog
  rw [mul_sum] at hHs ⊢
  rw [← mul_sum] at hHs ⊢
  linarith

/-- Lipschitz transfer of the negative log-likelihood (`log σ` is 1-Lipschitz). -/
theorem nll_transfer (hφ : ∀ x y, ‖φ x y‖ ≤ 1) {T : ℕ} (hT : 1 ≤ T)
    (θ θ' : EuclideanSpace ℝ (Fin d)) (hθθ' : ‖θ - θ'‖ ≤ 1 / T)
    (h : Fin T → X × Y × Y × Bool) (k : Fin T) :
    nll (linReward φ θ') (vpoData h k) - nll (linReward φ θ) (vpoData h k) ≤ 2 := by
  rw [nll_vpoData, nll_vpoData]
  have hT0 : (0 : ℝ) < T := by exact_mod_cast hT
  have hterm : ∀ j, log (prefProb (linReward φ θ) (h j)) -
      log (prefProb (linReward φ θ') (h j)) ≤ 2 / T := by
    intro j
    unfold prefProb
    refine le_trans (le_abs_self _) (le_trans (abs_log_sigmoid_sub_le _ _) ?_)
    rw [linReward_diff, linReward_diff, ← inner_sub_right]
    refine le_trans (inner_sub_bound φ hφ _ _ _ _) ?_
    calc 2 * ‖θ - θ'‖ ≤ 2 * (1 / T) := by linarith
      _ = 2 / T := by ring
  have hcard : ((univ.filter (fun j : Fin T ↦ j < k)).card : ℝ) ≤ T := by
    have := card_filter_le (univ : Finset (Fin T)) (fun j ↦ j < k)
    rw [card_univ, Fintype.card_fin] at this
    exact_mod_cast this
  have := sum_le_sum fun j (_ : j ∈ univ.filter (fun j : Fin T ↦ j < k)) ↦ hterm j
  rw [sum_sub_distrib, sum_const, nsmul_eq_mul] at this
  have h2 : ((univ.filter (fun j : Fin T ↦ j < k)).card : ℝ) * (2 / T) ≤ 2 := by
    rw [mul_div_assoc', div_le_iff₀ hT0]; linarith
  linarith

/-- Transfer of the Hellinger penalty: `|∑ ⟪d_j, θ'−θ⋆⟫² − ∑ ⟪d_j, θ−θ⋆⟫²| ≤ 16 R`. -/
theorem penalty_transfer (hφ : ∀ x y, ‖φ x y‖ ≤ 1) {R : ℝ} {T : ℕ} (hT : 1 ≤ T)
    (θ θ' : EuclideanSpace ℝ (Fin d)) (hθ : ‖θ‖ ≤ R) (hθ' : ‖θ'‖ ≤ R) (hθs : ‖θstar‖ ≤ R)
    (hθθ' : ‖θ - θ'‖ ≤ 1 / T) (h : Fin T → X × Y × Y × Bool) (k : Fin T) :
    ∑ j ∈ univ.filter (fun j ↦ j < k), inner ℝ (dz φ (h j)) (θ - θstar) ^ 2 ≤
      ∑ j ∈ univ.filter (fun j ↦ j < k), inner ℝ (dz φ (h j)) (θ' - θstar) ^ 2 + 16 * R := by
  have hT0 : (0 : ℝ) < T := by exact_mod_cast hT
  have hR : 0 ≤ R := le_trans (norm_nonneg _) hθ
  have hterm : ∀ j, inner ℝ (dz φ (h j)) (θ - θstar) ^ 2 -
      inner ℝ (dz φ (h j)) (θ' - θstar) ^ 2 ≤ 16 * R / T := by
    intro j
    set A := inner ℝ (dz φ (h j)) (θ - θstar)
    set B := inner ℝ (dz φ (h j)) (θ' - θstar)
    have hA : |A| ≤ 4 * R := by
      refine le_trans (inner_sub_bound φ hφ _ _ _ _) ?_
      have := norm_sub_le θ θstar; linarith
    have hB : |B| ≤ 4 * R := by
      refine le_trans (inner_sub_bound φ hφ _ _ _ _) ?_
      have := norm_sub_le θ' θstar; linarith
    have hAB : |A - B| ≤ 2 / T := by
      have : A - B = inner ℝ (dz φ (h j)) (θ - θ') := by
        simp only [A, B, ← inner_sub_right]; congr 1; abel
      rw [this]
      refine le_trans (inner_sub_bound φ hφ _ _ _ _) ?_
      calc 2 * ‖θ - θ'‖ ≤ 2 * (1 / T) := by linarith
        _ = 2 / T := by ring
    have : A ^ 2 - B ^ 2 = (A - B) * (A + B) := by ring
    rw [this]
    calc (A - B) * (A + B) ≤ |A - B| * |A + B| := by rw [← abs_mul]; exact le_abs_self _
      _ ≤ (2 / T) * (8 * R) := by
          refine mul_le_mul hAB (le_trans (abs_add_le _ _) (by linarith)) (abs_nonneg _)
            (by positivity)
      _ = 16 * R / T := by ring
  have hcard : ((univ.filter (fun j : Fin T ↦ j < k)).card : ℝ) ≤ T := by
    have := card_filter_le (univ : Finset (Fin T)) (fun j ↦ j < k)
    rw [card_univ, Fintype.card_fin] at this
    exact_mod_cast this
  have := sum_le_sum fun j (_ : j ∈ univ.filter (fun j : Fin T ↦ j < k)) ↦ hterm j
  rw [sum_sub_distrib, sum_const, nsmul_eq_mul] at this
  have h2 : ((univ.filter (fun j : Fin T ↦ j < k)).card : ℝ) * (16 * R / T) ≤ 16 * R := by
    rw [mul_div_assoc', div_le_iff₀ hT0]; nlinarith
  linarith

theorem R_mul_exp_le {R : ℝ} (hR : 0 ≤ R) : R ≤ exp (4 * R) := by
  linarith [add_one_le_exp (4 * R)]

theorem sq_le_exp {R : ℝ} (hR : 0 ≤ R) : R ^ 2 ≤ exp (4 * R) := by
  have h1 : R ≤ exp (2 * R) := by linarith [add_one_le_exp (2 * R)]
  have h2 : exp (4 * R) = exp (2 * R) ^ 2 := by rw [← exp_nat_mul]; ring_nf
  rw [h2]
  exact pow_le_pow_left₀ hR h1 2

/-- The uniform E₁ event fails with probability at most `δ/2`, and off it the confidence bound
holds for every `θ` in the ball and every round. -/
theorem e1_uniform (hρ : ∀ x, 0 ≤ ρ x) (hρ1 : ∑ x, ρ x = 1) (href : IsPositivePolicy π_ref)
    (hφ : ∀ x y, ‖φ x y‖ ≤ 1) {R δ : ℝ} (hR : 0 < R) (hθs : ‖θstar‖ ≤ R) (hδ : 0 < δ)
    {T : ℕ} (hT : 1 ≤ T) (hd : 0 < d) :
    ∃ bad1 : (Fin T → X × Y × Y × Bool) → Prop,
      (∑ h, vpoTrajWeight ρ π_ref φ θstar β sel h * (open Classical in if bad1 h then 1 else 0) ≤
        δ / 2) ∧
      ∀ h, ¬ bad1 h → ∀ (k : Fin T) (θ : EuclideanSpace ℝ (Fin d)), ‖θ‖ ≤ R →
        nll (linReward φ θstar) (vpoData h k) - nll (linReward φ θ) (vpoData h k) ≤
          2 * log (2 * T / δ) + 2 * d * log (gridM R T d) + 3 -
            cH R * ∑ j ∈ univ.filter (fun j ↦ j < k), inner ℝ (dz φ (h j)) (θ - θstar) ^ 2 := by
  classical
  set M := gridM R T d
  have hM := one_le_gridM hR hT hd
  have hMR : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hT0 : (0 : ℝ) < T := by exact_mod_cast hT
  set N : ℝ := (M : ℝ) ^ d
  have hN : 0 < N := by positivity
  set L : ℝ := 2 * T * N / δ
  have hL : 0 < L := by positivity
  let rep := gridRep (d := d) R M hM
  let bad1 : (Fin T → X × Y × Y × Bool) → Prop := fun h ↦
    ∃ p ∈ (univ : Finset (Fin T × (Fin d → Fin M))),
      L ≤ ∏ j, (if j < p.1 then lrFac (linReward φ (rep p.2)) (linReward φ θstar) (h j) else 1)
  refine ⟨bad1, ?_, ?_⟩
  · have hu := @union_bound_sum _ _ _ (fun h ↦ vpoTrajWeight ρ π_ref φ θstar β sel h)
      (fun h ↦ vpoTrajWeight_nonneg ρ π_ref φ θstar β sel hρ href h) univ
      (fun (p : Fin T × (Fin d → Fin M)) h ↦
        L ≤ ∏ j, (if j < p.1 then lrFac (linReward φ (rep p.2)) (linReward φ θstar) (h j) else 1))
      (fun _ _ ↦ Classical.propDecidable _) (fun _ ↦ Classical.propDecidable _)
    refine le_trans (le_of_eq rfl) (le_trans hu ?_)
    calc _ ≤ ∑ _p ∈ (univ : Finset (Fin T × (Fin d → Fin M))), 1 / L :=
            sum_le_sum fun p _ ↦ e1_single ρ π_ref φ θstar β sel hρ hρ1 href (rep p.2) p.1 hL
        _ = δ / 2 := by
            rw [sum_const, card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_fun,
              Fintype.card_fin, Fintype.card_fin, nsmul_eq_mul]
            simp only [L, N]
            push_cast
            field_simp
  · intro h hgood k θ hθ
    set c := gridCell R M hM θ
    set θ' := rep c
    have hθ' : ‖θ'‖ ≤ R := gridRep_norm_le hR.le hM c
    have hcl : ‖θ - θ'‖ ≤ 1 / T := gridRep_cover hR hT hd θ hθ
    have hnot : ¬ L ≤ ∏ j, (if j < k then lrFac (linReward φ θ') (linReward φ θstar) (h j) else 1) :=
      fun hle ↦ hgood ⟨(k, c), mem_univ _, hle⟩
    have h1 := e1_consequence φ θstar hφ hR.le θ' hθ' hθs h k hnot
    have h2 := nll_transfer φ hφ hT θ θ' hcl h k
    have h3 := penalty_transfer φ θstar hφ hT θ θ' hθ hθ' hθs hcl h k
    have hcH : 0 < cH R := by unfold cH; positivity
    have hcR : cH R * (16 * R) ≤ 1 := by
      unfold cH
      rw [div_mul_eq_mul_div, one_mul, div_le_one (by positivity)]
      linarith [R_mul_exp_le hR.le]
    have hlogL : log L = log (2 * T / δ) + d * log M := by
      simp only [L, N]
      rw [show 2 * (T : ℝ) * (M : ℝ) ^ d / δ = (2 * T / δ) * (M : ℝ) ^ d by ring,
        log_mul (by positivity) (by positivity), log_pow]
    have := mul_le_mul_of_nonneg_left h3 hcH.le
    rw [hlogL] at h1
    nlinarith

end Event

end StatisticalRL.Ch7Rest.Rlhf
