import Formalization.RLHF.VPO.Regret

/-!
# Corrected Theorem 7.12: the regret bounds with probability `1 − δ`

Both bounds hold simultaneously on `E₁ ∩ E₂`, which has probability at least `1 − δ` under the
trajectory law `vpoTrajWeight`, for every ball-constrained selection rule.
-/

namespace StatisticalRL.Ch7Rest.Rlhf

open Finset Real

set_option linter.unusedSectionVars false

variable {X Y : Type} [Fintype X] [Fintype Y] {d : ℕ}

/-- Main export: for every ball-constrained selection rule, with probability at least `1 − δ`,
`Regret ≤ T B′/α + K Γ α` and `Regret ≤ (e^{4R/β}/(4β)) (16R² + 16 e^{4R} (B′ + 4Rα)) Γ`, with
`B′ = 2 log(2T/δ) + 2d log⌈2RT√d⌉₊ + 4`, `Γ = (e/(e−1)) (2d log(1 + T/d) + log(2/δ))`,
`K = 2κ e^{4R + 2R/β}`. -/
theorem vpo_regret_both (ρ : X → ℝ) (π_ref π_cal : X → Y → ℝ)
    (φ : X → Y → EuclideanSpace ℝ (Fin d)) (θstar : EuclideanSpace ℝ (Fin d)) {T : ℕ}
    {β R α δ : ℝ} (hd : 0 < d) (hT : 1 ≤ T) (hρ : ∀ x, 0 ≤ ρ x) (hρ1 : ∑ x, ρ x = 1)
    (href : IsPositivePolicy π_ref) (hcal : IsCondPolicy π_cal) (hφ : ∀ x y, ‖φ x y‖ ≤ 1)
    (hβ : 0 < β) (hR : 0 < R) (hθs : ‖θstar‖ ≤ R) (hα : 0 < α) (hδ : 0 < δ)
    (sel : List (X × Y × Y) → EuclideanSpace ℝ (Fin d))
    (hsel : IsBallSelection ρ π_ref π_cal φ α β R sel) :
    1 - δ ≤ ∑ h : Fin T → X × Y × Y × Bool, vpoTrajWeight ρ π_ref φ θstar β sel h *
      (if vpoRegret ρ π_ref π_cal φ θstar β sel h ≤
          T * (2 * log (2 * T / δ) + 2 * d * log ⌈2 * R * T * √(d : ℝ)⌉₊ + 4) / α +
            2 * vpoKappa π_ref π_cal * exp (4 * R + 2 * R / β) *
              (exp 1 / (exp 1 - 1) * (2 * d * log (1 + T / d) + log (2 / δ))) * α ∧
        vpoRegret ρ π_ref π_cal φ θstar β sel h ≤
          exp (4 * R / β) / (4 * β) * (16 * R ^ 2 + 16 * exp (4 * R) *
            ((2 * log (2 * T / δ) + 2 * d * log ⌈2 * R * T * √(d : ℝ)⌉₊ + 4) + 4 * R * α)) *
            (exp 1 / (exp 1 - 1) * (2 * d * log (1 + T / d) + log (2 / δ)))
        then 1 else 0) := by
  classical
  obtain ⟨bad1, hb1, hg1⟩ := e1_uniform ρ π_ref φ θstar β sel hρ hρ1 href hφ hR hθs hδ hT hd
  have hb2 := e2_event ρ π_ref φ θstar β sel hρ hρ1 href hφ hδ (T := T)
  set B := 2 * log (2 * T / δ) + 2 * d * log (gridM R T d : ℝ) + 3 with hBdef
  set Bp := 2 * log (2 * T / δ) + 2 * d * log ⌈2 * R * T * √(d : ℝ)⌉₊ + 4
  have hBp : B + 1 = Bp := by simp only [B, Bp, gridM]; ring
  set Γ := exp 1 / (exp 1 - 1) * (2 * d * log (1 + T / d) + log (2 / δ))
  set K := 2 * vpoKappa π_ref π_cal * exp (4 * R + 2 * R / β)
  set C := exp (4 * R / β) / (4 * β)
  have hgood : ∀ h : Fin T → X × Y × Y × Bool, ¬ bad1 h →
      ¬ (2 / δ ≤ ∏ k, exp ((1 - exp (-1)) * uStat ρ π_ref φ β sel h k - xStat φ h k)) →
      vpoRegret ρ π_ref π_cal φ θstar β sel h ≤ T * Bp / α + K * Γ * α ∧
        vpoRegret ρ π_ref π_cal φ θstar β sel h ≤
          C * (16 * R ^ 2 + 16 * exp (4 * R) * (Bp + 4 * R * α)) * Γ := by
    intro h n1 n2
    have hu := e2_consequence ρ π_ref φ β sel hφ hd hδ h n2
    have hu0 : ∀ k, 0 ≤ uStat ρ π_ref φ β sel h k :=
      fun k ↦ uStat_nonneg ρ π_ref φ β sel hρ href h k
    have hE1 := fun k ↦ hg1 h n1 k (sel (vpoData h k)) (hsel _).1
    unfold vpoRegret
    constructor
    · have hr := fun k ↦ round_bound_kappa hρ hρ1 href hcal hφ hR hθs hα hβ hsel h k (hE1 k)
      calc _ ≤ ∑ k : Fin T, ((B + 1) / α + K * α * uStat ρ π_ref φ β sel h k) :=
            sum_le_sum fun k _ ↦ le_trans (hr k) (le_of_eq (by ring))
        _ = T * (B + 1) / α + K * α * ∑ k, uStat ρ π_ref φ β sel h k := by
            rw [sum_add_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, ← mul_sum]
            ring
        _ ≤ T * Bp / α + K * Γ * α := by
            rw [hBp]
            have hK : 0 ≤ K * α := by
              have hκ : 0 ≤ vpoKappa π_ref π_cal := by
                obtain ⟨x₀, -⟩ : (univ : Finset X).Nonempty := by
                  by_contra hX
                  rw [not_nonempty_iff_eq_empty.1 hX, sum_empty] at hρ1
                  exact zero_ne_one hρ1
                obtain ⟨y₀, -⟩ := univ_nonempty_of_pos href x₀
                exact vpoKappa_nonneg π_ref π_cal href hcal x₀ y₀
              positivity
            have := mul_le_mul_of_nonneg_left hu hK
            linarith
    · have hr := fun k ↦ round_bound_local hρ hρ1 href hcal hφ hR hθs hα hβ hsel h k (hE1 k)
      have hC : 0 ≤ C * (16 * R ^ 2 + 16 * exp (4 * R) * (Bp + 4 * R * α)) := by
        have hBp0 : 0 ≤ Bp + 4 * R * α := by
          rw [← hBp]
          have : 0 ≤ ∑ k : Fin T, uStat ρ π_ref φ β sel h k := sum_nonneg fun k _ ↦ hu0 k
          -- `B + 1 + 4Rα ≥ 0` follows from `c_H S ≤ B + 4Rα` at round 0
          have hk0 := hE1 ⟨0, hT⟩
          have hfilter : univ.filter (fun j : Fin T ↦ j < ⟨0, hT⟩) = ∅ := by
            ext j; simp [Fin.lt_def]
          rw [hfilter, sum_empty, mul_zero, sub_zero] at hk0
          have hdata : vpoData h ⟨0, hT⟩ = [] := by
            unfold vpoData
            rw [List.map_eq_nil_iff, List.filter_eq_nil_iff]
            intro j _; simp [Fin.lt_def]
          rw [hdata] at hk0
          simp only [nll, List.map_nil, List.sum_nil, neg_zero, sub_self] at hk0
          have : 0 ≤ R * α := by positivity
          linarith
        positivity
      calc _ ≤ ∑ k : Fin T, C * (16 * R ^ 2 + 16 * exp (4 * R) * (Bp + 4 * R * α)) *
            uStat ρ π_ref φ β sel h k :=
            sum_le_sum fun k _ ↦ le_trans (hr k) (le_of_eq (by rw [hBp]))
        _ = C * (16 * R ^ 2 + 16 * exp (4 * R) * (Bp + 4 * R * α)) *
            ∑ k, uStat ρ π_ref φ β sel h k := by rw [mul_sum]
        _ ≤ _ := mul_le_mul_of_nonneg_left hu hC
  -- probability
  have hw0 := vpoTrajWeight_nonneg ρ π_ref φ θstar β sel hρ href (T := T)
  have hsum := vpoTrajWeight_sum ρ π_ref φ θstar β sel hρ1 href T
  have key : ∀ h : Fin T → X × Y × Y × Bool,
      vpoTrajWeight ρ π_ref φ θstar β sel h -
        vpoTrajWeight ρ π_ref φ θstar β sel h * (if bad1 h then 1 else 0) -
        vpoTrajWeight ρ π_ref φ θstar β sel h *
          (if 2 / δ ≤ ∏ k, exp ((1 - exp (-1)) * uStat ρ π_ref φ β sel h k - xStat φ h k)
            then 1 else 0) ≤
      vpoTrajWeight ρ π_ref φ θstar β sel h *
        (if vpoRegret ρ π_ref π_cal φ θstar β sel h ≤ T * Bp / α + K * Γ * α ∧
            vpoRegret ρ π_ref π_cal φ θstar β sel h ≤
              C * (16 * R ^ 2 + 16 * exp (4 * R) * (Bp + 4 * R * α)) * Γ then 1 else 0) := by
    intro h
    have hw := hw0 h
    by_cases n1 : bad1 h
    · rw [if_pos n1]
      have : 0 ≤ vpoTrajWeight ρ π_ref φ θstar β sel h *
          (if 2 / δ ≤ ∏ k, exp ((1 - exp (-1)) * uStat ρ π_ref φ β sel h k - xStat φ h k)
            then 1 else 0) := mul_nonneg hw (by split_ifs <;> norm_num)
      have : 0 ≤ vpoTrajWeight ρ π_ref φ θstar β sel h *
          (if vpoRegret ρ π_ref π_cal φ θstar β sel h ≤ T * Bp / α + K * Γ * α ∧
            vpoRegret ρ π_ref π_cal φ θstar β sel h ≤
              C * (16 * R ^ 2 + 16 * exp (4 * R) * (Bp + 4 * R * α)) * Γ then 1 else 0) :=
        mul_nonneg hw (by split_ifs <;> norm_num)
      linarith
    · rw [if_neg n1]
      by_cases n2 : 2 / δ ≤ ∏ k, exp ((1 - exp (-1)) * uStat ρ π_ref φ β sel h k - xStat φ h k)
      · rw [if_pos n2]
        have : 0 ≤ vpoTrajWeight ρ π_ref φ θstar β sel h *
            (if vpoRegret ρ π_ref π_cal φ θstar β sel h ≤ T * Bp / α + K * Γ * α ∧
              vpoRegret ρ π_ref π_cal φ θstar β sel h ≤
                C * (16 * R ^ 2 + 16 * exp (4 * R) * (Bp + 4 * R * α)) * Γ then 1 else 0) :=
          mul_nonneg hw (by split_ifs <;> norm_num)
        linarith
      · rw [if_neg n2, if_pos (hgood h n1 n2)]
        linarith
  have hS := sum_le_sum fun h (_ : h ∈ univ) ↦ key h
  rw [sum_sub_distrib, sum_sub_distrib, hsum] at hS
  have hb1' : ∑ h : Fin T → X × Y × Y × Bool,
      vpoTrajWeight ρ π_ref φ θstar β sel h * (if bad1 h then 1 else 0) ≤ δ / 2 := hb1
  linarith

end StatisticalRL.Ch7Rest.Rlhf
