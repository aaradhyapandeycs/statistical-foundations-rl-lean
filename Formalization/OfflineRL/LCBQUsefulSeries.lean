import Formalization.MDP.DiscountedOccupancyFlow
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Geometrically weighted propagation along `π⋆` (`lemma:useful`)

`chapters/offlineRL.tex:2292–2300`, proof `:4674–4785`. With
`H = ⌈4 log(SAT/δ)/(1-γ)⌉` and `κ = γ(1+1/H)³`, for every nonnegative `W`,
`∑_j κ^j ρᵀ P_π^j W ≤ C (⟨d_ρ^π, W⟩/(1-γ) + δ ‖W‖_∞ /(S T⁴ (1-γ)))` with the universal constant
`C = 84`. Here `ρᵀ P_π^j` is the actual time-`j` state law `occupancyStateAt`.

The proof needs `κ < 1`. The choice of `H` gives this when `log(SAT/δ) ≥ 1`, which is assumed
explicitly; that is a sufficient condition, not a necessary one. Without some such premise the
printed lemma is false (candidate C22 in `docs/SOURCE-ISSUES.md`). The premise does not follow
from the sample-size condition of the enclosing Theorem 6.8; that theorem's hypotheses (for
`c₂ ≥ 32`) still give `κ ≤ 1/2` in the corner `δ > SAT/e`, but this result does not cover that
corner.

The argument follows the source: split the series at `j = H`, compare
`κ^j ≤ e³ γ^j` before the split, and bound the tail geometrically using `γ^H ≤ δ/(S T⁴)` and
`1 - κ ≥ (1-γ)/4`.
-/

open scoped BigOperators
namespace StatisticalRL.OfflineRL.LCBQ
open StatisticalRL.DiscountedMDP

variable {State Action : Type*} [Fintype State] [Fintype Action]

/-- The time-`j` state law has total mass one. -/
theorem occupancyStateAt_sum (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (ρ : FiniteDistribution State) (j : ℕ) : ∑ s, M.occupancyStateAt π ρ j s = 1 :=
  (M.occupancyStateLaw π ρ j).sum_prob

/-- `(1 + 1/H)^(3H) ≤ e³ < 21`. -/
theorem one_add_inv_pow_le (H : ℕ) (hH : 1 ≤ H) : (1 + 1 / (H : ℝ)) ^ (3 * H) ≤ 21 := by
  have hH0 : (0 : ℝ) < H := by exact_mod_cast hH
  have h1 : 1 + 1 / (H : ℝ) ≤ Real.exp (1 / H) := by
    have := Real.add_one_le_exp (1 / (H : ℝ)); linarith
  have h2 : (1 + 1 / (H : ℝ)) ^ H ≤ Real.exp 1 := by
    calc (1 + 1 / (H : ℝ)) ^ H ≤ Real.exp (1 / H) ^ H :=
          pow_le_pow_left₀ (by positivity) h1 H
      _ = Real.exp 1 := by
          rw [← Real.exp_nat_mul]; congr 1; field_simp
  have h3 : Real.exp 1 ^ 3 < 21 := by
    have he := Real.exp_one_lt_d9
    have he0 := Real.exp_pos 1
    have : Real.exp 1 ^ 3 < (2.7182818286 : ℝ) ^ 3 := by
      exact pow_lt_pow_left₀ he he0.le (by norm_num)
    linarith [show (2.7182818286 : ℝ) ^ 3 < 21 by norm_num]
  calc (1 + 1 / (H : ℝ)) ^ (3 * H) = ((1 + 1 / (H : ℝ)) ^ H) ^ 3 := by ring
    _ ≤ Real.exp 1 ^ 3 := pow_le_pow_left₀ (by positivity) h2 3
    _ ≤ 21 := h3.le

/-- `lemma:useful` with the explicit constant `84`, under `log(SAT/δ) ≥ 1`. -/
theorem lcbq_useful (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (ρ : FiniteDistribution State) (δ : ℝ) (T : ℕ) (W : State → ℝ)
    (hδ : 0 < δ) (hδ1 : δ < 1) (hT : 1 ≤ T)
    (hι : 1 ≤ Real.log ((Fintype.card State : ℝ) * Fintype.card Action * T / δ))
    (hW : ∀ s, 0 ≤ W s) :
    let γ := M.discount
    let L := Real.log ((Fintype.card State : ℝ) * Fintype.card Action * T / δ)
    let H : ℕ := ⌈4 / (1 - γ) * L⌉₊
    let κ := γ * (1 + 1 / (H : ℝ)) ^ 3
    ∑' j : ℕ, κ ^ j * ∑ s, M.occupancyStateAt π ρ j s * W s ≤
      84 * ((∑ s, M.discountedStateOccupancy π ρ s * W s) / (1 - γ) +
        δ * ‖W‖ / ((Fintype.card State : ℝ) * (T : ℝ) ^ 4 * (1 - γ))) := by
  intro γ L H κ
  -- Basic scalars.
  have hγ0 : 0 ≤ γ := M.discount_nonneg
  have hγ1 : γ < 1 := M.discount_lt_one
  set x := 1 - γ with hx
  have hx0 : 0 < x := by rw [hx]; linarith
  have hx1 : x ≤ 1 := by rw [hx]; linarith
  have hS1 : (1 : ℝ) ≤ Fintype.card State := by
    have : 0 < Fintype.card State := Fintype.card_pos_iff.mpr M.state_nonempty
    exact_mod_cast this
  have hA1 : (1 : ℝ) ≤ Fintype.card Action := by
    have : 0 < Fintype.card Action := Fintype.card_pos_iff.mpr M.action_nonempty
    exact_mod_cast this
  have hT1 : (1 : ℝ) ≤ T := by exact_mod_cast hT
  set S : ℝ := (Fintype.card State : ℝ) with hSdef
  set A : ℝ := (Fintype.card Action : ℝ) with hAdef
  have hL1 : 1 ≤ L := hι
  -- The horizon `H`.
  have hHge : 4 / x * L ≤ H := Nat.le_ceil _
  have hHx : 4 / x ≤ H := le_trans (by
    have : 4 / x * 1 ≤ 4 / x * L := mul_le_mul_of_nonneg_left hL1 (by positivity)
    linarith) hHge
  have hHpos : (0 : ℝ) < H := lt_of_lt_of_le (by positivity) hHx
  have hH1 : 1 ≤ H := by
    have : (1 : ℝ) ≤ H := le_trans (by rw [le_div_iff₀ hx0]; linarith) hHx
    exact_mod_cast this
  have hinvH : 1 / (H : ℝ) ≤ x / 4 := by
    rw [div_le_div_iff₀ hHpos (by norm_num)]
    have := (div_le_iff₀ hx0).mp hHx
    linarith
  -- `κ ≤ 1 - x/4`.
  have hκ0 : 0 ≤ κ := by positivity
  have hκ1 : κ ≤ 1 - x / 4 := by
    have hpow : (1 + 1 / (H : ℝ)) ^ 3 ≤ (1 + x / 4) ^ 3 :=
      pow_le_pow_left₀ (by positivity) (by linarith) 3
    have hγx : γ = 1 - x := by rw [hx]; ring
    calc κ = γ * (1 + 1 / (H : ℝ)) ^ 3 := rfl
      _ ≤ γ * (1 + x / 4) ^ 3 := mul_le_mul_of_nonneg_left hpow hγ0
      _ = 1 - x / 4 - (9 / 16 * x ^ 2 + 11 / 64 * x ^ 3 + 1 / 64 * x ^ 4) := by
          rw [hγx]; ring
      _ ≤ 1 - x / 4 := by
          have : 0 ≤ 9 / 16 * x ^ 2 + 11 / 64 * x ^ 3 + 1 / 64 * x ^ 4 := by positivity
          linarith
  have hκlt : κ < 1 := by linarith
  -- Early terms: `κ^j ≤ 21 γ^j` for `j ≤ H`.
  have hearly : ∀ j, j ≤ H → κ ^ j ≤ 21 * γ ^ j := by
    intro j hj
    have hb : 1 ≤ 1 + 1 / (H : ℝ) := by have : 0 ≤ 1 / (H : ℝ) := by positivity
                                        linarith
    calc κ ^ j = γ ^ j * (1 + 1 / (H : ℝ)) ^ (3 * j) := by
          simp only [κ]; rw [mul_pow, ← pow_mul, mul_comm 3 j]
      _ ≤ γ ^ j * (1 + 1 / (H : ℝ)) ^ (3 * H) := by
          apply mul_le_mul_of_nonneg_left _ (pow_nonneg hγ0 j)
          exact pow_le_pow_right₀ hb (by omega)
      _ ≤ γ ^ j * 21 := mul_le_mul_of_nonneg_left (one_add_inv_pow_le H hH1) (pow_nonneg hγ0 j)
      _ = 21 * γ ^ j := by ring
  -- `γ^H ≤ δ/(S T⁴)`.
  have hγH : γ ^ H ≤ δ / (S * (T : ℝ) ^ 4) := by
    have hSAT : 0 < S * A * T / δ := by positivity
    have h1 : γ ≤ Real.exp (-x) := by have := Real.add_one_le_exp (-x); rw [hx] at this ⊢; linarith
    have h2 : γ ^ H ≤ Real.exp (-x) ^ H := pow_le_pow_left₀ hγ0 h1 H
    have h3 : Real.exp (-x) ^ H = Real.exp (-(x * H)) := by
      rw [← Real.exp_nat_mul]; congr 1; ring
    have h4 : x * H ≥ 4 * L := by
      have := (div_mul_eq_mul_div 4 x L) ▸ hHge
      rw [div_le_iff₀ hx0] at this
      linarith
    have h5 : Real.exp (-(x * H)) ≤ Real.exp (-(4 * L)) := Real.exp_le_exp.mpr (by linarith)
    have h6 : Real.exp (-(4 * L)) = (δ / (S * A * T)) ^ 4 := by
      have hL : Real.exp L = S * A * T / δ := Real.exp_log hSAT
      rw [show -(4 * L) = (4 : ℕ) * (-L) by push_cast; ring, Real.exp_nat_mul, Real.exp_neg, hL]
      field_simp
    have h7 : (δ / (S * A * T)) ^ 4 ≤ δ / (S * (T : ℝ) ^ 4) := by
      have hδ3 : δ ^ 3 ≤ 1 := pow_le_one₀ hδ.le hδ1.le
      have hS3A4 : 1 ≤ S ^ 3 * A ^ 4 := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hS1)
        (one_le_pow₀ hA1)
      have e : (δ / (S * A * T)) ^ 4 = δ / (S * (T : ℝ) ^ 4) * (δ ^ 3 / (S ^ 3 * A ^ 4)) := by
        field_simp
        try ring
      rw [e]
      have : δ ^ 3 / (S ^ 3 * A ^ 4) ≤ 1 := by
        rw [div_le_one (by positivity)]; linarith
      have hpos : 0 ≤ δ / (S * (T : ℝ) ^ 4) := by positivity
      exact mul_le_of_le_one_right hpos this
    calc γ ^ H ≤ _ := h2
      _ = _ := h3
      _ ≤ _ := h5
      _ = _ := h6
      _ ≤ _ := h7
  have hκH : κ ^ H ≤ 21 * δ / (S * (T : ℝ) ^ 4) := by
    have := hearly H le_rfl
    have h2 := mul_le_mul_of_nonneg_left hγH (by norm_num : (0 : ℝ) ≤ 21)
    calc κ ^ H ≤ 21 * γ ^ H := this
      _ ≤ 21 * (δ / (S * (T : ℝ) ^ 4)) := h2
      _ = 21 * δ / (S * (T : ℝ) ^ 4) := by ring
  -- The sequence `a_j = ρᵀ P^j W`.
  set a : ℕ → ℝ := fun j => ∑ s, M.occupancyStateAt π ρ j s * W s with ha
  have ha0 : ∀ j, 0 ≤ a j := fun j =>
    Finset.sum_nonneg fun s _ => mul_nonneg (M.occupancyStateAt_nonneg π ρ j s) (hW s)
  have haW : ∀ j, a j ≤ ‖W‖ := by
    intro j
    calc a j ≤ ∑ s, M.occupancyStateAt π ρ j s * ‖W‖ :=
          Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left
            ((le_abs_self (W s)).trans (by simpa using norm_le_pi_norm W s))
            (M.occupancyStateAt_nonneg π ρ j s)
      _ = ‖W‖ := by rw [← Finset.sum_mul, occupancyStateAt_sum, one_mul]
  have hWn : 0 ≤ ‖W‖ := norm_nonneg W
  -- Summability.
  have hgeomκ : Summable (fun j : ℕ => κ ^ j * ‖W‖) :=
    (summable_geometric_of_lt_one hκ0 hκlt).mul_right _
  have hsumκ : Summable (fun j : ℕ => κ ^ j * a j) :=
    Summable.of_nonneg_of_le (fun j => mul_nonneg (pow_nonneg hκ0 j) (ha0 j))
      (fun j => mul_le_mul_of_nonneg_left (haW j) (pow_nonneg hκ0 j)) hgeomκ
  have hsumγ : Summable (fun j : ℕ => γ ^ j * a j) :=
    Summable.of_nonneg_of_le (fun j => mul_nonneg (pow_nonneg hγ0 j) (ha0 j))
      (fun j => mul_le_mul_of_nonneg_left (haW j) (pow_nonneg hγ0 j))
      ((summable_geometric_of_lt_one hγ0 hγ1).mul_right _)
  -- `∑_j γ^j a_j = ⟨d, W⟩/(1-γ)`.
  have hocc : ∑ s, M.discountedStateOccupancy π ρ s * W s = x * ∑' j : ℕ, γ ^ j * a j := by
    have hsum_s : ∀ s, Summable (fun t : ℕ => γ ^ t * M.occupancyStateAt π ρ t s * W s) :=
      fun s => (M.discountedState_summable π ρ s).mul_right _
    calc ∑ s, M.discountedStateOccupancy π ρ s * W s
        = ∑ s, x * ∑' t : ℕ, γ ^ t * M.occupancyStateAt π ρ t s * W s := by
          refine Finset.sum_congr rfl fun s _ => ?_
          unfold discountedStateOccupancy
          rw [tsum_mul_right]; ring
      _ = x * ∑ s, ∑' t : ℕ, γ ^ t * M.occupancyStateAt π ρ t s * W s := by
          rw [Finset.mul_sum]
      _ = x * ∑' t : ℕ, ∑ s, γ ^ t * M.occupancyStateAt π ρ t s * W s := by
          rw [Summable.tsum_finsetSum (fun s _ => hsum_s s)]
      _ = x * ∑' j : ℕ, γ ^ j * a j := by
          congr 1; refine tsum_congr fun j => ?_
          simp only [ha, Finset.mul_sum]
          refine Finset.sum_congr rfl fun s _ => ?_; ring
  -- Split the series at `H`.
  show ∑' j : ℕ, κ ^ j * a j ≤ _
  rw [← hsumκ.sum_add_tsum_nat_add H]
  have hfirst : ∑ j ∈ Finset.range H, κ ^ j * a j ≤ 21 * ∑' j : ℕ, γ ^ j * a j := by
    calc ∑ j ∈ Finset.range H, κ ^ j * a j ≤ ∑ j ∈ Finset.range H, 21 * (γ ^ j * a j) :=
          Finset.sum_le_sum fun j hj => by
            have := hearly j (Finset.mem_range.mp hj).le
            calc κ ^ j * a j ≤ (21 * γ ^ j) * a j := mul_le_mul_of_nonneg_right this (ha0 j)
              _ = 21 * (γ ^ j * a j) := by ring
      _ = 21 * ∑ j ∈ Finset.range H, γ ^ j * a j := by rw [Finset.mul_sum]
      _ ≤ 21 * ∑' j : ℕ, γ ^ j * a j := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          exact hsumγ.sum_le_tsum _ (fun j _ => mul_nonneg (pow_nonneg hγ0 j) (ha0 j))
  have hsecond : ∑' j : ℕ, κ ^ (j + H) * a (j + H) ≤ 84 * (δ * ‖W‖ / (S * (T : ℝ) ^ 4 * x)) := by
    have hle : ∑' j : ℕ, κ ^ (j + H) * a (j + H) ≤ ∑' j : ℕ, κ ^ H * (κ ^ j * ‖W‖) := by
      apply Summable.tsum_le_tsum _ ((hsumκ.comp_injective (add_left_injective H)))
        (hgeomκ.mul_left _)
      intro j
      have := mul_le_mul_of_nonneg_left (haW (j + H)) (mul_nonneg (pow_nonneg hκ0 H)
        (pow_nonneg hκ0 j))
      calc κ ^ (j + H) * a (j + H) = κ ^ H * κ ^ j * a (j + H) := by rw [pow_add]; ring
        _ ≤ κ ^ H * κ ^ j * ‖W‖ := this
        _ = κ ^ H * (κ ^ j * ‖W‖) := by ring
    have hgeo : ∑' j : ℕ, κ ^ H * (κ ^ j * ‖W‖) = κ ^ H * ‖W‖ / (1 - κ) := by
      rw [tsum_mul_left, tsum_mul_right, tsum_geometric_of_lt_one hκ0 hκlt]
      field_simp
    have h1κ : x / 4 ≤ 1 - κ := by linarith
    have hfin : κ ^ H * ‖W‖ / (1 - κ) ≤ 84 * (δ * ‖W‖ / (S * (T : ℝ) ^ 4 * x)) := by
      have hκHn : 0 ≤ κ ^ H := pow_nonneg hκ0 H
      calc κ ^ H * ‖W‖ / (1 - κ) ≤ κ ^ H * ‖W‖ / (x / 4) :=
            div_le_div_of_nonneg_left (mul_nonneg hκHn hWn) (by positivity) h1κ
        _ ≤ (21 * δ / (S * (T : ℝ) ^ 4)) * ‖W‖ / (x / 4) := by
            apply div_le_div_of_nonneg_right _ (by positivity)
            exact mul_le_mul_of_nonneg_right hκH hWn
        _ = 84 * (δ * ‖W‖ / (S * (T : ℝ) ^ 4 * x)) := by
            field_simp
            ring
    linarith
  have hA0 : 0 ≤ (∑ s, M.discountedStateOccupancy π ρ s * W s) / x := by
    rw [hocc]
    have : 0 ≤ ∑' j : ℕ, γ ^ j * a j :=
      tsum_nonneg fun j => mul_nonneg (pow_nonneg hγ0 j) (ha0 j)
    positivity
  have hdiv : 21 * ∑' j : ℕ, γ ^ j * a j = 21 * ((∑ s, M.discountedStateOccupancy π ρ s * W s) / x) := by
    rw [hocc]; field_simp
  have hB0 : 0 ≤ δ * ‖W‖ / (S * (T : ℝ) ^ 4 * x) := by positivity
  change ∑ j ∈ Finset.range H, κ ^ j * a j + ∑' j : ℕ, κ ^ (j + H) * a (j + H) ≤
    84 * ((∑ s, M.discountedStateOccupancy π ρ s * W s) / x + δ * ‖W‖ / (S * (T : ℝ) ^ 4 * x))
  linarith [hfirst, hsecond, hdiv, hA0, hB0]

end StatisticalRL.OfflineRL.LCBQ
