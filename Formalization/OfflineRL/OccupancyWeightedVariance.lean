import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Occupancy-weighted variance propagation (proof of `lem:sum-d-Var-UB`)

Source `chapters/offlineRL.tex:4277–4335` (statement `:1529–1537`). Deterministic helper.

Rows `P s ·` are real stochastic vectors, `ρ` is a probability vector, and `d ≥ 0`
solves the discounted flow equation `d = (1-γ) ρ + γ Pᵀ d`. With `0 ≤ V ≤ 1/(1-γ)`,
`b ≥ 0` and the upstream residual nonnegativity `0 ≤ V - γ P V + 2b`:

`∑ d · Var_P(V) ≤ 2/(γ²(1-γ)) + 4/(γ²(1-γ)) · ∑ d b`.

Argument: pointwise `V² - (γ P V)² ≤ 2/(1-γ) · (V - γ P V + 2b)`; relax `V²` to `γ V²`;
sum against `d` using the flow equation; discard `-γ(1-γ) ∑ ρ V² ≤ 0`; bound
`(1-γ) ∑ ρ V ≤ 1`. Only `0 < γ < 1` is used (no `γ ≥ 1/2`). Helper only: the
residual hypothesis must be derived by the consumer from genuine VI-LCB objects.
-/

open scoped BigOperators

namespace StatisticalRL.OfflineRL.BonusSummation

universe u

theorem occupancyWeightedVariance {S : Type u} [Fintype S]
    (P : S → S → ℝ) (d ρ V b : S → ℝ) (γ : ℝ)
    (hγ : 0 < γ) (hγ1 : γ < 1)
    (hP : ∀ s t, 0 ≤ P s t) (hPsum : ∀ s, ∑ t, P s t = 1)
    (hd : ∀ s, 0 ≤ d s) (hρ : ∀ s, 0 ≤ ρ s) (hρsum : ∑ s, ρ s = 1)
    (hflow : ∀ s, d s = (1 - γ) * ρ s + γ * ∑ t, d t * P t s)
    (hV0 : ∀ s, 0 ≤ V s) (hV1 : ∀ s, V s ≤ 1 / (1 - γ))
    (hb : ∀ s, 0 ≤ b s)
    (hres : ∀ s, 0 ≤ V s - γ * (∑ t, P s t * V t) + 2 * b s) :
    ∑ s, d s * ((∑ t, P s t * (V t)^2) - (∑ t, P s t * V t)^2) ≤
      2 / (γ^2 * (1 - γ)) +
        (4 / (γ^2 * (1 - γ))) * (∑ s, d s * b s) := by
  -- Opaque abbreviations, so that rewriting is purely syntactic.
  obtain ⟨w, hw⟩ : ∃ w : S → ℝ, ∀ s, w s = ∑ t, P s t * V t := ⟨_, fun _ => rfl⟩
  obtain ⟨q, hq⟩ : ∃ q : S → ℝ, ∀ s, q s = ∑ t, P s t * V t ^ 2 := ⟨_, fun _ => rfl⟩
  obtain ⟨m, hm⟩ : ∃ m : S → ℝ, ∀ t, m t = ∑ s, d s * P s t := ⟨_, fun _ => rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = 1 / (1 - γ) := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = 2 / (1 - γ) := ⟨_, rfl⟩
  simp_rw [← hq, ← hw]
  simp_rw [← hw] at hres
  have h1g : 0 < 1 - γ := sub_pos.mpr hγ1
  have h1g' : 1 - γ ≠ 0 := h1g.ne'
  have hγ' : γ ≠ 0 := hγ.ne'
  have hcB : c = 2 * B := by rw [hc, hB]; ring
  have hBg : (1 - γ) * B = 1 := by rw [hB]; field_simp
  have hV1' : ∀ s, V s ≤ B := fun s => by rw [hB]; exact hV1 s
  have hflow' : ∀ t, d t = (1 - γ) * ρ t + γ * m t := fun t => by rw [hm t]; exact hflow t
  -- Row expectations of `V` lie in `[0, B]`.
  have hw0 : ∀ s, 0 ≤ w s := fun s => by
    rw [hw s]; exact Finset.sum_nonneg fun t _ => mul_nonneg (hP s t) (hV0 t)
  have hw1 : ∀ s, w s ≤ B := fun s => by
    calc w s = ∑ t, P s t * V t := hw s
      _ ≤ ∑ t, P s t * B :=
          Finset.sum_le_sum fun t _ => mul_le_mul_of_nonneg_left (hV1' t) (hP s t)
      _ = B := by rw [← Finset.sum_mul, hPsum s, one_mul]
  -- Pointwise auxiliary bound `eq:infinite-extra-lemma-au1`.
  have haux : ∀ s, V s ^ 2 - (γ * w s) ^ 2 ≤ c * (V s - γ * w s + 2 * b s) := by
    intro s
    have hsum0 : 0 ≤ V s + γ * w s := add_nonneg (hV0 s) (mul_nonneg hγ.le (hw0 s))
    have hgw : γ * w s ≤ B := by
      nlinarith [hw1 s, mul_nonneg (sub_nonneg.2 hγ1.le) (hw0 s)]
    have hsumle : V s + γ * w s ≤ c := by rw [hcB]; linarith [hV1' s]
    calc V s ^ 2 - (γ * w s) ^ 2 = (V s - γ * w s) * (V s + γ * w s) := by ring
      _ ≤ (V s - γ * w s + 2 * b s) * (V s + γ * w s) := by
          nlinarith [mul_nonneg (hb s) hsum0]
      _ ≤ (V s - γ * w s + 2 * b s) * c := mul_le_mul_of_nonneg_left hsumle (hres s)
      _ = c * (V s - γ * w s + 2 * b s) := by ring
  -- Relax `V²` to `γ V²`, multiplied through by `γ²`.
  have hpt : ∀ s, γ ^ 2 * (q s - w s ^ 2) ≤
      γ ^ 2 * q s - γ * V s ^ 2 + c * (V s - γ * w s + 2 * b s) := fun s => by
    nlinarith [haux s, mul_nonneg (sub_nonneg.2 hγ1.le) (sq_nonneg (V s))]
  have hpt2 : ∀ s, γ ^ 2 * (d s * (q s - w s ^ 2)) ≤
      γ ^ 2 * (d s * q s) - γ * (d s * V s ^ 2) + c * (d s * V s) -
        c * γ * (d s * w s) + 2 * c * (d s * b s) := fun s => by
    nlinarith [mul_le_mul_of_nonneg_left (hpt s) (hd s)]
  have hsum := Finset.sum_le_sum (fun s (_ : s ∈ (Finset.univ : Finset S)) => hpt2 s)
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum] at hsum
  -- Flow identities.
  have hswap : ∀ f : S → ℝ, ∑ s, d s * ∑ t, P s t * f t = ∑ t, m t * f t := by
    intro f
    calc ∑ s, d s * ∑ t, P s t * f t = ∑ s, ∑ t, d s * (P s t * f t) := by
          simp_rw [Finset.mul_sum]
      _ = ∑ t, ∑ s, d s * (P s t * f t) := Finset.sum_comm
      _ = ∑ t, m t * f t := by
          refine Finset.sum_congr rfl fun t _ => ?_
          rw [hm t, Finset.sum_mul]
          exact Finset.sum_congr rfl fun s _ => by ring
  have I1 : ∑ s, d s * q s = ∑ t, m t * V t ^ 2 := by
    simp_rw [hq]; exact hswap (fun t => V t ^ 2)
  have I2 : ∑ s, d s * w s = ∑ t, m t * V t := by
    simp_rw [hw]; exact hswap V
  have hflowsum : ∀ f : S → ℝ,
      ∑ t, d t * f t = (1 - γ) * ∑ t, ρ t * f t + γ * ∑ t, m t * f t := by
    intro f
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun t _ => by rw [hflow' t]; ring
  have I3 : ∑ t, d t * V t ^ 2 = (1 - γ) * ∑ t, ρ t * V t ^ 2 + γ * ∑ t, m t * V t ^ 2 :=
    hflowsum (fun t => V t ^ 2)
  have I4 : ∑ t, d t * V t = (1 - γ) * ∑ t, ρ t * V t + γ * ∑ t, m t * V t := hflowsum V
  -- `∑ ρ V ≤ B` and `∑ ρ V² ≥ 0`.
  have hρV : ∑ t, ρ t * V t ≤ B := by
    calc ∑ t, ρ t * V t ≤ ∑ t, ρ t * B :=
          Finset.sum_le_sum fun t _ => mul_le_mul_of_nonneg_left (hV1' t) (hρ t)
      _ = B := by rw [← Finset.sum_mul, hρsum, one_mul]
  have hρV2 : 0 ≤ ∑ t, ρ t * V t ^ 2 :=
    Finset.sum_nonneg fun t _ => mul_nonneg (hρ t) (sq_nonneg _)
  have E : γ ^ 2 * ∑ s, d s * q s - γ * ∑ s, d s * V s ^ 2 + c * ∑ s, d s * V s -
      c * γ * ∑ s, d s * w s + 2 * c * ∑ s, d s * b s =
      -(γ * (1 - γ)) * ∑ t, ρ t * V t ^ 2 + c * ((1 - γ) * ∑ t, ρ t * V t) +
        2 * c * ∑ s, d s * b s := by
    rw [I1, I2, I3, I4]; ring
  have hc0 : 0 ≤ c := by rw [hc]; exact div_nonneg (by norm_num) h1g.le
  have hcρ : c * ((1 - γ) * ∑ t, ρ t * V t) ≤ c := by
    have : (1 - γ) * ∑ t, ρ t * V t ≤ 1 := by
      calc (1 - γ) * ∑ t, ρ t * V t ≤ (1 - γ) * B := mul_le_mul_of_nonneg_left hρV h1g.le
        _ = 1 := hBg
    have := mul_le_mul_of_nonneg_left this hc0
    linarith
  have key : γ ^ 2 * ∑ s, d s * (q s - w s ^ 2) ≤ c + 2 * c * ∑ s, d s * b s := by
    linarith [mul_nonneg (mul_nonneg hγ.le h1g.le) hρV2]
  have hR : 2 / (γ ^ 2 * (1 - γ)) + 4 / (γ ^ 2 * (1 - γ)) * ∑ s, d s * b s =
      (c + 2 * c * ∑ s, d s * b s) / γ ^ 2 := by
    rw [hc]; field_simp; ring
  rw [hR, le_div_iff₀ (pow_pos hγ 2)]
  linarith
end StatisticalRL.OfflineRL.BonusSummation
