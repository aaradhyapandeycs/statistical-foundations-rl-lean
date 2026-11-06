import Formalization.OfflineRL.LowerBoundFamilyValues

/-!
# Per-state value gap of the offline hard family (`eq:infinite-delta-key-auxiliary`)

`chapters/offlineRL.tex:2659–2666`, proof `:5869–5933`. For every `θ`, every stationary
randomized policy `π` and every positive state `s`,
`V⋆_θ(s) - V^π_θ(s) ≥ 24 ε (1 - π(θ_s | s))`.

The proof uses the policy upper bound of Lemma 6.14 (`lb_policy_value_le`),
`V^π(s) ≤ (1 + γ(1-x)W)/(1 - γx)` with `x = p π(θ_s|s) + q π(1-θ_s|s)`, and the closed form
`V⋆(s) = lbVs` with `lbVs (1 - γp) = 1 + γ(1-p)W`. Then
`V⋆(s) - g(x) = γ(p-x)(V⋆(s) - W)/(1-γx)`, `(V⋆(s) - W)(1 - γp) = 1 - (1-γ)W ≥ 3/14`,
`(1-γp)(1-γq) ≤ 4(1-γ)²` and `γ(p - x) = 448(1-γ)²ε(1 - π(θ_s|s))`.
-/

open scoped BigOperators
namespace StatisticalRL.OfflineRL.LowerBound
open StatisticalRL.DiscountedMDP

/-- The scalar core of `eq:infinite-delta-key-auxiliary` (all quantities are plain reals). -/
theorem lb_value_gap_scalar {γ ε C δ p q a b Vs Vz W Vpi : ℝ}
    (hγ : 2 / 3 ≤ γ) (hγ1 : γ < 1) (hε : 0 ≤ ε) (hC : 2 < C)
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ (1 - γ) / 2) (hγδ : γ * δ = 224 * (1 - γ) ^ 2 * ε)
    (hp : p = γ + δ) (hq : q = γ - δ)
    (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) (hab : a + b = 1)
    (hVs : Vs = 1 + γ * (p * Vs + (1 - p) * W)) (hVz : Vz = 4 / 7 + γ * Vz) (hWVs : W < Vs)
    (hW : W = (1 - 1 / C) * Vz + Vs / C)
    (hVpi : Vpi ≤ (1 + γ * (1 - (p * a + q * b)) * W) / (1 - γ * (p * a + q * b))) :
    24 * ε * (1 - a) ≤ Vs - Vpi := by
  have hγ0 : 0 < γ := by linarith
  have h1γ : 0 < 1 - γ := by linarith
  have hC0 : 0 < C := by linarith
  have hb : b = 1 - a := by linarith
  have ha1 : a ≤ 1 := by linarith
  subst hb hp hq
  -- the mixture `x = p a + q b`
  set x := (γ + δ) * a + (γ - δ) * (1 - a) with hx_def
  have hxa : x = (γ - δ) + 2 * δ * a := by rw [hx_def]; ring
  have hpx : (γ + δ) - x = 2 * δ * (1 - a) := by rw [hxa]; ring
  have hδa : 0 ≤ δ * a := mul_nonneg hδ0 ha0
  have hδa' : 0 ≤ δ * (1 - a) := mul_nonneg hδ0 (by linarith)
  have hxq : γ - δ ≤ x := by rw [hxa]; linarith
  have hxp : x ≤ γ + δ := by linarith
  have hp1 : γ + δ < 1 := by linarith
  have hx0 : 0 ≤ x := by linarith
  have hγx : γ * x ≤ γ * (γ + δ) := mul_le_mul_of_nonneg_left hxp hγ0.le
  have hγp : γ * (γ + δ) < 1 := by
    have : γ * (γ + δ) ≤ 1 * (γ + δ) := mul_le_mul_of_nonneg_right hγ1.le (by linarith)
    linarith
  have hE : 0 < 1 - γ * x := by linarith
  have hEp : 0 < 1 - γ * (γ + δ) := by linarith
  have hEq : 1 - γ * x ≤ 1 - γ * (γ - δ) := by
    have := mul_le_mul_of_nonneg_left hxq hγ0.le
    linarith
  -- `(V⋆(s) - W)(1 - γ p) = 1 - (1-γ) W ≥ 3/14`
  have hVsp : Vs * (1 - γ * (γ + δ)) = 1 + γ * (1 - (γ + δ)) * W := by linear_combination hVs
  have hVz7 : (1 - γ) * Vz = 4 / 7 := by linear_combination hVz
  have hVs1 : (1 - γ) * Vs ≤ 1 := by
    have h1 : (1 - (γ + δ)) * W ≤ (1 - (γ + δ)) * Vs :=
      mul_le_mul_of_nonneg_left hWVs.le (by linarith)
    have h2 : (γ + δ) * Vs + (1 - (γ + δ)) * W ≤ Vs := by linarith
    have h3 : γ * ((γ + δ) * Vs + (1 - (γ + δ)) * W) ≤ γ * Vs :=
      mul_le_mul_of_nonneg_left h2 hγ0.le
    linarith
  have hiC : 1 / C ≤ 1 / 2 := by
    rw [div_le_div_iff₀ hC0 (by norm_num)]; linarith
  have hiC0 : 0 ≤ 1 / C := by positivity
  have hW1 : (1 - γ) * W ≤ 11 / 14 := by
    have e : (1 - γ) * W = (1 - 1 / C) * ((1 - γ) * Vz) + (1 / C) * ((1 - γ) * Vs) := by
      rw [hW]; ring
    rw [e, hVz7]
    have h1 : (1 / C) * ((1 - γ) * Vs) ≤ (1 / C) * 1 := mul_le_mul_of_nonneg_left hVs1 hiC0
    linarith
  have hG : 3 / 14 ≤ (Vs - W) * (1 - γ * (γ + δ)) := by
    have e : (Vs - W) * (1 - γ * (γ + δ)) = 1 - (1 - γ) * W := by linear_combination hVsp
    rw [e]; linarith
  -- `(1 - γ q)(1 - γ p) ≤ 4 (1-γ)²`
  have hprod : (1 - γ * (γ - δ)) * (1 - γ * (γ + δ)) ≤ 4 * (1 - γ) ^ 2 := by
    have e1 : (1 - γ * (γ - δ)) * (1 - γ * (γ + δ)) = (1 - γ ^ 2) ^ 2 - (γ * δ) ^ 2 := by ring
    have hpos : 0 ≤ 1 - γ ^ 2 := by
      have : γ ^ 2 ≤ 1 * γ := by rw [sq]; exact mul_le_mul_of_nonneg_right hγ1.le hγ0.le
      linarith
    have hle : 1 - γ ^ 2 ≤ 2 * (1 - γ) := by
      have : 0 ≤ (1 - γ) ^ 2 := sq_nonneg _
      have e : 2 * (1 - γ) - (1 - γ ^ 2) = (1 - γ) ^ 2 := by ring
      linarith
    have e2 : (1 - γ ^ 2) ^ 2 ≤ (2 * (1 - γ)) ^ 2 := pow_le_pow_left₀ hpos hle 2
    have e3 : (2 * (1 - γ)) ^ 2 = 4 * (1 - γ) ^ 2 := by ring
    have e4 : 0 ≤ (γ * δ) ^ 2 := sq_nonneg _
    rw [e1]; linarith
  -- the key scalar inequality `24 (1 - γ x) ≤ 448 (1-γ)² (V⋆(s) - W)`
  have hkey : 24 * (1 - γ * x) ≤ 448 * (1 - γ) ^ 2 * (Vs - W) := by
    have h1 : (1 - γ * x) * (1 - γ * (γ + δ)) ≤ (1 - γ * (γ - δ)) * (1 - γ * (γ + δ)) :=
      mul_le_mul_of_nonneg_right hEq hEp.le
    have h3 : 448 * (1 - γ) ^ 2 * (3 / 14) ≤ 448 * (1 - γ) ^ 2 * ((Vs - W) * (1 - γ * (γ + δ))) :=
      mul_le_mul_of_nonneg_left hG (by positivity)
    have h4 : (24 * (1 - γ * x)) * (1 - γ * (γ + δ)) ≤
        (448 * (1 - γ) ^ 2 * (Vs - W)) * (1 - γ * (γ + δ)) := by
      have e5 : (24 * (1 - γ * x)) * (1 - γ * (γ + δ)) = 24 * ((1 - γ * x) * (1 - γ * (γ + δ))) := by
        ring
      have e6 : (448 * (1 - γ) ^ 2 * (Vs - W)) * (1 - γ * (γ + δ)) =
          448 * (1 - γ) ^ 2 * ((Vs - W) * (1 - γ * (γ + δ))) := by ring
      rw [e5, e6]
      linarith
    exact le_of_mul_le_mul_right h4 hEp
  -- the gap identity `V⋆(s)(1 - γx) - 1 - γ(1-x)W = γ(p-x)(V⋆(s) - W)`
  have hid : Vs * (1 - γ * x) - (1 + γ * (1 - x) * W) = γ * ((γ + δ) - x) * (Vs - W) := by
    linear_combination hVsp
  have hVpiE : Vpi * (1 - γ * x) ≤ 1 + γ * (1 - x) * W := (le_div_iff₀ hE).mp hVpi
  have hgapE : γ * ((γ + δ) - x) * (Vs - W) ≤ (Vs - Vpi) * (1 - γ * x) := by
    have e : (Vs - Vpi) * (1 - γ * x) = Vs * (1 - γ * x) - Vpi * (1 - γ * x) := by ring
    rw [e]; linarith
  have hγpx : γ * ((γ + δ) - x) = 448 * (1 - γ) ^ 2 * ε * (1 - a) := by
    rw [hpx]; linear_combination (2 * (1 - a)) * hγδ
  have hεa : 0 ≤ ε * (1 - a) := mul_nonneg hε (by linarith)
  have hmain : (24 * ε * (1 - a)) * (1 - γ * x) ≤ (Vs - Vpi) * (1 - γ * x) := by
    have h1 := mul_le_mul_of_nonneg_left hkey hεa
    have h2 : (24 * ε * (1 - a)) * (1 - γ * x) = ε * (1 - a) * (24 * (1 - γ * x)) := by ring
    have h3 : ε * (1 - a) * (448 * (1 - γ) ^ 2 * (Vs - W)) = γ * ((γ + δ) - x) * (Vs - W) := by
      rw [hγpx]; ring
    rw [h2]; linarith
  exact le_of_mul_le_mul_right hmain hE

/-- `eq:infinite-delta-key-auxiliary`, per positive state:
`V⋆_θ(s) - V^π_θ(s) ≥ 24 ε (1 - π(θ_s | s))`. -/
theorem lb_value_gap_state (m : ℕ) (hm : 1 ≤ m) (γ ε C : ℝ) (hγ : 2 / 3 ≤ γ) (hγ1 : γ < 1)
    (hε : 0 ≤ ε) (hεmax : 224 * (1 - γ) * ε / γ ≤ 1 / 2) (hC : 2 < C) (θ : Fin m → Bool)
    (π : StationaryPolicy (Option (Fin m)) Bool) (i : Fin m) :
    24 * ε * (1 - (π (some i)).prob (θ i)) ≤
      (lbMDP m hm γ ε C hγ hγ1 hε hεmax hC θ).trajectoryExpectedValue
          (lbMDP m hm γ ε C hγ hγ1 hε hεmax hC θ).optimalGreedyPolicy (some i) -
        (lbMDP m hm γ ε C hγ hγ1 hε hεmax hC θ).trajectoryExpectedValue π (some i) := by
  have hVpi : (lbMDP m hm γ ε C hγ hγ1 hε hεmax hC θ).trajectoryExpectedValue π (some i) ≤
      (1 + γ * (1 - (lbP γ ε * (π (some i)).prob (θ i) + lbQ γ ε * (π (some i)).prob (!θ i))) *
          lbW γ ε C) /
        (1 - γ * (lbP γ ε * (π (some i)).prob (θ i) + lbQ γ ε * (π (some i)).prob (!θ i))) :=
    lb_policy_value_le m hm γ ε C hγ hγ1 hε hεmax hC θ π i
  rw [lb_optimalValue m hm γ ε C hγ hγ1 hε hεmax hC θ (some i)]
  simp only [lbValue]
  obtain ⟨_, hVz, hVs, hWVs, _⟩ := lb_scalar hγ hγ1 hε hεmax hC
  have hab : (π (some i)).prob (θ i) + (π (some i)).prob (!θ i) = 1 := by
    have := (π (some i)).sum_prob
    rwa [sum_bool_split _ (θ i)] at this
  have hγ0 : 0 < γ := by linarith
  have hγne : γ ≠ 0 := hγ0.ne'
  have hγδ : γ * lbGap γ ε = 224 * (1 - γ) ^ 2 * ε := by
    unfold lbGap; field_simp
  exact lb_value_gap_scalar hγ hγ1 hε hC (lbGap_nonneg hγ hε) (lbGap_le hγ hγ1 hεmax) hγδ rfl rfl
    ((π (some i)).prob_nonneg _) ((π (some i)).prob_nonneg _) hab hVs hVz hWVs rfl hVpi

end StatisticalRL.OfflineRL.LowerBound
