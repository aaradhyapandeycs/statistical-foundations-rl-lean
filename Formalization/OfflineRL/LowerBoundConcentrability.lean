import Formalization.OfflineRL.LowerBoundFamilyValues
import Formalization.OfflineRL.LowerBoundFamilyKL
import Formalization.MDP.DiscountedOccupancyFlow
import Mathlib.Data.ENNReal.Inv

/-!
# Behaviour law, test distribution and concentrability of the offline hard family

`chapters/offlineRL.tex:2586–2634`, proofs `:5825–5864`.

* `lbBehavior`: the data distribution `d^b(s,a) = μ(s)/2` (`eq:db-sa-inf-LB`).
* `lbTest`: the test distribution `ρ`, uniform on the positive states (`eq:rho-defn-inf-LB`).
* `lb_occupancy_some`: for `ε > 0`, the discounted state occupancy of the optimal greedy policy
  from `ρ` at every positive state is `(1-γ)/((S-1) lbD)`. It is obtained from the flow equation
  `d = (1-γ)ρ + γ dᵀP_π` (`eq:infinite-d-matrix-form`) by summing over the positive states.
* `lb_concentrability`: for `ε > 0`, the single-policy concentrability coefficient
  `C⋆_ρ = max_{(s,a)} d⋆(s,a;ρ)/d^b(s,a)` (`eq:concentrate-infinite-simple`, with the source's
  conventions encoded in `ℝ≥0∞`) lies in `[C, 2C]` (the closed form of `eq:expression-Cstar-LB-inf`).
-/

open scoped BigOperators ENNReal
namespace StatisticalRL.OfflineRL.LowerBound
open StatisticalRL.DiscountedMDP

/-- The batch data distribution `d^b(s,a) = μ(s)/2` (`eq:db-sa-inf-LB`, `chapters/offlineRL.tex:2592–2596`). -/
noncomputable def lbBehavior (C : ℝ) (m : ℕ) (hC : 2 < C) (hm : 1 ≤ m) :
    FiniteDistribution (Option (Fin m) × Bool) where
  prob sa := lbMu C m sa.1 / 2
  prob_nonneg sa := div_nonneg (lbMu_pos hC hm sa.1).le (by norm_num)
  sum_prob := by
    rw [Fintype.sum_prod_type]
    simp only [Fintype.sum_bool, add_halves]
    exact lbMu_sum hC hm

/-- The test-distribution masses of `eq:rho-defn-inf-LB`. -/
noncomputable def lbTestProb (m : ℕ) : Option (Fin m) → ℝ
  | none => 0
  | some _ => 1 / m

/-- The test distribution `ρ(0) = 0`, `ρ(s) = 1/(S-1)` for `s > 0`
(`eq:rho-defn-inf-LB`, `chapters/offlineRL.tex:2619–2627`). -/
noncomputable def lbTest (m : ℕ) (hm : 1 ≤ m) : FiniteDistribution (Option (Fin m)) where
  prob := lbTestProb m
  prob_nonneg s := by
    cases s with
    | none => simp [lbTestProb]
    | some _ => simp only [lbTestProb]; positivity
  sum_prob := by
    have hmR : (m : ℝ) ≠ 0 := by
      have : (0 : ℝ) < m := by exact_mod_cast hm
      exact this.ne'
    simp only [Fintype.sum_option, lbTestProb, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, zero_add]
    field_simp

/-- Flow equation at a positive state, for any MDP on `Option (Fin m)` whose policy kernel never
moves from state `0` to a positive state and moves from `s > 0` to `s' > 0` with probability
`p 1{s' = s} + c`. -/
theorem occupancy_some_flow {m : ℕ} (M : DiscountedMDP (Option (Fin m)) Bool)
    (π : StationaryPolicy (Option (Fin m)) Bool) (ρ : FiniteDistribution (Option (Fin m)))
    (γ p c r : ℝ) (hdisc : M.discount = γ)
    (hnone : ∀ k, (M.policyTransition π none).prob (some k) = 0)
    (hsome : ∀ j k, (M.policyTransition π (some j)).prob (some k) =
      p * (if k = j then 1 else 0) + c)
    (hρ : ∀ k, ρ.prob (some k) = r) (k : Fin m) :
    M.discountedStateOccupancy π ρ (some k) =
      (1 - γ) * r + γ * (p * M.discountedStateOccupancy π ρ (some k) +
        c * ∑ j, M.discountedStateOccupancy π ρ (some j)) := by
  have h := M.discountedStateOccupancy_flow π ρ (some k)
  rw [hdisc, hρ k, Fintype.sum_option, hnone k, mul_zero, zero_add] at h
  have hS : ∑ j, M.discountedStateOccupancy π ρ (some j) *
        (M.policyTransition π (some j)).prob (some k) =
      p * M.discountedStateOccupancy π ρ (some k) +
        c * ∑ j, M.discountedStateOccupancy π ρ (some j) := by
    simp_rw [hsome]
    calc ∑ j, M.discountedStateOccupancy π ρ (some j) * (p * (if k = j then 1 else 0) + c)
        = ∑ j, (p * (if k = j then M.discountedStateOccupancy π ρ (some j) else 0) +
            c * M.discountedStateOccupancy π ρ (some j)) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          split_ifs <;> ring
      _ = p * M.discountedStateOccupancy π ρ (some k) +
            c * ∑ j, M.discountedStateOccupancy π ρ (some j) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_ite_eq]
          simp
  rw [hS] at h
  exact h

/-- Solving the positive-state flow equations: every positive state carries
`(1-γ)/(m (1 - γ(p + m c)))`. -/
theorem occupancy_some_solve {m : ℕ} (hm : 1 ≤ m) (d : Fin m → ℝ) {γ p c : ℝ}
    (hflow : ∀ k, d k = (1 - γ) * (1 / m) + γ * (p * d k + c * ∑ j, d j))
    (hden : 0 < 1 - γ * (p + m * c)) (hp : 0 < 1 - γ * p) (k : Fin m) :
    d k = (1 - γ) / (m * (1 - γ * (p + m * c))) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hm1 : (m : ℝ) * (1 / m) = 1 := by field_simp
  obtain ⟨D, hDdef⟩ : ∃ D, D = ∑ j, d j := ⟨_, rfl⟩
  simp only [← hDdef] at hflow
  have hsum : D = (1 - γ) + γ * (p * D + m * c * D) := by
    have e : ∑ k, d k = ∑ k, ((1 - γ) * (1 / m) + γ * c * D + γ * p * d k) :=
      Finset.sum_congr rfl fun k _ => by linear_combination hflow k
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, ← hDdef] at e
    linear_combination e + (1 - γ) * hm1
  have hD : D * (1 - γ * (p + m * c)) = 1 - γ := by linear_combination hsum
  have h1 : (m * d k - D) * (1 - γ * p) = 0 := by
    linear_combination (m : ℝ) * hflow k - hsum + (1 - γ) * hm1
  have h2 : m * d k - D = 0 := by
    rcases mul_eq_zero.mp h1 with h | h
    · exact h
    · exact absurd h hp.ne'
  rw [eq_div_iff (mul_pos hmR hden).ne']
  linear_combination (1 - γ * (p + m * c)) * h2 + hD

/-- `1 - γ ≤ lbD ≤ 2(1-γ)`. -/
theorem lbD_bounds {γ ε C : ℝ} (hγ : 2 / 3 ≤ γ) (hγ1 : γ < 1) (hε : 0 ≤ ε)
    (hεmax : 224 * (1 - γ) * ε / γ ≤ 1 / 2) (hC : 2 < C) :
    1 - γ ≤ lbD γ ε C ∧ lbD γ ε C ≤ 2 * (1 - γ) := by
  have hγ0 : 0 < γ := by linarith
  have hC0 : 0 < C := by linarith
  have hg0 := lbGap_nonneg hγ hε
  have hg1 := lbGap_le hγ hγ1 hεmax
  have hp1 : lbP γ ε < 1 := by unfold lbP; linarith
  have hpγ : γ ≤ lbP γ ε := by unfold lbP; linarith
  have hq0 : 0 ≤ (1 - lbP γ ε) / C := div_nonneg (by linarith) hC0.le
  have hq1 : (1 - lbP γ ε) / C ≤ 1 - lbP γ ε := by
    rw [div_le_iff₀ hC0]; nlinarith
  have hx1 : lbP γ ε + (1 - lbP γ ε) / C ≤ 1 := by linarith
  have hxγ : γ ≤ lbP γ ε + (1 - lbP γ ε) / C := by linarith
  have e : lbD γ ε C = 1 - γ * (lbP γ ε + (1 - lbP γ ε) / C) := rfl
  have h1 : γ * (lbP γ ε + (1 - lbP γ ε) / C) ≤ γ * 1 := mul_le_mul_of_nonneg_left hx1 hγ0.le
  have h2 : γ * γ ≤ γ * (lbP γ ε + (1 - lbP γ ε) / C) := mul_le_mul_of_nonneg_left hxγ hγ0.le
  have h3 : 0 ≤ (1 - γ) * (1 - γ) := mul_nonneg (by linarith) (by linarith)
  constructor <;> rw [e] <;> nlinarith

section Family

variable (m : ℕ) (hm : 1 ≤ m) (γ ε C : ℝ) (hγ : 2 / 3 ≤ γ) (hγ1 : γ < 1) (hε : 0 ≤ ε)
  (hεmax : 224 * (1 - γ) * ε / γ ≤ 1 / 2) (hC : 2 < C) (θ : Fin m → Bool)

/-- The greedy policy kernel at state `0`: stay at `0` (for every `ε ≥ 0`). -/
theorem lb_greedyTransition_none (t : Option (Fin m)) :
    ((lbMDP m hm γ ε C hγ hγ1 hε hεmax hC θ).policyTransition
        (lbMDP m hm γ ε C hγ hγ1 hε hεmax hC θ).optimalGreedyPolicy none).prob t =
      if t = none then 1 else 0 := by
  rw [policyTransition_prob]
  simp only [DiscountedMDP.optimalGreedyPolicy, EnvironmentStage.expectation_pointMass]
  rw [lb_optimalGreedyAction_none m hm γ ε C hγ hγ1 hε hεmax hC θ]
  simp only [lbMDP, Bool.false_eq_true, ↓reduceIte, lbRow]
  ring

/-- The greedy policy kernel at a positive state `s`, for `ε > 0`: `p δ_s + (1-p) μ`. -/
theorem lb_greedyTransition_some (hεpos : 0 < ε) (j : Fin m) (t : Option (Fin m)) :
    ((lbMDP m hm γ ε C hγ hγ1 hε hεmax hC θ).policyTransition
        (lbMDP m hm γ ε C hγ hγ1 hε hεmax hC θ).optimalGreedyPolicy (some j)).prob t =
      lbP γ ε * (if t = some j then 1 else 0) + (1 - lbP γ ε) * lbMu C m t := by
  rw [policyTransition_prob]
  simp only [DiscountedMDP.optimalGreedyPolicy, EnvironmentStage.expectation_pointMass]
  rw [(lb_optimalGreedyAction m hm γ ε C hγ hγ1 hε hεmax hC θ hεpos).2 j]
  simp only [lbMDP, if_true, lbRow]

/-- `lb_occupancy_some`: for `ε > 0`, the discounted state occupancy of the optimal greedy
policy from `ρ` at a positive state is `(1-γ)/((S-1) lbD)`. -/
theorem lb_occupancy_some (hεpos : 0 < ε) (i : Fin m) :
    (lbMDP m hm γ ε C hγ hγ1 hε hεmax hC θ).discountedStateOccupancy
        (lbMDP m hm γ ε C hγ hγ1 hε hεmax hC θ).optimalGreedyPolicy (lbTest m hm) (some i) =
      (1 - γ) / (m * lbD γ ε C) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hC0 : 0 < C := by linarith
  have hflow := occupancy_some_flow (lbMDP m hm γ ε C hγ hγ1 hε hεmax hC θ)
    (lbMDP m hm γ ε C hγ hγ1 hε hεmax hC θ).optimalGreedyPolicy (lbTest m hm) γ (lbP γ ε)
    ((1 - lbP γ ε) * (1 / (C * m))) (1 / m) rfl
    (fun k => by rw [lb_greedyTransition_none]; simp)
    (fun j k => by
      rw [lb_greedyTransition_some m hm γ ε C hγ hγ1 hε hεmax hC θ hεpos]
      simp only [Option.some.injEq, lbMu])
    (fun k => rfl)
  have hCne : C ≠ 0 := hC0.ne'
  have hmne : (m : ℝ) ≠ 0 := hmR.ne'
  have hmc : (m : ℝ) * ((1 - lbP γ ε) * (1 / (C * m))) = (1 - lbP γ ε) / C := by
    field_simp
  have hden : 1 - γ * (lbP γ ε + m * ((1 - lbP γ ε) * (1 / (C * m)))) = lbD γ ε C := by
    rw [hmc]; rfl
  have hD := (lb_scalar hγ hγ1 hε hεmax hC).1
  have hp : 0 < 1 - γ * lbP γ ε := by
    have hg1 := lbGap_le hγ hγ1 hεmax
    have hg0 := lbGap_nonneg hγ hε
    have hp1 : lbP γ ε < 1 := by unfold lbP; linarith
    have hp0 : 0 ≤ lbP γ ε := by unfold lbP; linarith
    nlinarith
  have h := occupancy_some_solve hm
    (fun k => (lbMDP m hm γ ε C hγ hγ1 hε hεmax hC θ).discountedStateOccupancy
      (lbMDP m hm γ ε C hγ hγ1 hε hεmax hC θ).optimalGreedyPolicy (lbTest m hm) (some k))
    hflow (by rw [hden]; exact hD) hp i
  rw [hden] at h
  exact h

/-- The joint occupancy of the optimal greedy policy factors through its deterministic action. -/
theorem lb_jointOccupancy_eq (s : Option (Fin m)) (a : Bool) :
    (lbMDP m hm γ ε C hγ hγ1 hε hεmax hC θ).discountedJointOccupancy
        (lbMDP m hm γ ε C hγ hγ1 hε hεmax hC θ).optimalGreedyPolicy (lbTest m hm) s a =
      (lbMDP m hm γ ε C hγ hγ1 hε hεmax hC θ).discountedStateOccupancy
          (lbMDP m hm γ ε C hγ hγ1 hε hεmax hC θ).optimalGreedyPolicy (lbTest m hm) s *
        (if a = (lbMDP m hm γ ε C hγ hγ1 hε hεmax hC θ).optimalGreedyAction s then 1 else 0) := by
  rw [discountedJointOccupancy_eq]
  simp [DiscountedMDP.optimalGreedyPolicy, EnvironmentStage.pointMass]

/-- Pair-by-pair upper bound: `d⋆(s,a;ρ) ≤ 2C d^b(s,a)` for every pair, `ε > 0`. -/
theorem lb_occupancy_ratio_le (hεpos : 0 < ε) (sa : Option (Fin m) × Bool) :
    (lbMDP m hm γ ε C hγ hγ1 hε hεmax hC θ).discountedJointOccupancy
        (lbMDP m hm γ ε C hγ hγ1 hε hεmax hC θ).optimalGreedyPolicy (lbTest m hm) sa.1 sa.2 ≤
      2 * C * (lbBehavior C m hC hm).prob sa := by
  obtain ⟨s, a⟩ := sa
  dsimp only
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hC0 : 0 < C := by linarith
  have hCne : C ≠ 0 := hC0.ne'
  have hmne : (m : ℝ) ≠ 0 := hmR.ne'
  rw [lb_jointOccupancy_eq]
  have hind0 : (0 : ℝ) ≤ (if a = (lbMDP m hm γ ε C hγ hγ1 hε hεmax hC θ).optimalGreedyAction s
      then 1 else 0) := by split_ifs <;> norm_num
  have hind1 : (if a = (lbMDP m hm γ ε C hγ hγ1 hε hεmax hC θ).optimalGreedyAction s
      then (1 : ℝ) else 0) ≤ 1 := by split_ifs <;> norm_num
  have hocc0 := (lbMDP m hm γ ε C hγ hγ1 hε hεmax hC θ).discountedStateOccupancy_nonneg
    (lbMDP m hm γ ε C hγ hγ1 hε hεmax hC θ).optimalGreedyPolicy (lbTest m hm) s
  have hle : (lbMDP m hm γ ε C hγ hγ1 hε hεmax hC θ).discountedStateOccupancy
        (lbMDP m hm γ ε C hγ hγ1 hε hεmax hC θ).optimalGreedyPolicy (lbTest m hm) s *
        (if a = (lbMDP m hm γ ε C hγ hγ1 hε hεmax hC θ).optimalGreedyAction s then 1 else 0) ≤
      (lbMDP m hm γ ε C hγ hγ1 hε hεmax hC θ).discountedStateOccupancy
        (lbMDP m hm γ ε C hγ hγ1 hε hεmax hC θ).optimalGreedyPolicy (lbTest m hm) s :=
    mul_le_of_le_one_right hocc0 hind1
  refine hle.trans ?_
  cases s with
  | none =>
    have h1 := finiteDistribution_prob_le_one
      ((lbMDP m hm γ ε C hγ hγ1 hε hεmax hC θ).discountedStateLaw
        (lbMDP m hm γ ε C hγ hγ1 hε hεmax hC θ).optimalGreedyPolicy (lbTest m hm)) none
    change (lbMDP m hm γ ε C hγ hγ1 hε hεmax hC θ).discountedStateOccupancy
        (lbMDP m hm γ ε C hγ hγ1 hε hεmax hC θ).optimalGreedyPolicy (lbTest m hm) none ≤ 1 at h1
    have e : 2 * C * (lbBehavior C m hC hm).prob (none, a) = C - 1 := by
      change 2 * C * ((1 - 1 / C) / 2) = C - 1
      field_simp
    rw [e]; linarith
  | some i =>
    rw [lb_occupancy_some m hm γ ε C hγ hγ1 hε hεmax hC θ hεpos i]
    have e : 2 * C * (lbBehavior C m hC hm).prob (some i, a) = 1 / m := by
      change 2 * C * ((1 / (C * m)) / 2) = 1 / m
      field_simp
    rw [e]
    obtain ⟨hD1, _⟩ := lbD_bounds hγ hγ1 hε hεmax hC
    have hDpos : 0 < lbD γ ε C := lt_of_lt_of_le (by linarith) hD1
    rw [div_le_div_iff₀ (mul_pos hmR hDpos) hmR]
    nlinarith

/-- Lower bound at the pair `(s, θ_s)`: `C d^b(s, θ_s) ≤ d⋆(s, θ_s; ρ)`, `ε > 0`. -/
theorem lb_occupancy_ratio_ge (hεpos : 0 < ε) (i : Fin m) :
    C * (lbBehavior C m hC hm).prob (some i, θ i) ≤
      (lbMDP m hm γ ε C hγ hγ1 hε hεmax hC θ).discountedJointOccupancy
        (lbMDP m hm γ ε C hγ hγ1 hε hεmax hC θ).optimalGreedyPolicy (lbTest m hm) (some i) (θ i) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hC0 : 0 < C := by linarith
  have hCne : C ≠ 0 := hC0.ne'
  have hmne : (m : ℝ) ≠ 0 := hmR.ne'
  rw [lb_jointOccupancy_eq, (lb_optimalGreedyAction m hm γ ε C hγ hγ1 hε hεmax hC θ hεpos).2 i,
    if_pos rfl, mul_one, lb_occupancy_some m hm γ ε C hγ hγ1 hε hεmax hC θ hεpos i]
  have e : C * (lbBehavior C m hC hm).prob (some i, θ i) = 1 / (2 * m) := by
    change C * ((1 / (C * m)) / 2) = 1 / (2 * m)
    field_simp
  rw [e]
  obtain ⟨hD1, hD2⟩ := lbD_bounds hγ hγ1 hε hεmax hC
  have hDpos : 0 < lbD γ ε C := lt_of_lt_of_le (by linarith) hD1
  rw [div_le_div_iff₀ (by positivity) (mul_pos hmR hDpos)]
  nlinarith

/-- **Concentrability of the hard instance** (`eq:expression-Cstar-LB-inf`, closed form): for
`ε > 0`, `C ≤ C⋆_ρ ≤ 2C`, where `C⋆_ρ = max_{(s,a)} d⋆(s,a;ρ)/d^b(s,a)` in `ℝ≥0∞`
(`eq:concentrate-infinite-simple`, `chapters/offlineRL.tex:128–140`). -/
theorem lb_concentrability (hεpos : 0 < ε) :
    ENNReal.ofReal C ≤
        ⨆ sa : Option (Fin m) × Bool,
          ENNReal.ofReal ((lbMDP m hm γ ε C hγ hγ1 hε hεmax hC θ).discountedJointOccupancy
              (lbMDP m hm γ ε C hγ hγ1 hε hεmax hC θ).optimalGreedyPolicy (lbTest m hm)
              sa.1 sa.2) /
            ENNReal.ofReal ((lbBehavior C m hC hm).prob sa) ∧
      (⨆ sa : Option (Fin m) × Bool,
          ENNReal.ofReal ((lbMDP m hm γ ε C hγ hγ1 hε hεmax hC θ).discountedJointOccupancy
              (lbMDP m hm γ ε C hγ hγ1 hε hεmax hC θ).optimalGreedyPolicy (lbTest m hm)
              sa.1 sa.2) /
            ENNReal.ofReal ((lbBehavior C m hC hm).prob sa)) ≤ ENNReal.ofReal (2 * C) := by
  have hC0 : 0 < C := by linarith
  have hdb : ∀ sa, 0 < (lbBehavior C m hC hm).prob sa := fun sa =>
    div_pos (lbMu_pos hC hm sa.1) (by norm_num)
  constructor
  · let i0 : Fin m := ⟨0, by omega⟩
    refine le_iSup_of_le (some i0, θ i0) ?_
    rw [← ENNReal.ofReal_div_of_pos (hdb _)]
    apply ENNReal.ofReal_le_ofReal
    rw [le_div_iff₀ (hdb _)]
    exact lb_occupancy_ratio_ge m hm γ ε C hγ hγ1 hε hεmax hC θ hεpos i0
  · refine iSup_le fun sa => ?_
    rw [← ENNReal.ofReal_div_of_pos (hdb _)]
    apply ENNReal.ofReal_le_ofReal
    rw [div_le_iff₀ (hdb _)]
    exact lb_occupancy_ratio_le m hm γ ε C hγ hγ1 hε hεmax hC θ hεpos sa

end Family

end StatisticalRL.OfflineRL.LowerBound
