import Formalization.Ch7Rest.InnerConstant710
import Formalization.MDP.Basic

/-!
# Corrected Theorem 7.9 (FedSynQ): deterministic (pathwise) analysis

Source: `chapters/federated_RL.tex`, algorithm :35–90, Theorem 7.9 :99–117.

Along any sample path `sm t k s a = s_t^k(s,a)` of FedSynQ (`Fed.fedRun`):

* `noiseW u j s a = V_u^j(s_{u+1}^j(s,a)) - P V_u^j (s,a)` is the sampling noise of agent `j` at
  iteration `u+1`;
* `noiseG t k` is the noise process obtained by running the FedSynQ recursion (local averaging
  with weight `η`, agent averaging at synchronization times) on the noise alone. It is written
  with deterministic coefficients: `noiseG t k = Σ_{u<t} (a(t,u) · avg_j noiseW u j +
  b(t,u) · noiseW u k)`;
* `errE = Q_t^k - Q⋆ - γ noiseG t k` obeys a noise-free recursion that contracts per agent.

If `0 ≤ η ≤ 1` and every `|noiseG u k s a| ≤ σ` (`u ≤ T`), then
`|Q_T - Q⋆| ≤ (1-η(1-γ))^T/(1-γ) + γ²σ/(1-γ) + γσ`.
-/

open scoped BigOperators

namespace StatisticalRL.Ch7Rest.FedSync

open StatisticalRL.Ch7Rest.Fed StatisticalRL.Ch7Rest.FedGeneric

/-! ## Deterministic coefficients -/

/-- `(a(t,u), b(t,u))`: the weight of the agent-averaged noise and of the agent's own noise of
iteration `u+1` in the noise process at iteration `t`. -/
noncomputable def coefAB (η : ℝ) (τ : ℕ) : ℕ → ℕ → ℝ × ℝ
  | 0, _ => (0, 0)
  | t + 1, u =>
    if (t + 1) % τ = 0 then
      ((1 - η) * ((coefAB η τ t u).1 + (coefAB η τ t u).2) + (if u = t then η else 0), 0)
    else
      ((1 - η) * (coefAB η τ t u).1, (1 - η) * (coefAB η τ t u).2 + (if u = t then η else 0))

/-- Synchronized coefficient `a(t,u)`. -/
noncomputable def coefA (η : ℝ) (τ t u : ℕ) : ℝ := (coefAB η τ t u).1

/-- Local coefficient `b(t,u)`. -/
noncomputable def coefB (η : ℝ) (τ t u : ℕ) : ℝ := (coefAB η τ t u).2

section Coef

variable (η : ℝ) (τ : ℕ)

@[simp] theorem coefA_zero (u : ℕ) : coefA η τ 0 u = 0 := rfl

@[simp] theorem coefB_zero (u : ℕ) : coefB η τ 0 u = 0 := rfl

theorem coefA_succ (t u : ℕ) : coefA η τ (t + 1) u =
    if (t + 1) % τ = 0 then (1 - η) * (coefA η τ t u + coefB η τ t u) + (if u = t then η else 0)
    else (1 - η) * coefA η τ t u := by
  simp only [coefA, coefB, coefAB]
  split_ifs <;> rfl

theorem coefB_succ (t u : ℕ) : coefB η τ (t + 1) u =
    if (t + 1) % τ = 0 then 0 else (1 - η) * coefB η τ t u + (if u = t then η else 0) := by
  simp only [coefB, coefAB]
  split_ifs <;> rfl

theorem coef_eq_zero_of_le : ∀ t u : ℕ, t ≤ u → coefA η τ t u = 0 ∧ coefB η τ t u = 0
  | 0, u, _ => ⟨rfl, rfl⟩
  | t + 1, u, h => by
    have ih := coef_eq_zero_of_le t u (by omega)
    have hne : u ≠ t := by omega
    rw [coefA_succ, coefB_succ, ih.1, ih.2]
    simp only [hne, if_false]
    split_ifs <;> simp

theorem coefA_mul_coefB : ∀ t u : ℕ, coefA η τ t u * coefB η τ t u = 0
  | 0, u => by simp
  | t + 1, u => by
    rw [coefA_succ, coefB_succ]
    by_cases hs : (t + 1) % τ = 0
    · simp [hs]
    · simp only [if_neg hs]
      by_cases hu : u = t
      · subst hu
        have hz := coef_eq_zero_of_le η τ u u le_rfl
        rw [hz.1]
        simp
      · have ih := coefA_mul_coefB t u
        simp only [if_neg hu]
        calc (1 - η) * coefA η τ t u * ((1 - η) * coefB η τ t u + 0)
            = (1 - η) ^ 2 * (coefA η τ t u * coefB η τ t u) := by ring
          _ = 0 := by rw [ih, mul_zero]

theorem succ_mod_of_ne_zero {t τ : ℕ} (hτ : 1 ≤ τ) (h : (t + 1) % τ ≠ 0) :
    (t + 1) % τ = t % τ + 1 := by
  have hlt : t % τ < τ := Nat.mod_lt _ (by omega)
  have hrw : (t + 1) % τ = (t % τ + 1) % τ := (Nat.mod_add_mod t τ 1).symm
  rcases Nat.lt_or_ge (t % τ + 1) τ with h1 | h1
  · rw [hrw, Nat.mod_eq_of_lt h1]
  · have heq : t % τ + 1 = τ := by omega
    rw [hrw, heq, Nat.mod_self] at h
    exact absurd rfl h

/-- Square sums of the coefficients: the total is at most `η` (geometric decay), and the local
part is at most `η²` times the number of iterations since the last synchronization. -/
theorem coef_sq_sum_le (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (hτ : 1 ≤ τ) : ∀ t : ℕ,
    (∑ u ∈ Finset.range t, (coefA η τ t u ^ 2 + coefB η τ t u ^ 2)) ≤ η ∧
      (∑ u ∈ Finset.range t, coefB η τ t u ^ 2) ≤ η ^ 2 * ((t % τ : ℕ) : ℝ)
  | 0 => by simp [hη0]
  | t + 1 => by
    obtain ⟨ih1, ih2⟩ := coef_sq_sum_le hη0 hη1 hτ t
    have hz := coef_eq_zero_of_le η τ t t le_rfl
    have hη2 : 0 ≤ (1 - η) ^ 2 := sq_nonneg _
    have hgeo : (1 - η) ^ 2 * η + η ^ 2 ≤ η := by nlinarith
    by_cases hs : (t + 1) % τ = 0
    · have hA : ∀ u ∈ Finset.range t,
          coefA η τ (t + 1) u ^ 2 + coefB η τ (t + 1) u ^ 2 =
            (1 - η) ^ 2 * (coefA η τ t u ^ 2 + coefB η τ t u ^ 2) := by
        intro u hu
        have hne : u ≠ t := (Finset.mem_range.mp hu).ne
        have hab := coefA_mul_coefB η τ t u
        rw [coefA_succ, coefB_succ, if_pos hs, if_pos hs, if_neg hne]
        linear_combination (2 * (1 - η) ^ 2) * hab
      have hB : ∀ u, coefB η τ (t + 1) u = 0 := fun u => by rw [coefB_succ, if_pos hs]
      refine ⟨?_, ?_⟩
      · rw [Finset.sum_range_succ, Finset.sum_congr rfl hA, ← Finset.mul_sum, coefA_succ,
          coefB_succ, if_pos hs, if_pos hs, if_pos rfl, hz.1, hz.2]
        have := mul_le_mul_of_nonneg_left ih1 hη2
        nlinarith
      · simp only [hB, hs]
        simp
    · have hA : ∀ u ∈ Finset.range t,
          coefA η τ (t + 1) u ^ 2 + coefB η τ (t + 1) u ^ 2 =
            (1 - η) ^ 2 * (coefA η τ t u ^ 2 + coefB η τ t u ^ 2) := by
        intro u hu
        have hne : u ≠ t := (Finset.mem_range.mp hu).ne
        rw [coefA_succ, coefB_succ, if_neg hs, if_neg hs, if_neg hne]
        ring
      have hB' : ∀ u ∈ Finset.range t,
          coefB η τ (t + 1) u ^ 2 = (1 - η) ^ 2 * coefB η τ t u ^ 2 := by
        intro u hu
        have hne : u ≠ t := (Finset.mem_range.mp hu).ne
        rw [coefB_succ, if_neg hs, if_neg hne]
        ring
      refine ⟨?_, ?_⟩
      · rw [Finset.sum_range_succ, Finset.sum_congr rfl hA, ← Finset.mul_sum, coefA_succ,
          coefB_succ, if_neg hs, if_neg hs, if_pos rfl, hz.1, hz.2]
        have := mul_le_mul_of_nonneg_left ih1 hη2
        nlinarith
      · rw [Finset.sum_range_succ, Finset.sum_congr rfl hB', ← Finset.mul_sum, coefB_succ,
          if_neg hs, if_pos rfl, hz.2, succ_mod_of_ne_zero hτ hs]
        have hsum0 : 0 ≤ ∑ u ∈ Finset.range t, coefB η τ t u ^ 2 :=
          Finset.sum_nonneg fun u _ => sq_nonneg _
        have h1 : (1 - η) ^ 2 ≤ 1 := by nlinarith
        have := mul_le_mul_of_nonneg_right h1 hsum0
        push_cast
        nlinarith

/-- Square sum of the per-agent coefficient vector `c_{u,j} = a(t,u)/K + b(t,u)·[j = k]`:
at most `2η/K` under `η(τ-1) ≤ 1/K` (second half of the τ condition (106)). -/
theorem agent_coef_sq_sum_le (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (hτ : 1 ≤ τ) {K : ℕ} (k : Fin K)
    (hητ : η * ((τ : ℝ) - 1) ≤ 1 / (K : ℝ)) (t : ℕ) :
    (∑ u ∈ Finset.range t, ∑ j : Fin K,
      (coefA η τ t u / K + (if j = k then coefB η τ t u else 0)) ^ 2) ≤ 2 * η / K := by
  have hKpos : (0 : ℝ) < K := by exact_mod_cast (lt_of_le_of_lt (Nat.zero_le _) k.isLt)
  have hK1 : (1 : ℝ) ≤ K := by
    exact_mod_cast (Nat.succ_le_of_lt (lt_of_le_of_lt (Nat.zero_le _) k.isLt))
  have hinner : ∀ u, (∑ j : Fin K,
      (coefA η τ t u / K + (if j = k then coefB η τ t u else 0)) ^ 2) =
      (1 / K) * (coefA η τ t u ^ 2 + coefB η τ t u ^ 2) + (1 - 1 / K) * coefB η τ t u ^ 2 := by
    intro u
    have hab := coefA_mul_coefB η τ t u
    have hexp : ∀ j : Fin K, (coefA η τ t u / K + (if j = k then coefB η τ t u else 0)) ^ 2 =
        (coefA η τ t u / K) ^ 2 +
          (if j = k then 2 * (coefA η τ t u / K) * coefB η τ t u + coefB η τ t u ^ 2 else 0) := by
      intro j
      split_ifs <;> ring
    rw [Finset.sum_congr rfl (fun j _ => hexp j), Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Finset.sum_ite_eq' Finset.univ k,
      if_pos (Finset.mem_univ k)]
    field_simp
    linear_combination 2 * hab
  rw [Finset.sum_congr rfl (fun u _ => hinner u), Finset.sum_add_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum]
  obtain ⟨h1, h2⟩ := coef_sq_sum_le η τ hη0 hη1 hτ t
  have hmod : ((t % τ : ℕ) : ℝ) ≤ (τ : ℝ) - 1 := by
    have : t % τ + 1 ≤ τ := Nat.mod_lt _ (by omega)
    have : ((t % τ : ℕ) : ℝ) + 1 ≤ τ := by exact_mod_cast this
    linarith
  have hc2 : 1 - 1 / (K : ℝ) ≤ 1 := by
    have : 0 ≤ 1 / (K : ℝ) := by positivity
    linarith
  have hsum0 : 0 ≤ ∑ u ∈ Finset.range t, coefB η τ t u ^ 2 :=
    Finset.sum_nonneg fun u _ => sq_nonneg _
  have e1 : 1 / (K : ℝ) * (∑ u ∈ Finset.range t, (coefA η τ t u ^ 2 + coefB η τ t u ^ 2)) ≤
      1 / K * η := mul_le_mul_of_nonneg_left h1 (by positivity)
  have e2 : (1 - 1 / (K : ℝ)) * (∑ u ∈ Finset.range t, coefB η τ t u ^ 2) ≤
      ∑ u ∈ Finset.range t, coefB η τ t u ^ 2 := by
    calc _ ≤ 1 * (∑ u ∈ Finset.range t, coefB η τ t u ^ 2) :=
          mul_le_mul_of_nonneg_right hc2 hsum0
      _ = _ := one_mul _
  have e3 : η ^ 2 * ((t % τ : ℕ) : ℝ) ≤ η * (1 / K) := by
    calc η ^ 2 * ((t % τ : ℕ) : ℝ) ≤ η ^ 2 * ((τ : ℝ) - 1) :=
          mul_le_mul_of_nonneg_left hmod (sq_nonneg _)
      _ = η * (η * ((τ : ℝ) - 1)) := by ring
      _ ≤ η * (1 / K) := mul_le_mul_of_nonneg_left hητ hη0
  have : 2 * η / K = 1 / K * η + η * (1 / K) := by ring
  rw [this]
  linarith

end Coef

/-! ## Noise processes along a path -/

variable {State Action : Type} [Fintype State] [Fintype Action]

section Path

variable (M : DiscountedMDP State Action) (η : ℝ) (K τ : ℕ) (Q₀ : State → Action → ℝ)
  (sm : ℕ → Fin K → State → Action → State)

/-- Sampling noise of agent `j` at iteration `u+1`:
`V_u^j(s_{u+1}^j(s,a)) - Σ_{s'} P(s'|s,a) V_u^j(s')`. -/
noncomputable def noiseW (u : ℕ) (j : Fin K) (s : State) (a : Action) : ℝ :=
  greedyValue (fedRun M η K τ Q₀ sm u j) (sm (u + 1) j s a) -
    (M.transition s a).expectation (greedyValue (fedRun M η K τ Q₀ sm u j))

/-- Noise process of agent `k` at iteration `t`. -/
noncomputable def noiseG (t : ℕ) (k : Fin K) (s : State) (a : Action) : ℝ :=
  ∑ u ∈ Finset.range t, (coefA η τ t u * ((1 / (K : ℝ)) * ∑ j, noiseW M η K τ Q₀ sm u j s a) +
    coefB η τ t u * noiseW M η K τ Q₀ sm u k s a)

/-- Noise-free error `Q_t^k - Q⋆ - γ G_t^k`. -/
noncomputable def errE (t : ℕ) (k : Fin K) (s : State) (a : Action) : ℝ :=
  fedRun M η K τ Q₀ sm t k s a - M.optimalityFixedPoint s a -
    M.discount * noiseG M η K τ Q₀ sm t k s a

@[simp] theorem noiseG_zero (k : Fin K) (s : State) (a : Action) :
    noiseG M η K τ Q₀ sm 0 k s a = 0 := by simp [noiseG]

theorem noiseG_succ (t : ℕ) (k : Fin K) (s : State) (a : Action) :
    noiseG M η K τ Q₀ sm (t + 1) k s a =
      if (t + 1) % τ = 0 then
        (1 / (K : ℝ)) * ∑ i, ((1 - η) * noiseG M η K τ Q₀ sm t i s a +
          η * noiseW M η K τ Q₀ sm t i s a)
      else (1 - η) * noiseG M η K τ Q₀ sm t k s a + η * noiseW M η K τ Q₀ sm t k s a := by
  have hKpos : (0 : ℝ) < K := by exact_mod_cast (lt_of_le_of_lt (Nat.zero_le _) k.isLt)
  have hK : (K : ℝ) ≠ 0 := hKpos.ne'
  set w := fun u (j : Fin K) => noiseW M η K τ Q₀ sm u j s a with hw
  have hz := coef_eq_zero_of_le η τ t t le_rfl
  unfold noiseG
  rw [Finset.sum_range_succ]
  split_ifs with hs
  · have hL : ∀ u ∈ Finset.range t,
        coefA η τ (t + 1) u * ((1 / (K : ℝ)) * ∑ j, w u j) + coefB η τ (t + 1) u * w u k =
          (1 - η) * (coefA η τ t u + coefB η τ t u) * ((1 / (K : ℝ)) * ∑ j, w u j) := by
      intro u hu
      have hne : u ≠ t := (Finset.mem_range.mp hu).ne
      rw [coefA_succ, coefB_succ, if_pos hs, if_pos hs, if_neg hne]
      ring
    rw [Finset.sum_congr rfl hL, coefA_succ, coefB_succ, if_pos hs, if_pos hs, if_pos rfl, hz.1,
      hz.2]
    have key : ∀ u, ∑ i : Fin K, (coefA η τ t u * ((1 / (K : ℝ)) * ∑ j, w u j) +
        coefB η τ t u * w u i) =
        (coefA η τ t u + coefB η τ t u) * ∑ j, w u j := by
      intro u
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, ← Finset.mul_sum]
      field_simp
    have hpull : ∑ u ∈ Finset.range t,
        (1 - η) * (coefA η τ t u + coefB η τ t u) * ((1 / (K : ℝ)) * ∑ j, w u j) =
        (1 / (K : ℝ)) * ((1 - η) * ∑ u ∈ Finset.range t,
          (coefA η τ t u + coefB η τ t u) * ∑ j, w u j) := by
      conv_rhs => rw [Finset.mul_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun u _ => by ring
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_comm,
      Finset.sum_congr rfl (fun u _ => key u), hpull]
    ring
  · have hL : ∀ u ∈ Finset.range t,
        coefA η τ (t + 1) u * ((1 / (K : ℝ)) * ∑ j, w u j) + coefB η τ (t + 1) u * w u k =
          (1 - η) * (coefA η τ t u * ((1 / (K : ℝ)) * ∑ j, w u j) + coefB η τ t u * w u k) := by
      intro u hu
      have hne : u ≠ t := (Finset.mem_range.mp hu).ne
      rw [coefA_succ, coefB_succ, if_neg hs, if_neg hs, if_neg hne]
      ring
    rw [Finset.sum_congr rfl hL, ← Finset.mul_sum, coefA_succ, coefB_succ, if_neg hs, if_neg hs,
      if_pos rfl, hz.1, hz.2]
    ring

/-- One local step, after subtracting `Q⋆` and the noise: noise-free. -/
theorem local_step_err (t : ℕ) (i : Fin K) (s : State) (a : Action) :
    localUpdate M η (fedRun M η K τ Q₀ sm t i) (sm (t + 1) i) s a - M.optimalityFixedPoint s a -
      M.discount * ((1 - η) * noiseG M η K τ Q₀ sm t i s a + η * noiseW M η K τ Q₀ sm t i s a) =
    (1 - η) * errE M η K τ Q₀ sm t i s a +
      η * M.discount * ((M.transition s a).expectation (greedyValue (fedRun M η K τ Q₀ sm t i)) -
        (M.transition s a).expectation (vStar M)) := by
  haveI := M.action_nonempty
  unfold localUpdate errE noiseW
  rw [optimalityFixedPoint_bellman M s a]
  ring

theorem errE_succ (t : ℕ) (k : Fin K) (s : State) (a : Action) :
    errE M η K τ Q₀ sm (t + 1) k s a =
      if (t + 1) % τ = 0 then
        (1 / (K : ℝ)) * ∑ i, ((1 - η) * errE M η K τ Q₀ sm t i s a +
          η * M.discount * ((M.transition s a).expectation
            (greedyValue (fedRun M η K τ Q₀ sm t i)) - (M.transition s a).expectation (vStar M)))
      else (1 - η) * errE M η K τ Q₀ sm t k s a +
          η * M.discount * ((M.transition s a).expectation
            (greedyValue (fedRun M η K τ Q₀ sm t k)) - (M.transition s a).expectation (vStar M)) := by
  have hKpos : (0 : ℝ) < K := by exact_mod_cast (lt_of_le_of_lt (Nat.zero_le _) k.isLt)
  have hK : (K : ℝ) ≠ 0 := hKpos.ne'
  have hrun : fedRun M η K τ Q₀ sm (t + 1) =
      fedStep M η K τ (t + 1) (fedRun M η K τ Q₀ sm t) (sm (t + 1)) := rfl
  conv_lhs => unfold errE
  rw [noiseG_succ, hrun]
  split_ifs with hs
  · simp only [fedStep, if_pos hs]
    rw [← Finset.sum_congr rfl (fun i _ => local_step_err M η K τ Q₀ sm t i s a)]
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum]
    field_simp
  · simp only [fedStep, if_neg hs]
    rw [← local_step_err M η K τ Q₀ sm t k s a]

end Path

/-! ## Bounds -/

omit [Fintype State] in
theorem greedyValue_mem [Nonempty Action] (Q : State → Action → ℝ) (x : State) (lo hi : ℝ)
    (h : ∀ a, lo ≤ Q x a ∧ Q x a ≤ hi) : lo ≤ greedyValue Q x ∧ greedyValue Q x ≤ hi := by
  obtain ⟨a₀⟩ := (inferInstance : Nonempty Action)
  exact ⟨le_trans (h a₀).1 (le_ciSup (Finite.bddAbove_range _) a₀), ciSup_le fun a => (h a).2⟩

theorem avg_abs_le {K : ℕ} (hK : 0 < K) (f : Fin K → ℝ) (c : ℝ) (h : ∀ i, |f i| ≤ c) :
    |(1 / (K : ℝ)) * ∑ i, f i| ≤ c := by
  have hKpos : (0 : ℝ) < K := by exact_mod_cast hK
  rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / K)]
  calc 1 / (K : ℝ) * |∑ i, f i| ≤ 1 / K * ∑ i : Fin K, c :=
        mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs _ _).trans
          (Finset.sum_le_sum fun i _ => h i)) (by positivity)
    _ = c := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        field_simp

theorem avg_mem {K : ℕ} (f : Fin K → ℝ) (lo hi : ℝ) (hlo : lo ≤ 0) (h : ∀ i, lo ≤ f i ∧ f i ≤ hi)
    (hhi : 0 ≤ hi) : lo ≤ (1 / (K : ℝ)) * ∑ i, f i ∧ (1 / (K : ℝ)) * ∑ i, f i ≤ hi := by
  rcases Nat.eq_zero_or_pos K with hK | hK
  · subst hK
    simp [hlo, hhi]
  have hKpos : (0 : ℝ) < K := by exact_mod_cast hK
  have hcard : ∀ c : ℝ, (1 / (K : ℝ)) * ∑ _i : Fin K, c = c := by
    intro c
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  constructor
  · calc lo = (1 / (K : ℝ)) * ∑ _i : Fin K, lo := (hcard lo).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => (h i).1) (by positivity)
  · calc (1 / (K : ℝ)) * ∑ i, f i ≤ (1 / (K : ℝ)) * ∑ _i : Fin K, hi :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => (h i).2) (by positivity)
      _ = hi := hcard hi

section Bounds

variable (M : DiscountedMDP State Action) (η : ℝ) (K τ : ℕ) (Q₀ : State → Action → ℝ)
  (sm : ℕ → Fin K → State → Action → State)

/-- Step 0: with `0 ≤ η ≤ 1` and `Q₀ ∈ [0, 1/(1-γ)]`, every iterate stays in `[0, 1/(1-γ)]`. -/
theorem fedRun_mem (hη0 : 0 ≤ η) (hη1 : η ≤ 1)
    (hQ₀ : ∀ s a, 0 ≤ Q₀ s a ∧ Q₀ s a ≤ 1 / (1 - M.discount)) :
    ∀ t k s a, 0 ≤ fedRun M η K τ Q₀ sm t k s a ∧
      fedRun M η K τ Q₀ sm t k s a ≤ 1 / (1 - M.discount) := by
  haveI := M.action_nonempty
  have hg : 0 < 1 - M.discount := by linarith [M.discount_lt_one]
  have hγ0 := M.discount_nonneg
  have hH : 0 ≤ 1 / (1 - M.discount) := by positivity
  have hloc : ∀ (Q : State → Action → ℝ) (nx : State → Action → State),
      (∀ s a, 0 ≤ Q s a ∧ Q s a ≤ 1 / (1 - M.discount)) →
      ∀ s a, 0 ≤ localUpdate M η Q nx s a ∧ localUpdate M η Q nx s a ≤ 1 / (1 - M.discount) := by
    intro Q nx hQ s a
    have hv := greedyValue_mem Q (nx s a) 0 (1 / (1 - M.discount)) (fun b => hQ (nx s a) b)
    have hr0 := M.reward_nonneg s a
    have hr1 := M.reward_le_one s a
    have hy0 : 0 ≤ M.reward s a + M.discount * greedyValue Q (nx s a) := by
      have := mul_nonneg hγ0 hv.1
      linarith
    have hy1 : M.reward s a + M.discount * greedyValue Q (nx s a) ≤ 1 / (1 - M.discount) := by
      have h1 : M.discount * greedyValue Q (nx s a) ≤ M.discount * (1 / (1 - M.discount)) :=
        mul_le_mul_of_nonneg_left hv.2 hγ0
      have h2 : 1 + M.discount * (1 / (1 - M.discount)) = 1 / (1 - M.discount) := by
        field_simp
        ring
      linarith
    have hq := hQ s a
    unfold localUpdate
    constructor
    · have := mul_nonneg (sub_nonneg.mpr hη1) hq.1
      have := mul_nonneg hη0 hy0
      linarith
    · have e1 := mul_le_mul_of_nonneg_left hq.2 (sub_nonneg.mpr hη1)
      have e2 := mul_le_mul_of_nonneg_left hy1 hη0
      nlinarith
  intro t
  induction t with
  | zero => intro k s a; exact hQ₀ s a
  | succ t ih =>
    intro k s a
    have hrun : fedRun M η K τ Q₀ sm (t + 1) =
        fedStep M η K τ (t + 1) (fedRun M η K τ Q₀ sm t) (sm (t + 1)) := rfl
    rw [hrun]
    unfold fedStep
    split_ifs
    · exact avg_mem _ 0 _ le_rfl (fun i => hloc _ _ (ih i) s a) hH
    · exact hloc _ _ (ih k) s a

/-- `|w| ≤ 1/(1-γ)`. -/
theorem noiseW_abs_le (hη0 : 0 ≤ η) (hη1 : η ≤ 1)
    (hQ₀ : ∀ s a, 0 ≤ Q₀ s a ∧ Q₀ s a ≤ 1 / (1 - M.discount)) (u : ℕ) (j : Fin K) (s : State)
    (a : Action) : |noiseW M η K τ Q₀ sm u j s a| ≤ 1 / (1 - M.discount) := by
  haveI := M.action_nonempty
  have hV : ∀ x, 0 ≤ greedyValue (fedRun M η K τ Q₀ sm u j) x ∧
      greedyValue (fedRun M η K τ Q₀ sm u j) x ≤ 1 / (1 - M.discount) := fun x =>
    greedyValue_mem _ x _ _ (fun b => fedRun_mem M η K τ Q₀ sm hη0 hη1 hQ₀ u j x b)
  have hE := expectation_bounds (M.transition s a) _ _ _ hV
  have hv := hV (sm (u + 1) j s a)
  unfold noiseW
  rw [abs_sub_le_iff]
  constructor <;> linarith [hv.1, hv.2, hE.1, hE.2]

/-- Contraction of the noise-free error, given a uniform bound `σ` on the noise process. -/
theorem errE_abs_le (hη0 : 0 ≤ η) (hη1 : η ≤ 1)
    (hQ₀ : ∀ s a, 0 ≤ Q₀ s a ∧ Q₀ s a ≤ 1 / (1 - M.discount)) (σ : ℝ) (hσ : 0 ≤ σ) (T : ℕ)
    (hG : ∀ u ≤ T, ∀ k s a, |noiseG M η K τ Q₀ sm u k s a| ≤ σ) :
    ∀ t ≤ T, ∀ k s a, |errE M η K τ Q₀ sm t k s a| ≤
      (1 - η * (1 - M.discount)) ^ t * (1 / (1 - M.discount)) +
        M.discount ^ 2 * σ / (1 - M.discount) := by
  haveI := M.action_nonempty
  have hg : 0 < 1 - M.discount := by linarith [M.discount_lt_one]
  have hγ0 := M.discount_nonneg
  have hγ1 := M.discount_lt_one
  set g := 1 - M.discount with hgdef
  set γ := M.discount with hγdef
  have hρ0 : 0 ≤ 1 - η * g := by nlinarith
  have hrest : 0 ≤ γ ^ 2 * σ / g := by positivity
  intro t
  induction t with
  | zero =>
    intro _ k s a
    unfold errE
    simp only [noiseG_zero, mul_zero, sub_zero, pow_zero, one_mul]
    have h1 := hQ₀ s a
    have h2 := M.optimalityFixedPoint_bounds s a
    have : |Q₀ s a - M.optimalityFixedPoint s a| ≤ 1 / g := by
      rw [abs_sub_le_iff]; constructor <;> linarith
    have hrun : fedRun M η K τ Q₀ sm 0 k s a = Q₀ s a := rfl
    rw [hrun]
    linarith
  | succ t ih =>
    intro ht k s a
    set b := (1 - η * g) ^ t * (1 / g) + γ ^ 2 * σ / g with hb
    have hQ : ∀ i s' a', |fedRun M η K τ Q₀ sm t i s' a' - M.optimalityFixedPoint s' a'| ≤
        b + γ * σ := by
      intro i s' a'
      have h1 := ih (by omega) i s' a'
      have h2 := hG t (by omega) i s' a'
      have hdec : fedRun M η K τ Q₀ sm t i s' a' - M.optimalityFixedPoint s' a' =
          errE M η K τ Q₀ sm t i s' a' + γ * noiseG M η K τ Q₀ sm t i s' a' := by
        unfold errE; ring
      rw [hdec]
      calc _ ≤ |errE M η K τ Q₀ sm t i s' a'| + |γ * noiseG M η K τ Q₀ sm t i s' a'| :=
            abs_add_le _ _
        _ ≤ b + γ * σ := by
            rw [abs_mul, abs_of_nonneg hγ0]
            exact add_le_add h1 (mul_le_mul_of_nonneg_left h2 hγ0)
    have hP : ∀ i, |(M.transition s a).expectation (greedyValue (fedRun M η K τ Q₀ sm t i)) -
        (M.transition s a).expectation (vStar M)| ≤ b + γ * σ := by
      intro i
      rw [← FiniteDistribution.expectation_sub]
      apply FiniteDistribution.abs_expectation_le
      intro x
      exact greedyValue_sub_le _ _ x _ (fun a' => hQ i x a')
    have hstep : ∀ i, |(1 - η) * errE M η K τ Q₀ sm t i s a +
        η * γ * ((M.transition s a).expectation (greedyValue (fedRun M η K τ Q₀ sm t i)) -
          (M.transition s a).expectation (vStar M))| ≤
        (1 - η * g) ^ (t + 1) * (1 / g) + γ ^ 2 * σ / g := by
      intro i
      have h1 := ih (by omega) i s a
      have h2 := hP i
      calc _ ≤ |(1 - η) * errE M η K τ Q₀ sm t i s a| +
            |η * γ * ((M.transition s a).expectation (greedyValue (fedRun M η K τ Q₀ sm t i)) -
              (M.transition s a).expectation (vStar M))| := abs_add_le _ _
        _ ≤ (1 - η) * b + η * γ * (b + γ * σ) := by
            rw [abs_mul, abs_mul, abs_of_nonneg (sub_nonneg.mpr hη1),
              abs_of_nonneg (mul_nonneg hη0 hγ0)]
            exact add_le_add (mul_le_mul_of_nonneg_left h1 (sub_nonneg.mpr hη1))
              (mul_le_mul_of_nonneg_left h2 (mul_nonneg hη0 hγ0))
        _ = (1 - η * g) ^ (t + 1) * (1 / g) + γ ^ 2 * σ / g := by
            have hgne : g ≠ 0 := hg.ne'
            rw [hb]
            field_simp
            rw [hgdef]
            ring
    rw [errE_succ]
    split_ifs
    · exact avg_abs_le (lt_of_le_of_lt (Nat.zero_le _) k.isLt) _ _ hstep
    · exact hstep k

/-- **Pathwise error bound** for the FedSynQ output. -/
theorem fedOutput_abs_le (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (hK : 1 ≤ K)
    (hQ₀ : ∀ s a, 0 ≤ Q₀ s a ∧ Q₀ s a ≤ 1 / (1 - M.discount)) (σ : ℝ) (hσ : 0 ≤ σ) (T : ℕ)
    (hG : ∀ u ≤ T, ∀ k s a, |noiseG M η K τ Q₀ sm u k s a| ≤ σ) (s : State) (a : Action) :
    |fedOutput M η K τ Q₀ sm T s a - M.optimalityFixedPoint s a| ≤
      (1 - η * (1 - M.discount)) ^ T * (1 / (1 - M.discount)) +
        M.discount ^ 2 * σ / (1 - M.discount) + M.discount * σ := by
  have hKpos : (0 : ℝ) < K := by exact_mod_cast hK
  have hγ0 := M.discount_nonneg
  have heq : fedOutput M η K τ Q₀ sm T s a - M.optimalityFixedPoint s a =
      (1 / (K : ℝ)) * ∑ k, (errE M η K τ Q₀ sm T k s a +
        M.discount * noiseG M η K τ Q₀ sm T k s a) := by
    unfold fedOutput errE
    simp only [sub_add_cancel]
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    field_simp
  rw [heq]
  apply avg_abs_le hK
  intro k
  calc _ ≤ |errE M η K τ Q₀ sm T k s a| + |M.discount * noiseG M η K τ Q₀ sm T k s a| :=
        abs_add_le _ _
    _ ≤ _ := by
        rw [abs_mul, abs_of_nonneg hγ0]
        exact add_le_add (errE_abs_le M η K τ Q₀ sm hη0 hη1 hQ₀ σ hσ T hG T le_rfl k s a)
          (mul_le_mul_of_nonneg_left (hG T le_rfl k s a) hγ0)

end Bounds

end StatisticalRL.Ch7Rest.FedSync
