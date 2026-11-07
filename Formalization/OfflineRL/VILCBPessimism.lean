import Formalization.OfflineRL.VILCBPenaltyDominance
import Formalization.OfflineRL.LCBQRecursion
import Formalization.MDP.DiscountedOccupancyFlow

/-!
# Theorem 6.3, Steps 2–3: pessimism, the lower bound on `V̂`, and the occupancy reduction

Source: `chapters/offlineRL.tex:1209–1307` (Step 2, `eq:infinite-q-upper2` `:1238–1245`, the
arg-min argument `:1262–1292`, `eq:Vhat-pi-V-pihat-order-infinite` `:1301–1304`) and
`:1310–1407` (Step 3, `eq:infinite-v-lower` `:1314–1327`, `eqn:brahms-reduction` `:1379`,
`eq:infinite-d-matrix-form` `:1390–1392`).

All statements are deterministic. `V̂ = value (I.iter τ)`; `Qstar` is the fixed point of
`T_pess` with `Q̂ ≤ Q̂⋆_pe`, `‖Q̂ − Q̂⋆_pe‖ ≤ 1/N` (corrected Lemma 6.2) and the two Lemma 6.4
estimates; `hdom` is the Step 1 penalty dominance for the true rows `P`.
-/

open scoped BigOperators

namespace StatisticalRL.OfflineVILCB.Theorem63

open StatisticalRL StatisticalRL.OfflineVILCB StatisticalRL.OfflineRL.LCBQ

variable {S A : Type*} [Fintype S] [Fintype A]

/-- `|E f − E g| ≤ c` when `|f − g| ≤ c` pointwise. -/
theorem abs_expectation_sub_expectation_le (d : FiniteDistribution S) (f g : S → ℝ) {c : ℝ}
    (h : ∀ t, |f t - g t| ≤ c) : |d.expectation f - d.expectation g| ≤ c := by
  rw [← d.expectation_sub]
  exact d.abs_expectation_le h

section Iterate

variable [Nonempty A] (I : Input S A)

/-- The value of a greedy selection. -/
theorem value_eq_of_greedy (Q : S → A → ℝ) (π : S → A) (h : ∀ s a, Q s a ≤ Q s (π s)) (s : S) :
    Input.value Q s = Q s (π s) :=
  le_antisymm (Input.value_le Q s _ (h s)) (Input.le_value Q s (π s))

/-- **`eq:infinite-q-upper2`** (`offlineRL.tex:1238–1245`), with both cases of Step 2:
`Q̂(s,a) ≤ r(s,a) + γ P_{s,a} V̂` for every pair. -/
theorem iter_le_reward_add (P : S → A → FiniteDistribution S) (τ : ℕ) (Qstar : S → A → ℝ)
    (hfix : I.pess Qstar = Qstar) (hle : I.iter τ ≤ Qstar)
    (hV : ∀ t, |Input.value Qstar t - Input.value (I.iter τ) t| ≤ 1 / I.N)
    (hb : ∀ s a, |I.bonus s a (Input.value Qstar) - I.bonus s a (Input.value (I.iter τ))| ≤ 2 / I.N)
    (hdom : ∀ s a, |(I.Phat s a).expectation (Input.value (I.iter τ)) -
        (P s a).expectation (Input.value (I.iter τ))| + 5 / I.N ≤
      I.bonus s a (Input.value (I.iter τ)))
    (s : S) (a : A) :
    I.iter τ s a ≤ I.r s a + I.γ * (P s a).expectation (Input.value (I.iter τ)) := by
  set V := Input.value (I.iter τ) with hVdef
  have hN : (0 : ℝ) < I.N := by exact_mod_cast I.N_pos
  have hbox := I.iter_mem_box τ
  have hV0 : ∀ t, 0 ≤ V t := fun t => I.value_nonneg _ hbox t
  have hγ0 := I.γ_nonneg
  have hγ1 := I.γ_lt_one
  have hQ : Qstar s a = max (I.tilde s a (Input.value Qstar)) 0 := by
    conv_lhs => rw [← hfix]
    rfl
  have hE1 : |(I.Phat s a).expectation (Input.value Qstar) - (I.Phat s a).expectation V| ≤
      1 / I.N := abs_expectation_sub_expectation_le _ _ _ hV
  have hb1 := hb s a
  have hd := hdom s a
  have hPV : 0 ≤ (P s a).expectation V := (P s a).expectation_nonneg hV0
  have hr := I.r_nonneg s a
  have hdev := le_abs_self ((I.Phat s a).expectation V - (P s a).expectation V)
  have hdev0 := abs_nonneg ((I.Phat s a).expectation V - (P s a).expectation V)
  have htilde : I.tilde s a (Input.value Qstar) ≤ I.r s a + I.γ * (P s a).expectation V := by
    unfold Input.tilde
    rw [abs_le] at hE1 hb1
    have h1 : I.γ * ((I.Phat s a).expectation (Input.value Qstar) - (P s a).expectation V) ≤
        I.γ * (1 / I.N + |(I.Phat s a).expectation V - (P s a).expectation V|) :=
      mul_le_mul_of_nonneg_left (by linarith) hγ0
    have h2 : I.γ * (1 / I.N + |(I.Phat s a).expectation V - (P s a).expectation V|) ≤
        1 / I.N + |(I.Phat s a).expectation V - (P s a).expectation V| := by
      have : 0 ≤ 1 / (I.N : ℝ) + |(I.Phat s a).expectation V - (P s a).expectation V| := by
        positivity
      nlinarith
    have h3 : 1 / (I.N : ℝ) + 2 / I.N ≤ 5 / I.N := by
      rw [← add_div]; exact div_le_div_of_nonneg_right (by norm_num) hN.le
    nlinarith
  have hle' : I.iter τ s a ≤ Qstar s a := hle s a
  rw [hQ] at hle'
  exact hle'.trans (max_le htilde (by positivity))

/-- **`eq:infinite-v-lower`** (`offlineRL.tex:1314–1327`), for every action `a`:
`V̂(s) ≥ r(s,a) + γ P_{s,a} V̂ − 2 b(s,a;V̂)`. -/
theorem reward_add_sub_le_value (P : S → A → FiniteDistribution S) (τ : ℕ) (Qstar : S → A → ℝ)
    (hfix : I.pess Qstar = Qstar)
    (hclose : ∀ s a, |I.iter τ s a - Qstar s a| ≤ 1 / I.N)
    (hV : ∀ t, |Input.value Qstar t - Input.value (I.iter τ) t| ≤ 1 / I.N)
    (hb : ∀ s a, |I.bonus s a (Input.value Qstar) - I.bonus s a (Input.value (I.iter τ))| ≤ 2 / I.N)
    (hdom : ∀ s a, |(I.Phat s a).expectation (Input.value (I.iter τ)) -
        (P s a).expectation (Input.value (I.iter τ))| + 5 / I.N ≤
      I.bonus s a (Input.value (I.iter τ)))
    (s : S) (a : A) :
    I.r s a + I.γ * (P s a).expectation (Input.value (I.iter τ)) -
      2 * I.bonus s a (Input.value (I.iter τ)) ≤ Input.value (I.iter τ) s := by
  set V := Input.value (I.iter τ) with hVdef
  have hN : (0 : ℝ) < I.N := by exact_mod_cast I.N_pos
  have hγ0 := I.γ_nonneg
  have hγ1 := I.γ_lt_one
  have hQ : Qstar s a = max (I.tilde s a (Input.value Qstar)) 0 := by
    conv_lhs => rw [← hfix]
    rfl
  have hE1 : |(I.Phat s a).expectation (Input.value Qstar) - (I.Phat s a).expectation V| ≤
      1 / I.N := abs_expectation_sub_expectation_le _ _ _ hV
  have hb1 := hb s a
  have hd := hdom s a
  have hc := hclose s a
  have hval : I.iter τ s a ≤ V s := Input.le_value _ s a
  have hdev := neg_abs_le ((I.Phat s a).expectation V - (P s a).expectation V)
  have hdev0 := abs_nonneg ((I.Phat s a).expectation V - (P s a).expectation V)
  have htilde : I.tilde s a (Input.value Qstar) ≤ Qstar s a := by rw [hQ]; exact le_max_left _ _
  unfold Input.tilde at htilde
  rw [abs_le] at hE1 hb1 hc
  have h1 : I.γ * ((I.Phat s a).expectation (Input.value Qstar) - (P s a).expectation V) ≥
      -(I.γ * (1 / I.N + |(I.Phat s a).expectation V - (P s a).expectation V|)) := by
    have : (I.Phat s a).expectation (Input.value Qstar) - (P s a).expectation V ≥
        -(1 / I.N + |(I.Phat s a).expectation V - (P s a).expectation V|) := by linarith
    nlinarith
  have h2 : I.γ * (1 / I.N + |(I.Phat s a).expectation V - (P s a).expectation V|) ≤
      1 / I.N + |(I.Phat s a).expectation V - (P s a).expectation V| := by
    have : 0 ≤ 1 / (I.N : ℝ) + |(I.Phat s a).expectation V - (P s a).expectation V| := by
      positivity
    nlinarith
  have h3 : 1 / (I.N : ℝ) + 2 / I.N + 1 / I.N ≤ 5 / I.N := by
    rw [← add_div, ← add_div]; exact div_le_div_of_nonneg_right (by norm_num) hN.le
  nlinarith

end Iterate

section MDP

/-- `P_{π}` for a deterministic `π` is the row of the chosen action. -/
theorem policyTransition_detPolicy (M : DiscountedMDP S A) (f : S → A) (s : S) :
    M.policyTransition (detPolicy f) s = M.transition s (f s) := by
  apply OfflineVILCB.LeaveOneOut.finiteDistribution_ext
  intro t
  simp [detPolicy, DiscountedMDP.policyTransition_prob]

/-- **Step 2 (pessimism)**, `eq:Vhat-pi-V-pihat-order-infinite` (`offlineRL.tex:1253–1304`): if
`Q̂ ≤ r + γ P V̂` everywhere, then `V̂ ≤ V^{π̂}` for every greedy `π̂` (any tie rule). -/
theorem value_le_trajectoryValue [Nonempty A] (I : Input S A) (M : DiscountedMDP S A)
    (hγ : I.γ = M.discount) (hr : I.r = M.reward) (τ : ℕ)
    (hup : ∀ s a, I.iter τ s a ≤
      I.r s a + I.γ * (M.transition s a).expectation (Input.value (I.iter τ)))
    (πhat : S → A) (hgreedy : ∀ s a, I.iter τ s a ≤ I.iter τ s (πhat s)) (s : S) :
    Input.value (I.iter τ) s ≤
      M.trajectoryExpectedValue (fun x => EnvironmentStage.pointMass (πhat x)) s := by
  haveI := M.state_nonempty
  set V := Input.value (I.iter τ) with hVdef
  set Vp := M.trajectoryExpectedValue (detPolicy πhat) with hVp
  change V s ≤ Vp s
  set W : S → ℝ := fun t => Vp t - V t with hW
  obtain ⟨s₀, -, hmin⟩ := Finset.exists_min_image Finset.univ W Finset.univ_nonempty
  have hkey : ∀ t, M.discount * W s₀ ≤ W t := by
    intro t
    have h1 : Vp t = M.reward t (πhat t) + M.discount *
        (M.transition t (πhat t)).expectation Vp := by
      rw [hVp, value_det_eq_Q, trajectoryQ_eq_reward_add]
    have h2 : V t = I.iter τ t (πhat t) := value_eq_of_greedy _ πhat hgreedy t
    have h3 := hup t (πhat t)
    rw [hγ, hr] at h3
    have h4 : W s₀ ≤ (M.transition t (πhat t)).expectation W := by
      have := (M.transition t (πhat t)).expectation_mono (f := fun _ => W s₀) (g := W)
        (fun u => hmin u (Finset.mem_univ u))
      simpa using this
    have h5 : (M.transition t (πhat t)).expectation W =
        (M.transition t (πhat t)).expectation Vp - (M.transition t (πhat t)).expectation V :=
      (M.transition t (πhat t)).expectation_sub Vp V
    rw [h5] at h4
    have h6 := mul_le_mul_of_nonneg_left h4 M.discount_nonneg
    have hWt : W t = Vp t - V t := rfl
    rw [hWt]
    linarith
  have hW0 : 0 ≤ W s₀ := by
    have := hkey s₀
    have h1 := M.discount_lt_one
    nlinarith
  have := hmin s (Finset.mem_univ s)
  simp only [hW] at this hW0
  linarith

/-- **Occupancy reduction** (`eqn:brahms-reduction`, `offlineRL.tex:1340–1402`, via the flow
equation `eq:infinite-d-matrix-form`): if `Δ ≤ γ P_π Δ + 2b` pointwise for a deterministic `π`,
then `(1-γ) ⟨ρ, Δ⟩ ≤ 2 ⟨d^π_ρ, b⟩`. No sign condition on `Δ` is needed. -/
theorem occupancy_reduction (M : DiscountedMDP S A) (f : S → A) (ρ : FiniteDistribution S)
    (Δ b : S → ℝ)
    (h : ∀ s, Δ s ≤ M.discount * (M.transition s (f s)).expectation Δ + 2 * b s) :
    (1 - M.discount) * ρ.expectation Δ ≤
      2 * ∑ s, M.discountedStateOccupancy (detPolicy f) ρ s * b s := by
  set d := M.discountedStateOccupancy (detPolicy f) ρ with hd
  set γ := M.discount with hγ
  have hflow : ∀ t, γ * ∑ u, d u * (M.transition u (f u)).prob t = d t - (1 - γ) * ρ.prob t := by
    intro t
    have h := M.discountedStateOccupancy_flow (detPolicy f) ρ t
    simp only [policyTransition_detPolicy] at h
    rw [← hd, ← hγ] at h
    linarith
  have h1 : ∑ s, d s * Δ s ≤ ∑ s, d s * (γ * (M.transition s (f s)).expectation Δ + 2 * b s) :=
    Finset.sum_le_sum fun s _ =>
      mul_le_mul_of_nonneg_left (h s) (M.discountedStateOccupancy_nonneg _ ρ s)
  have h2 : ∑ s, d s * (γ * (M.transition s (f s)).expectation Δ + 2 * b s) =
      ∑ t, (γ * ∑ u, d u * (M.transition u (f u)).prob t) * Δ t + 2 * ∑ s, d s * b s := by
    simp only [FiniteDistribution.expectation, mul_add, Finset.sum_add_distrib, Finset.mul_sum,
      Finset.sum_mul]
    congr 1
    · rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun u _ => ?_
      ring
    · refine Finset.sum_congr rfl fun s _ => ?_
      ring
  simp_rw [hflow] at h2
  have h3 : ∑ t, (d t - (1 - γ) * ρ.prob t) * Δ t =
      ∑ t, d t * Δ t - (1 - γ) * ρ.expectation Δ := by
    rw [FiniteDistribution.expectation, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun t _ => ?_
    ring
  rw [h3] at h2
  linarith

end MDP

end StatisticalRL.OfflineVILCB.Theorem63
