import Formalization.Federated.Sync.PrintedStatement

/-!
# Printed Theorem 7.9 under the literal reading: the prescribed learning rate can exceed 1 (SOURCE-ISSUES C41)

The printed theorem is false under the literal reading; the algorithm's input
range `η ∈ (0,1)` (`federated_RL.tex:51, 76`) is a missing hypothesis. If that
range is read as tacitly assumed, the witness below lies outside the theorem and
the theorem is vacuous for large `K`, not false.

The prescribed step size `η = c_η K (1-γ)⁴ ε² / log(SAKT/δ)` (`federated_RL.tex:114`)
is unbounded in the number of agents `K`, and nothing in the theorem keeps it
below 1. Witness, for every pair of constants `c_T, c_η > 0`: one state, one
action, reward `1`, `γ = 1/2`, `Q₀ = 0`, `τ = T = 1`, `δ = 1/2`, `ε = 1`, and `K`
large. Then (106) and (112–113) hold, every sample path gives `Q_T = η`, the
Bellman optimality equation forces `Q⋆ = 2`, and `|Q_T - Q⋆| = η - 2 > 1 = ε`.
So the success probability is `0 < 1/2 = 1 - δ` on every probability space.

Constants: in the witness only `K` depends on `(c_T, c_η)`; `δ, ε, Q₀, τ, T, γ, S, A`
are fixed. So, by inspection of the proof (not formalized as a separate statement),
readings in which the constants may depend on `δ, ε, Q₀, τ, T, γ, S, A` but not on
`K` are refuted as well.

Scope: this shows only that a hypothesis such as "the prescribed `η` lies in
`(0,1)`" is missing; it says nothing about the cited result under that hypothesis.
-/

open MeasureTheory Filter Topology

namespace StatisticalRL.Ch7Rest.Fed

/-- The one-state, one-action MDP with reward `1` and discount `1/2`. -/
noncomputable def unitMDP : DiscountedMDP (Fin 1) (Fin 1) where
  state_nonempty := ⟨0⟩
  action_nonempty := ⟨0⟩
  transition := fun _ _ ↦ ⟨fun _ ↦ 1, fun _ ↦ zero_le_one, by simp⟩
  reward := fun _ _ ↦ 1
  reward_nonneg := fun _ _ ↦ zero_le_one
  reward_le_one := fun _ _ ↦ le_rfl
  discount := 1 / 2
  discount_nonneg := by norm_num
  discount_lt_one := by norm_num

@[simp] theorem unitMDP_discount : unitMDP.discount = 1 / 2 := rfl

@[simp] theorem unitMDP_reward (s a : Fin 1) : unitMDP.reward s a = 1 := rfl

theorem greedyValue_fin_one (Q : Fin 1 → Fin 1 → ℝ) (s : Fin 1) :
    greedyValue Q s = Q s 0 := ciSup_unique

/-- In `unitMDP` every solution of the Bellman optimality equation equals `2`. -/
theorem unitMDP_optimalQ {Q : Fin 1 → Fin 1 → ℝ} (hQ : IsOptimalQ unitMDP Q) :
    Q 0 0 = 2 := by
  have h := hQ 0 0
  have he : (unitMDP.transition 0 0).expectation (greedyValue Q) = Q 0 0 := by
    simp [FiniteDistribution.expectation, unitMDP, greedyValue_fin_one]
  rw [he, unitMDP_reward, unitMDP_discount] at h
  linarith

/-- One FedSynQ iteration with `τ = 1` from `Q₀ = 0` gives `η` at every agent,
for every sample path. -/
theorem fedRun_one (η : ℝ) (K : ℕ) (hK : 1 ≤ K)
    (samples : ℕ → Fin K → Fin 1 → Fin 1 → Fin 1) (k : Fin K) (s a : Fin 1) :
    fedRun unitMDP η K 1 (fun _ _ ↦ 0) samples 1 k s a = η := by
  have hK' : (K : ℝ) ≠ 0 := by
    have : (1 : ℝ) ≤ K := by exact_mod_cast hK
    linarith
  have hloc : ∀ next : Fin 1 → Fin 1 → Fin 1,
      localUpdate unitMDP η (fun _ _ ↦ 0) next s a = η := by
    intro next
    simp [localUpdate, greedyValue_fin_one]
  simp only [fedRun, fedStep, Nat.mod_one, if_true, hloc, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

/-- The FedSynQ output after `T = 1` iteration with `τ = 1`, `Q₀ = 0` is `η`. -/
theorem fedOutput_one (η : ℝ) (K : ℕ) (hK : 1 ≤ K)
    (samples : ℕ → Fin K → Fin 1 → Fin 1 → Fin 1) (s a : Fin 1) :
    fedOutput unitMDP η K 1 (fun _ _ ↦ 0) samples 1 s a = η := by
  have hK' : (K : ℝ) ≠ 0 := by
    have : (1 : ℝ) ≤ K := by exact_mod_cast hK
    linarith
  simp only [fedOutput, fedRun_one η K hK, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  field_simp

/-- For all constants there is a number of agents `K` at which the printed
iteration bound allows `T = 1` while the printed step size exceeds `3`. -/
theorem exists_large_K (c_T c_η : ℝ) (hT : 0 < c_T) (hη : 0 < c_η) :
    ∃ K : ℕ, 1 ≤ K ∧ 32 * c_T * Real.log (8 * K) ^ 3 < K ∧
      96 * Real.log (2 * K) < c_η * (2 * K) := by
  have h8 : Tendsto (fun K : ℕ ↦ (8 : ℝ) * K) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num)
  have h2 : Tendsto (fun K : ℕ ↦ (2 : ℝ) * K) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num)
  have hA := ((Real.tendsto_pow_log_div_mul_add_atTop 1 0 3 one_ne_zero).comp h8).eventually
    (gt_mem_nhds (show (0 : ℝ) < 1 / (256 * c_T) by positivity))
  have hB := ((Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp h2).eventually
    (gt_mem_nhds (show (0 : ℝ) < c_η / 96 by positivity))
  obtain ⟨K, hA, hB, hK⟩ := (hA.and (hB.and (eventually_ge_atTop 1))).exists
  simp only [Function.comp_apply, one_mul, add_zero, pow_one] at hA hB
  have hKr : (1 : ℝ) ≤ K := by exact_mod_cast hK
  refine ⟨K, hK, ?_, ?_⟩
  · rw [div_lt_iff₀ (by positivity)] at hA
    have h' := mul_lt_mul_of_pos_left hA (show (0 : ℝ) < 32 * c_T by positivity)
    calc 32 * c_T * Real.log (8 * K) ^ 3
        = 32 * c_T * (Real.log (8 * K) ^ 3) := by ring
      _ < 32 * c_T * (1 / (256 * c_T) * (8 * K)) := h'
      _ = K := by field_simp; ring
  · rw [div_lt_iff₀ (by positivity)] at hB
    have h' := mul_lt_mul_of_pos_left hB (show (0 : ℝ) < 96 by norm_num)
    calc 96 * Real.log (2 * K) < 96 * (c_η / 96 * (2 * K)) := h'
      _ = c_η * (2 * K) := by ring

/-- **C41.** For all constants `c_T, c_η > 0`, the printed Theorem 7.9 fails under
the literal reading (no hypothesis `η ∈ (0,1)`). -/
theorem not_thm7_9_at (c_T c_η : ℝ) (hT : 0 < c_T) (hη : 0 < c_η) :
    ¬ Thm7_9_at c_T c_η := by
  intro h
  obtain ⟨K, hK, hTK, hηK⟩ := exists_large_K c_T c_η hT hη
  have hKr : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hL2 : 0 < Real.log (2 * K) := Real.log_pos (by linarith)
  set η : ℝ := c_η * K * (1 - unitMDP.discount) ^ 4 * (1 : ℝ) ^ 2 /
      Real.log (Fintype.card (Fin 1) * Fintype.card (Fin 1) * K * ((1 : ℕ) : ℝ) / (1 / 2))
    with hηdef
  have hηval : η = c_η * K / (16 * Real.log (2 * K)) := by
    rw [hηdef]
    simp only [Fintype.card_fin, Nat.cast_one, one_mul, mul_one, unitMDP_discount, one_pow]
    rw [show (K : ℝ) / (1 / 2) = 2 * K by ring]
    ring
  have hη3 : 3 < η := by
    rw [hηval, lt_div_iff₀ (by positivity)]
    linarith
  obtain ⟨Ω, _, μ, _, samples, Qstar, hQ, hprob⟩ :=
    h (Fin 1) (Fin 1) unitMDP K 1 1 (1 / 2) 1 η (fun _ _ ↦ 0)
      hK le_rfl le_rfl (one_dvd 1) (by norm_num) (by norm_num) (by norm_num) one_pos
      (by norm_num) (fun _ _ ↦ ⟨le_rfl, by norm_num⟩) hηdef
      (by
        have hmin : 0 ≤ min ((1 - unitMDP.discount) / (8 * unitMDP.discount)) (1 / (K : ℝ)) :=
          le_min (by norm_num) (by positivity)
        have : 0 ≤ 1 / η * min ((1 - unitMDP.discount) / (8 * unitMDP.discount))
            (1 / (K : ℝ)) := mul_nonneg (by have := hη3; positivity) hmin
        push_cast
        linarith)
      (by
        simp only [Fintype.card_fin, Nat.cast_one, one_mul, mul_one, unitMDP_discount,
          one_pow]
        rw [show (K : ℝ) / (1 / 2 * (1 - 1 / 2) ^ 2) = 8 * K by ring,
          div_mul_eq_mul_div, div_le_one (by positivity)]
        nlinarith)
  have hQ00 := unitMDP_optimalQ hQ
  have hempty : {ω | ∀ s a, |fedOutput unitMDP η K 1 (fun _ _ ↦ 0) (samples ω) 1 s a
      - Qstar s a| ≤ 1} = ∅ := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_forall, not_le]
    refine ⟨0, 0, ?_⟩
    rw [fedOutput_one η K hK, hQ00]
    rw [abs_of_pos (by linarith)]
    linarith
  rw [hempty, measureReal_empty] at hprob
  norm_num at hprob

/-- **C41.** Printed Theorem 7.9 is false under the literal reading; the algorithm's
input range `η ∈ (0,1)` (`federated_RL.tex:51, 76`) is a missing hypothesis. If it
is read as tacitly assumed, the theorem is vacuous for large `K` instead. -/
theorem not_thm7_9_printed : ¬ Thm7_9_printed := by
  rintro ⟨c_T, c_η, hT, hη, h⟩
  exact not_thm7_9_at c_T c_η hT hη h

end StatisticalRL.Ch7Rest.Fed
