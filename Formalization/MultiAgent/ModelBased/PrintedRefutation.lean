import Formalization.MultiAgent.ModelBased.CE2

/-!
# `not_thm7_6_printed`: CE2 refutes printed Theorem 7.6 (SOURCE-ISSUES C45)
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace StatisticalRL.Ch7Rest.Marl76

open StatisticalRL StatisticalRL.Ch7Rest.Marl

namespace CE2

theorem threshold_eq (C₁ : ℝ) (N : ℕ) (hthr : 128 * C₁ * Real.log (128 * (N : ℝ) ^ 2) ≤ N) :
    C₁ * ((2 : ℕ) : ℝ) ^ 3 / (1 / 4) ^ 2 *
      Real.log (((8 * N : ℕ) : ℝ) * ((2 : ℕ) : ℝ) * N * (∏ i, (A2 i : ℝ)) / (1 / 2)) ≤ N := by
  have hprod : ∏ i, (A2 i : ℝ) = 4 := by simp; norm_num
  have harg : ((8 * N : ℕ) : ℝ) * ((2 : ℕ) : ℝ) * N * 4 / (1 / 2) = 128 * (N : ℝ) ^ 2 := by
    push_cast; ring
  rw [hprod, harg]
  have : C₁ * ((2 : ℕ) : ℝ) ^ 3 / (1 / 4) ^ 2 = 128 * C₁ := by push_cast; ring
  rw [this]
  exact hthr

theorem gap_null (N : ℕ) (hN1 : 1 ≤ N) (hN : 0 < N) (hS : 3 ≤ 8 * N) (hS0 : 0 < 8 * N) :
    (gameSamplingLaw (game hS) hS0 (fun _ => by norm_num) N).real
      {data | gap (game hS) (oracle hS (empiricalGame (game hS) N hN data)) ≤ 1 / 4} = 0 := by
  have hsub : {data | gap (game hS) (oracle hS (empiricalGame (game hS) N hN data)) ≤ 1 / 4} ⊆
      {data | ¬ Good hS N data} := by
    intro data hd hg
    have h1 := gap_ge hS N hN data hg
    have h2 : gap (game hS) (oracle hS (empiricalGame (game hS) N hN data)) ≤ 1 / 4 := hd
    have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
    have hfrac : (N : ℝ) / (((8 * N : ℕ) : ℝ) - 2) ≤ 1 / 6 := by
      push_cast
      rw [div_le_iff₀ (by linarith)]
      linarith
    linarith
  have h0 := good_ae hS hS0 N
  have hle := measureReal_mono (μ := gameSamplingLaw (game hS) hS0 (fun _ => by norm_num) N) hsub
    (measure_ne_top _ _)
  have := measureReal_nonneg (μ := gameSamplingLaw (game hS) hS0 (fun _ => by norm_num) N)
    (s := {data | gap (game hS) (oracle hS (empiricalGame (game hS) N hN data)) ≤ 1 / 4})
  linarith

theorem gapJ_null (N : ℕ) (hN1 : 1 ≤ N) (hN : 0 < N) (hS : 3 ≤ 8 * N) (hS0 : 0 < 8 * N) :
    (gameSamplingLaw (game hS) hS0 (fun _ => by norm_num) N).real
      {data | gapJ (game hS) (toJoint (oracle hS (empiricalGame (game hS) N hN data))) ≤ 1 / 4} =
      0 := by
  simp_rw [gapJ_toJoint]
  exact gap_null N hN1 hN hS hS0

theorem success_null (N : ℕ) (hN1 : 1 ≤ N) (hN : 0 < N) (hS : 3 ≤ 8 * N) (hS0 : 0 < 8 * N) :
    (gameSamplingLaw (game hS) hS0 (fun _ => by norm_num) N).real
      {data | gap (game hS) (oracle hS (empiricalGame (game hS) N hN data)) ≤ 1 / 4 ∧
        gapJ (game hS) (toJoint (oracle hS (empiricalGame (game hS) N hN data))) ≤ 1 / 4} = 0 := by
  have hle := measureReal_mono (μ := gameSamplingLaw (game hS) hS0 (fun _ => by norm_num) N)
    (s₁ := {data | gap (game hS) (oracle hS (empiricalGame (game hS) N hN data)) ≤ 1 / 4 ∧
        gapJ (game hS) (toJoint (oracle hS (empiricalGame (game hS) N hN data))) ≤ 1 / 4})
    (s₂ := {data | gap (game hS) (oracle hS (empiricalGame (game hS) N hN data)) ≤ 1 / 4})
    (fun data hd => hd.1) (measure_ne_top _ _)
  rw [gap_null N hN1 hN hS hS0] at hle
  exact le_antisymm hle measureReal_nonneg

end CE2

open CE2 in
/-- **CE2 refutes printed Theorem 7.6** (SOURCE-ISSUES C45): with an unspecified planning oracle
the printed conclusion fails for every universal constant `C₁`, even with `0 < N`. -/
theorem not_thm7_6_printed : ¬ Thm7_6_printed := by
  rintro ⟨C₁, hC₁, hall⟩
  obtain ⟨N, hN1, hthr⟩ := exists_large_N C₁ hC₁
  have hN : 0 < N := by omega
  have hS : 3 ≤ 8 * N := by omega
  have hS0 : 0 < 8 * N := by omega
  have hR : ∀ (i : Fin 2) h s a, 1 ≤ h → h ≤ 2 →
      0 ≤ (game hS).reward i h s a ∧ (game hS).reward i h s a ≤ 1 :=
    fun i h s a _ _ => game_reward_mem hS i h s a
  have hεH : (1 / 4 : ℝ) ≤ Real.sqrt ((2 : ℕ) : ℝ) := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]; push_cast; norm_num
  have h1 := hall 2 (8 * N) 2 A2 hS0 (fun _ => by norm_num) (game hS) hR N hN (1 / 2) (1 / 4)
    (by norm_num) (by norm_num) (by norm_num) hεH (threshold_eq C₁ N hthr) (oracle hS)
    (fun G' => toJoint (oracle hS G'))
  have hne : ∀ data, IsNE (empiricalGame (game hS) N hN data)
      (oracle hS (empiricalGame (game hS) N hN data)) := fun data => oracle_isNE hS _ rfl
  have h2 := h1 hne (fun data => (hne data).isCCE)
  have h0 := success_null N hN1 hN hS hS0
  have : (1 : ℝ) - 1 / 2 ≤ 0 := h2.trans (le_of_eq h0)
  norm_num at this

open CE2 in
/-- CE2 also refutes the NE-only reading of printed Theorem 7.6. -/
theorem not_thm7_6_printed_ne : ¬ Thm7_6_printed_ne := by
  rintro ⟨C₁, hC₁, hall⟩
  obtain ⟨N, hN1, hthr⟩ := exists_large_N C₁ hC₁
  have hN : 0 < N := by omega
  have hS : 3 ≤ 8 * N := by omega
  have hS0 : 0 < 8 * N := by omega
  have hR : ∀ (i : Fin 2) h s a, 1 ≤ h → h ≤ 2 →
      0 ≤ (game hS).reward i h s a ∧ (game hS).reward i h s a ≤ 1 :=
    fun i h s a _ _ => game_reward_mem hS i h s a
  have hεH : (1 / 4 : ℝ) ≤ Real.sqrt ((2 : ℕ) : ℝ) := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]; push_cast; norm_num
  have h1 := hall 2 (8 * N) 2 A2 hS0 (fun _ => by norm_num) (game hS) hR N hN (1 / 2) (1 / 4)
    (by norm_num) (by norm_num) (by norm_num) hεH (threshold_eq C₁ N hthr) (oracle hS)
  have hne : ∀ data, IsNE (empiricalGame (game hS) N hN data)
      (oracle hS (empiricalGame (game hS) N hN data)) := fun data => oracle_isNE hS _ rfl
  have h2 := h1 hne
  have h0 := gap_null N hN1 hN hS hS0
  have : (1 : ℝ) - 1 / 2 ≤ 0 := h2.trans (le_of_eq h0)
  norm_num at this

open CE2 in
/-- CE2 also refutes the CCE-only reading of printed Theorem 7.6 (the oracle output, an NE, is a
CCE). -/
theorem not_thm7_6_printed_cce : ¬ Thm7_6_printed_cce := by
  rintro ⟨C₁, hC₁, hall⟩
  obtain ⟨N, hN1, hthr⟩ := exists_large_N C₁ hC₁
  have hN : 0 < N := by omega
  have hS : 3 ≤ 8 * N := by omega
  have hS0 : 0 < 8 * N := by omega
  have hR : ∀ (i : Fin 2) h s a, 1 ≤ h → h ≤ 2 →
      0 ≤ (game hS).reward i h s a ∧ (game hS).reward i h s a ≤ 1 :=
    fun i h s a _ _ => game_reward_mem hS i h s a
  have hεH : (1 / 4 : ℝ) ≤ Real.sqrt ((2 : ℕ) : ℝ) := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]; push_cast; norm_num
  have h1 := hall 2 (8 * N) 2 A2 hS0 (fun _ => by norm_num) (game hS) hR N hN (1 / 2) (1 / 4)
    (by norm_num) (by norm_num) (by norm_num) hεH (threshold_eq C₁ N hthr)
    (fun G' => toJoint (oracle hS G'))
  have hne : ∀ data, IsNE (empiricalGame (game hS) N hN data)
      (oracle hS (empiricalGame (game hS) N hN data)) := fun data => oracle_isNE hS _ rfl
  have h2 := h1 (fun data => (hne data).isCCE)
  have h0 := gapJ_null N hN1 hN hS hS0
  have : (1 : ℝ) - 1 / 2 ≤ 0 := h2.trans (le_of_eq h0)
  norm_num at this

end StatisticalRL.Ch7Rest.Marl76
