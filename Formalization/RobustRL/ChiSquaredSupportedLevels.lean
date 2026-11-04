import Formalization.MDP.Basic

/-! χ² SupportedLevels for finite probability rows. This module supports the χ² branch of Lemma 7.1, robust_RL.tex:302–324. -/
open scoped BigOperators
namespace StatisticalRL.RobustRL.ChiSquaredSupportedLevels

variable {State : Type*} [Fintype State]

/-- The minimum supported value is attained, its nominal level mass is in
(0,1], and, when that mass is less than one, a next supported value exists.
States with zero nominal mass need not satisfy the minimum bound. -/
theorem exists_supported_minimum_and_next
    (p : StatisticalRL.FiniteDistribution State) (V : State → ℝ) (b : ℝ)
    (hb : ∀ s, V s ≤ b) :
    ∃ a : ℝ, ∃ s₀ : State,
      0 < p.prob s₀ ∧ V s₀ = a ∧
      (∀ s, 0 < p.prob s → a ≤ V s) ∧
      0 < p.expectation (fun s ↦ if V s = a then 1 else 0) ∧
      p.expectation (fun s ↦ if V s = a then 1 else 0) ≤ 1 ∧
      (p.expectation (fun s ↦ if V s = a then 1 else 0) < 1 →
        ∃ c : ℝ, ∃ s₁ : State,
          0 < p.prob s₁ ∧ V s₁ = c ∧ a < c ∧ c ≤ b ∧
          ∀ s, 0 < p.prob s → V s = a ∨ c ≤ V s) := by
  classical
  let support : Finset State := Finset.univ.filter (fun s ↦ 0 < p.prob s)
  have hsupport : support.Nonempty := by
    have hsum : 0 < ∑ s, p.prob s := by rw [p.sum_prob]; norm_num
    obtain ⟨s, hs, hp⟩ := (Finset.sum_pos_iff_of_nonneg
      (fun s _ ↦ p.prob_nonneg s)).mp hsum
    exact ⟨s, by simp [support, hp]⟩
  obtain ⟨s₀, hs₀, hmin⟩ := Finset.exists_min_image support V hsupport
  have hp₀ : 0 < p.prob s₀ := (Finset.mem_filter.mp hs₀).2
  have hmin' : ∀ s, 0 < p.prob s → V s₀ ≤ V s := by
    intro s hs
    exact hmin s (by simp [support, hs])
  let f : State → ℝ := fun s ↦ if V s = V s₀ then 1 else 0
  have hf0 : ∀ s, 0 ≤ f s := by
    intro s
    dsimp [f]
    split_ifs <;> norm_num
  have hf1 : ∀ s, f s ≤ 1 := by
    intro s
    dsimp [f]
    split_ifs <;> norm_num
  have hmasspos : 0 < p.expectation f := by
    unfold StatisticalRL.FiniteDistribution.expectation
    apply Finset.sum_pos' (fun s _ ↦ mul_nonneg (p.prob_nonneg s) (hf0 s))
    exact ⟨s₀, Finset.mem_univ _, by simpa [f] using hp₀⟩
  have hmassle : p.expectation f ≤ 1 := p.expectation_le_const hf1
  refine ⟨V s₀, s₀, hp₀, rfl, hmin', hmasspos, hmassle, ?_⟩
  intro hlt
  have hextra : ∃ s, 0 < p.prob s ∧ V s₀ < V s := by
    by_contra hn
    have heq : p.expectation f = 1 := by
      unfold StatisticalRL.FiniteDistribution.expectation
      calc
        (∑ s, p.prob s * f s) = ∑ s, p.prob s := by
          apply Finset.sum_congr rfl
          intro s _
          by_cases hz : p.prob s = 0
          · simp [hz]
          · have hp : 0 < p.prob s := lt_of_le_of_ne (p.prob_nonneg s) (Ne.symm hz)
            have hnot : ¬ V s₀ < V s := by
              intro hh
              exact hn ⟨s, hp, hh⟩
            have he : V s = V s₀ := le_antisymm (le_of_not_gt hnot) (hmin' s hp)
            simp [f, he]
        _ = 1 := p.sum_prob
    exact (ne_of_lt hlt) heq
  let above : Finset State := support.filter (fun s ↦ V s₀ < V s)
  obtain ⟨s₁, hp₁, hgt⟩ := hextra
  have habove : above.Nonempty := ⟨s₁, by simp [above, support, hp₁, hgt]⟩
  obtain ⟨t, ht, htmin⟩ := Finset.exists_min_image above V habove
  have htpos : 0 < p.prob t := (Finset.mem_filter.mp (Finset.mem_filter.mp ht).1).2
  have htgt : V s₀ < V t := (Finset.mem_filter.mp ht).2
  refine ⟨V t, t, htpos, rfl, htgt, hb t, ?_⟩
  intro s hp
  rcases (hmin' s hp).eq_or_lt with he | hlt'
  · exact Or.inl he.symm
  · exact Or.inr (htmin s (by simp [above, support, hp, hlt']))
end StatisticalRL.RobustRL.ChiSquaredSupportedLevels
