import Formalization.ModelFree.QLearningComparatorDistanceEndpoints

/-! CONDITIONAL comparator-closeness consumption. The actual
model-stability estimate is a visible separate input, not proved or concealed
by this file. No unconditional source or final accuracy claim is made. -/
namespace StatisticalRL.QLearning
variable {State Action : Type*} [Fintype State] [Fintype Action]

/-- Apply a separately established actual-model optimal-trajectory stability
bound to the two actual selected kernels and add the exact source shift cost. -/
theorem qComparator_closeness_of_actualModel_stability (M : DiscountedMDP State Action)
    (ρ : ℝ) (_hρpos : 0 < ρ)
    (hstable : ∀ M' : DiscountedMDP State Action,
      M'.reward = M.reward → M'.discount = M.discount →
      (∀ s a, M'.transition s a ∈ qChiBall (M.transition s a) ρ) →
      ‖M'.trajectoryExpectedQ M'.optimalGreedyPolicy - M.trajectoryExpectedQ M.optimalGreedyPolicy‖ ≤
        Real.sqrt (M.discount*ρ/(2*(1-M.discount)^3))) :
    ∀ (hρ : 0 ≤ ρ) s a,
      |qRobustPlusFixedPoint M ρ (2*ρ*M.effectiveHorizon) hρ s a -
        M.trajectoryExpectedQ M.optimalGreedyPolicy s a| ≤
        Real.sqrt (M.discount*ρ/(2*(1-M.discount)^3)) + 2*ρ/(1-M.discount)^2 ∧
      |qRobustMinusFixedPoint M ρ (2*ρ*M.effectiveHorizon) hρ s a -
        M.trajectoryExpectedQ M.optimalGreedyPolicy s a| ≤
        Real.sqrt (M.discount*ρ/(2*(1-M.discount)^3)) + 2*ρ/(1-M.discount)^2 := by
  intro hρ s a
  have hspec := qComparator_selectedModel_specs M ρ (2*ρ*M.effectiveHorizon) hρ
  have hp := hstable (qRobustPlusModel M ρ (2*ρ*M.effectiveHorizon) hρ)
    hspec.1.2.1 hspec.1.2.2 hspec.1.1
  have hm := hstable (qRobustMinusModel M ρ (2*ρ*M.effectiveHorizon) hρ)
    hspec.2.2.1 hspec.2.2.2 hspec.2.1
  have hred := qComparator_source_norm_distance_reduction M ρ hρ
  have hpn := hred.1.trans (add_le_add hp (le_refl (2*ρ/(1-M.discount)^2)))
  have hmn := hred.2.trans (add_le_add hm (le_refl (2*ρ/(1-M.discount)^2)))
  have hpc : |qRobustPlusFixedPoint M ρ (2*ρ*M.effectiveHorizon) hρ s a -
      M.trajectoryExpectedQ M.optimalGreedyPolicy s a| ≤
      ‖qRobustPlusFixedPoint M ρ (2*ρ*M.effectiveHorizon) hρ - M.trajectoryExpectedQ M.optimalGreedyPolicy‖ := by
    have hh := (norm_le_pi_norm
      ((qRobustPlusFixedPoint M ρ (2*ρ*M.effectiveHorizon) hρ - M.trajectoryExpectedQ M.optimalGreedyPolicy) s) a).trans
      (norm_le_pi_norm
        (qRobustPlusFixedPoint M ρ (2*ρ*M.effectiveHorizon) hρ - M.trajectoryExpectedQ M.optimalGreedyPolicy) s)
    simpa only [Pi.sub_apply, Real.norm_eq_abs] using hh
  have hmc : |qRobustMinusFixedPoint M ρ (2*ρ*M.effectiveHorizon) hρ s a -
      M.trajectoryExpectedQ M.optimalGreedyPolicy s a| ≤
      ‖qRobustMinusFixedPoint M ρ (2*ρ*M.effectiveHorizon) hρ - M.trajectoryExpectedQ M.optimalGreedyPolicy‖ := by
    have hh := (norm_le_pi_norm
      ((qRobustMinusFixedPoint M ρ (2*ρ*M.effectiveHorizon) hρ - M.trajectoryExpectedQ M.optimalGreedyPolicy) s) a).trans
      (norm_le_pi_norm
        (qRobustMinusFixedPoint M ρ (2*ρ*M.effectiveHorizon) hρ - M.trajectoryExpectedQ M.optimalGreedyPolicy) s)
    simpa only [Pi.sub_apply, Real.norm_eq_abs] using hh
  exact ⟨hpc.trans hpn, hmc.trans hmn⟩

/-- A positive-discount/positive-radius stability API suffices: zero branches
are proved by exact actual-model identities instead of being silently excluded. -/
theorem qComparator_closeness_of_positive_actualModel_stability (M : DiscountedMDP State Action)
    (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hstable : 0 < M.discount → 0 < ρ → ∀ M' : DiscountedMDP State Action,
      M'.reward = M.reward → M'.discount = M.discount →
      (∀ s a, M'.transition s a ∈ qChiBall (M.transition s a) ρ) →
      ‖M'.trajectoryExpectedQ M'.optimalGreedyPolicy - M.trajectoryExpectedQ M.optimalGreedyPolicy‖ ≤
        Real.sqrt (M.discount*ρ/(2*(1-M.discount)^3))) (s : State) (a : Action) :
      |qRobustPlusFixedPoint M ρ (2*ρ*M.effectiveHorizon) hρ s a -
        M.trajectoryExpectedQ M.optimalGreedyPolicy s a| ≤
        Real.sqrt (M.discount*ρ/(2*(1-M.discount)^3)) + 2*ρ/(1-M.discount)^2 ∧
      |qRobustMinusFixedPoint M ρ (2*ρ*M.effectiveHorizon) hρ s a -
        M.trajectoryExpectedQ M.optimalGreedyPolicy s a| ≤
        Real.sqrt (M.discount*ρ/(2*(1-M.discount)^3)) + 2*ρ/(1-M.discount)^2 := by
  by_cases hγ0 : M.discount = 0
  · exact qComparator_sourceCloseness_zeroDiscount M ρ hρ hγ0 s a
  by_cases hρ0 : ρ = 0
  · subst ρ
    exact qComparator_sourceCloseness_zeroRadius M hρ s a
  have hγpos : 0 < M.discount := lt_of_le_of_ne M.discount_nonneg (Ne.symm hγ0)
  have hρpos : 0 < ρ := lt_of_le_of_ne hρ (Ne.symm hρ0)
  exact qComparator_closeness_of_actualModel_stability M ρ hρpos (hstable hγpos hρpos) hρ s a

end StatisticalRL.QLearning
