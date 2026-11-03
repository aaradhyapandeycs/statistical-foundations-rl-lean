import Formalization.ModelFree.QLearningComparatorDistanceReduction
import Formalization.ModelFree.QLearningChiUpper

/-! Endpoint proofs. These derive the actual zero-discount
and zero-radius identities without assuming the missing sharp stability result. -/
namespace StatisticalRL.QLearning
variable {State Action : Type*} [Fintype State] [Fintype Action]

/-- At zero discount, actual optimal forced-action trajectory Q is immediate reward. -/
theorem qComparator_zeroDiscount_trajectoryQ (M : DiscountedMDP State Action)
    (hγ : M.discount = 0) (s : State) (a : Action) :
    M.trajectoryExpectedQ M.optimalGreedyPolicy s a = M.reward s a := by
  rw [M.optimalGreedy_trajectoryQ]
  have hh := congrFun (congrFun M.optimalityFixedPoint_spec s) a
  change M.reward s a + M.discount * (M.transition s a).expectation _ = M.optimalityFixedPoint s a at hh
  simpa only [hγ, zero_mul, add_zero] using hh.symm

/-- Both actual selected-model optimal Q distances vanish at gamma=0. -/
theorem qComparator_selectedModels_zeroDiscount (M : DiscountedMDP State Action)
    (ρ b : ℝ) (hρ : 0 ≤ ρ) (hγ : M.discount = 0) (s : State) (a : Action) :
    ((qRobustPlusModel M ρ b hρ).trajectoryExpectedQ
      (qRobustPlusModel M ρ b hρ).optimalGreedyPolicy s a =
        M.trajectoryExpectedQ M.optimalGreedyPolicy s a) ∧
    ((qRobustMinusModel M ρ b hρ).trajectoryExpectedQ
      (qRobustMinusModel M ρ b hρ).optimalGreedyPolicy s a =
        M.trajectoryExpectedQ M.optimalGreedyPolicy s a) := by
  rw [qComparator_zeroDiscount_trajectoryQ M hγ]
  constructor
  · simpa only [qRobustPlusModel] using qComparator_zeroDiscount_trajectoryQ
      (qRobustPlusModel M ρ b hρ) hγ s a
  · simpa only [qRobustMinusModel] using qComparator_zeroDiscount_trajectoryQ
      (qRobustMinusModel M ρ b hρ) hγ s a

/-- Supported zero-radius rows have exactly the nominal expectation, including
all nominal zero atoms. No strict positivity/full support is introduced. -/
theorem qComparator_zeroBall_expectation_eq (p q : FiniteDistribution State)
    (hq : q ∈ qChiBall p 0) (v : State → ℝ) : q.expectation v = p.expectation v := by
  have hh := qChiBall_abs_expectation_sub_le p q 0 v hq
  have hz : |q.expectation v-p.expectation v| ≤ 0 := by
    simpa only [zero_mul, Real.sqrt_zero] using hh
  have he := abs_nonpos_iff.mp hz
  linarith

/-- Source b=2rhoH is zero at rho=0; actual both-sign comparators coincide
with actual true optimal trajectory Q by their equations and uniqueness. -/
theorem qComparator_zeroRadius_exact (M : DiscountedMDP State Action) (hρ : (0:ℝ) ≤ 0) :
    qRobustPlusFixedPoint M 0 0 hρ = M.trajectoryExpectedQ M.optimalGreedyPolicy ∧
    qRobustMinusFixedPoint M 0 0 hρ = M.trajectoryExpectedQ M.optimalGreedyPolicy := by
  let Qp := qRobustPlusFixedPoint M 0 0 hρ
  let Qm := qRobustMinusFixedPoint M 0 0 hρ
  have hplus : M.qOptimality Qp = Qp := by
    funext s a
    change M.reward s a + M.discount * (M.transition s a).expectation (qLearningValue M Qp) = Qp s a
    have hh := congrFun (congrFun (qRobustPlusFixedPoint_spec M 0 0 hρ) s) a
    change M.reward s a + 0 + M.discount * sSup (qRobustExpectations (M.transition s a) 0
      (qLearningValue M Qp)) = Qp s a at hh
    rw [qRobustPlusOptimizer_sup M 0 0 hρ s a] at hh
    rw [qComparator_zeroBall_expectation_eq (M.transition s a) _
      (qRobustPlusOptimizer_spec M 0 0 hρ s a).1] at hh
    simpa only [add_zero] using hh
  have hminus : M.qOptimality Qm = Qm := by
    funext s a
    change M.reward s a + M.discount * (M.transition s a).expectation (qLearningValue M Qm) = Qm s a
    have hh := congrFun (congrFun (qRobustMinusFixedPoint_spec M 0 0 hρ) s) a
    change M.reward s a - 0 + M.discount * sInf (qRobustExpectations (M.transition s a) 0
      (qLearningValue M Qm)) = Qm s a at hh
    rw [qRobustMinusOptimizer_inf M 0 0 hρ s a] at hh
    rw [qComparator_zeroBall_expectation_eq (M.transition s a) _
      (qRobustMinusOptimizer_spec M 0 0 hρ s a).1] at hh
    simpa only [sub_zero] using hh
  have hp := (M.optimalityFixedPoint_characterization Qp).mp hplus
  have hm := (M.optimalityFixedPoint_characterization Qm).mp hminus
  constructor
  · funext s a
    rw [M.optimalGreedy_trajectoryQ]
    exact congrFun (congrFun hp s) a
  · funext s a
    rw [M.optimalGreedy_trajectoryQ]
    exact congrFun (congrFun hm s) a

/-- The source comparator-closeness radius is proved at gamma=0, without a
positive-discount geometric argument or any stability estimate premise. -/
theorem qComparator_sourceCloseness_zeroDiscount (M : DiscountedMDP State Action)
    (ρ : ℝ) (hρ : 0 ≤ ρ) (hγ : M.discount = 0) (s : State) (a : Action) :
    (|qRobustPlusFixedPoint M ρ (2*ρ*M.effectiveHorizon) hρ s a -
        M.trajectoryExpectedQ M.optimalGreedyPolicy s a| ≤
      Real.sqrt (M.discount*ρ/(2*(1-M.discount)^3)) + 2*ρ/(1-M.discount)^2) ∧
    (|qRobustMinusFixedPoint M ρ (2*ρ*M.effectiveHorizon) hρ s a -
        M.trajectoryExpectedQ M.optimalGreedyPolicy s a| ≤
      Real.sqrt (M.discount*ρ/(2*(1-M.discount)^3)) + 2*ρ/(1-M.discount)^2) := by
  obtain ⟨hp, hm⟩ := qComparator_source_distance_reduction M ρ hρ s a
  have he := qComparator_selectedModels_zeroDiscount M ρ (2*ρ*M.effectiveHorizon) hρ hγ s a
  rw [he.1, sub_self, abs_zero, zero_add] at hp
  rw [he.2, sub_self, abs_zero, zero_add] at hm
  exact ⟨by simpa only [hγ, zero_mul, zero_div, Real.sqrt_zero, zero_add] using hp,
    by simpa only [hγ, zero_mul, zero_div, Real.sqrt_zero, zero_add] using hm⟩

/-- The source comparator-closeness radius is also exact at rho=0, with no
zero-over-zero scalar selection or strict positivity premise. -/
theorem qComparator_sourceCloseness_zeroRadius (M : DiscountedMDP State Action)
    (hρ : (0:ℝ) ≤ 0) (s : State) (a : Action) :
    (|qRobustPlusFixedPoint M 0 (2*0*M.effectiveHorizon) hρ s a -
        M.trajectoryExpectedQ M.optimalGreedyPolicy s a| ≤
      Real.sqrt (M.discount*0/(2*(1-M.discount)^3)) + 2*0/(1-M.discount)^2) ∧
    (|qRobustMinusFixedPoint M 0 (2*0*M.effectiveHorizon) hρ s a -
        M.trajectoryExpectedQ M.optimalGreedyPolicy s a| ≤
      Real.sqrt (M.discount*0/(2*(1-M.discount)^3)) + 2*0/(1-M.discount)^2) := by
  have he := qComparator_zeroRadius_exact M hρ
  simp only [mul_zero, zero_mul, zero_div, Real.sqrt_zero, zero_add]
  rw [he.1, he.2]
  simp

end StatisticalRL.QLearning
