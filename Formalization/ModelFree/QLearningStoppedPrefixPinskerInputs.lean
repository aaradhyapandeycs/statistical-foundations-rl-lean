import Formalization.ModelFree.QLearningStoppedPrefixGeometricBound
import Formalization.ModelFree.QLearningCountableKLNonneg

/-! Actual stopped-prefix normalization, support and KL summability for Pinsker. -/

open scoped BigOperators
namespace StatisticalRL.QLearning.CountablePinsker

variable {State Action : Type*} [Fintype State] [Fintype Action]

/-- Actual stopped-prefix laws satisfy the probability, support, and
absolute-KL-summability inputs needed by the countable Pinsker theorem.
The KL orientation is numerator `M'`, reference `M`; support is rowwise in
the same direction. Every depth `k` is the existing actual prefix law with
exactly `k` transitions after the fixed initial pair. -/
theorem qActualStoppedPrefixPinskerInputs
    (M M' : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (γ ρ : ℝ) (s : State) (a : Action)
    (hγ : 0 ≤ γ) (hγ1 : γ < 1) (hρ : 0 ≤ ρ)
    (hrowSupport : ∀ x b y, (M'.transition x b).prob y ≠ 0 →
      (M.transition x b).prob y ≠ 0)
    (hrowKL : ∀ x b,
      StatisticalRL.GenerativeLowerBound.finiteKLExpression
        (fun y ↦ (M'.transition x b).prob y)
        (fun y ↦ (M.transition x b).prob y) ≤ ρ) :
    HasSum (qActualStoppedPrefixMass M' π γ s a) 1 ∧
    HasSum (qActualStoppedPrefixMass M π γ s a) 1 ∧
    (∀ z : qStoppedPrefixAbsCarrier (State := State) (Action := Action),
      qActualStoppedPrefixMass M' π γ s a z ≠ 0 →
        qActualStoppedPrefixMass M π γ s a z ≠ 0) ∧
    Summable (fun z : qStoppedPrefixAbsCarrier (State := State) (Action := Action) ↦
      |qStoppedPrefixKLAtom (qActualStoppedPrefixMass M' π γ s a z)
        (qActualStoppedPrefixMass M π γ s a z)|) := by
  constructor
  · exact qActualStoppedPrefixMass_hasSum_one M' π γ s a hγ hγ1
  constructor
  · exact qActualStoppedPrefixMass_hasSum_one M π γ s a hγ hγ1
  constructor
  · intro z hz
    cases z with
    | mk k path =>
        change qGeometricStopWeight γ k *
          qForcedPrefixWeight M' π s a k path ≠ 0 at hz
        change qGeometricStopWeight γ k *
          qForcedPrefixWeight M π s a k path ≠ 0
        have hw : qGeometricStopWeight γ k ≠ 0 := by
          intro hw0
          apply hz
          simp [hw0]
        have hp : qForcedPrefixWeight M' π s a k path ≠ 0 := by
          intro hp0
          apply hz
          simp [hp0]
        have hq := qForcedPrefixWeight_support M M' π s a k
          hrowSupport path hp
        exact mul_ne_zero hw hq
  · exact qActualStoppedPrefixKL_abs_summable M M' π γ ρ s a
      hγ hγ1 hρ hrowSupport hrowKL

/-- At zero discount the actual stopped law is the common zero-transition
point mass, hence its zero-safe KL series is zero. This endpoint statement
does not require any transition-row support or KL assumption. -/
theorem qActualStoppedPrefixPinskerInputs_zero_discount
    (M M' : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (s : State) (a : Action) :
    (∑' z : qStoppedPrefixAbsCarrier (State := State) (Action := Action),
      qStoppedPrefixKLAtom (qActualStoppedPrefixMass M' π 0 s a z)
        (qActualStoppedPrefixMass M π 0 s a z)) = 0 := by
  exact qActualStoppedPrefixKL_zero_discount M M' π s a

end StatisticalRL.QLearning.CountablePinsker
