import Formalization.ModelFree.QLearningComparisonDefinitions
import Formalization.ModelFree.QLearningChiLower

/-! Source wrapper for Q-comparison-facts (i).
The finite span is the actual maximum minus minimum, not a location bound. -/
open scoped BigOperators
namespace StatisticalRL.QLearning
variable {State : Type*} [Fintype State]

theorem qChi_pairwise_le_span [Nonempty State] (v : State → ℝ) (x y : State) :
    |v x - v y| ≤ qChiValueSpan v := by
  have hx := le_actionMaximum v x
  have hy := le_actionMaximum v y
  have hnx := le_actionMaximum (fun x ↦ -v x) x
  have hny := le_actionMaximum (fun x ↦ -v x) y
  unfold qChiValueSpan
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem qChi_expectation_neg (p : FiniteDistribution State) (v : State → ℝ) :
    p.expectation (fun x ↦ -v x) = -p.expectation v := by
  simp [FiniteDistribution.expectation, Finset.sum_neg_distrib]

theorem qChi_variance_neg (p : FiniteDistribution State) (v : State → ℝ) :
    p.variance (fun x ↦ -v x) = p.variance v := by
  unfold FiniteDistribution.variance
  rw [qChi_expectation_neg]
  simp only [neg_sq]

/-- Bounds of the actual expectation image derived from feasible-row deviation. -/
theorem qChi_expectation_image_bounded (p : FiniteDistribution State) (ρ : ℝ)
    (v : State → ℝ) :
    BddAbove (qRobustExpectations p ρ v) ∧ BddBelow (qRobustExpectations p ρ v) := by
  constructor
  · refine ⟨p.expectation v + Real.sqrt (ρ * p.variance v), ?_⟩
    rintro z ⟨q, hq, rfl⟩
    have hh := (abs_le.mp (qChiBall_abs_expectation_sub_le p q ρ v hq)).2
    linarith
  · refine ⟨p.expectation v - Real.sqrt (ρ * p.variance v), ?_⟩
    rintro z ⟨q, hq, rfl⟩
    have hh := (abs_le.mp (qChiBall_abs_expectation_sub_le p q ρ v hq)).1
    linarith

/-- Negation changes the actual robust supremum into the negative infimum. -/
theorem qChi_sSup_neg_eq_neg_sInf (p : FiniteDistribution State) (ρ : ℝ)
    (hρ : 0 ≤ ρ) (v : State → ℝ) :
    sSup (qRobustExpectations p ρ (fun x ↦ -v x)) = -sInf (qRobustExpectations p ρ v) := by
  have hb := qChi_expectation_image_bounded p ρ v
  have hbn := qChi_expectation_image_bounded p ρ (fun x ↦ -v x)
  apply le_antisymm
  · apply csSup_le (qRobustExpectations_nonempty p ρ hρ _)
    rintro z ⟨q, hq, rfl⟩
    rw [qChi_expectation_neg]
    exact neg_le_neg (csInf_le hb.2 ⟨q, hq, rfl⟩)
  · have hh : -sSup (qRobustExpectations p ρ (fun x ↦ -v x)) ≤
        sInf (qRobustExpectations p ρ v) := by
      apply le_csInf (qRobustExpectations_nonempty p ρ hρ _)
      rintro z ⟨q, hq, rfl⟩
      have hq' := le_csSup hbn.1 (show q.expectation (fun x ↦ -v x) ∈
          qRobustExpectations p ρ (fun x ↦ -v x) from ⟨q, hq, rfl⟩)
      rw [qChi_expectation_neg] at hq'
      linarith
    linarith

/-- Both complete support-function comparisons under the exact finite span
premise. H>0 abstracts the source H=1/(1-gamma); rho=0 is also covered. -/
theorem qChi_support_comparison [Nonempty State] (p : FiniteDistribution State) (ρ H : ℝ)
    (hρ : 0 ≤ ρ) (hH : 0 < H) (v : State → ℝ) (hspan : qChiValueSpan v ≤ H) :
    (Real.sqrt (ρ * p.variance v) - ρ * H ≤
        sSup (qRobustExpectations p ρ v) - p.expectation v ∧
      sSup (qRobustExpectations p ρ v) - p.expectation v ≤ Real.sqrt (ρ * p.variance v)) ∧
    (Real.sqrt (ρ * p.variance v) - ρ * H ≤
        p.expectation v - sInf (qRobustExpectations p ρ v) ∧
      p.expectation v - sInf (qRobustExpectations p ρ v) ≤ Real.sqrt (ρ * p.variance v)) := by
  have hc : ∀ x, |v x - p.expectation v| ≤ H :=
    qChi_abs_centered_le_of_pairwise p v H (fun x y ↦ (qChi_pairwise_le_span v x y).trans hspan)
  have hcn : ∀ x, |-v x - p.expectation (fun x ↦ -v x)| ≤ H := by
    intro x
    rw [qChi_expectation_neg]
    have he : -v x - -p.expectation v = -(v x - p.expectation v) := by ring
    rw [he, abs_neg]
    exact hc x
  have hl := qRobustExpectations_sSup_sub_ge_of_centered_span p v H ρ hH hρ hc
  have hu := qRobustExpectations_sSup_sub_le p ρ hρ v
  have hln := qRobustExpectations_sSup_sub_ge_of_centered_span p (fun x ↦ -v x) H ρ hH hρ hcn
  have hun := qRobustExpectations_sSup_sub_le p ρ hρ (fun x ↦ -v x)
  rw [qChi_variance_neg, qChi_expectation_neg, qChi_sSup_neg_eq_neg_sInf p ρ hρ v] at hln hun
  exact ⟨⟨hl, hu⟩, ⟨by linarith, by linarith⟩⟩

end StatisticalRL.QLearning
