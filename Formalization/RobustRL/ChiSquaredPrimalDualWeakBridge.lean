import Formalization.RobustRL.ChiSquaredWeakDuality

/-!
# χ² weak duality between the finite primal and scalar dual

The nominal probability vector determines a nonempty finite value interval.
The pointwise clipped inequality lifts to the primal infimum and the scalar
dual supremum over that interval. This proves only weak duality; scalar
maximum attainment and the reverse inequality remain separate.
-/

open scoped BigOperators

namespace StatisticalRL.RobustRL.ChiSquaredPrimalDualWeakBridge

open StatisticalRL
open StatisticalRL.QLearning

variable {State : Type*} [Fintype State]

/-- A normalized finite probability vector forces its carrier to be nonempty. -/
theorem state_nonempty_of_finite_distribution (p : FiniteDistribution State) :
    Nonempty State := by
  classical
  have hsumpos : 0 < ∑ s, p.prob s := by
    rw [p.sum_prob]
    norm_num
  obtain ⟨s, hs, _⟩ :=
    (Finset.sum_pos_iff_of_nonneg (fun s hs ↦ p.prob_nonneg s)).mp hsumpos
  exact ⟨s⟩

noncomputable def valueImage (V : State → ℝ) : Finset ℝ := by
  classical
  exact Finset.univ.image V

noncomputable def valueMin (p : FiniteDistribution State) (V : State → ℝ) : ℝ := by
  classical
  exact (valueImage V).min'
    (Finset.image_nonempty.mpr
      ((Finset.univ_nonempty_iff).mpr (state_nonempty_of_finite_distribution p)))

noncomputable def valueMax (p : FiniteDistribution State) (V : State → ℝ) : ℝ := by
  classical
  exact (valueImage V).max'
    (Finset.image_nonempty.mpr
      ((Finset.univ_nonempty_iff).mpr (state_nonempty_of_finite_distribution p)))

theorem valueMin_le (p : FiniteDistribution State) (V : State → ℝ) (s : State) :
    valueMin p V ≤ V s := by
  classical
  unfold valueMin valueImage
  apply Finset.min'_le
  exact Finset.mem_image.mpr ⟨s, Finset.mem_univ s, rfl⟩

theorem le_valueMax (p : FiniteDistribution State) (V : State → ℝ) (s : State) :
    V s ≤ valueMax p V := by
  classical
  unfold valueMax valueImage
  apply Finset.le_max'
  exact Finset.mem_image.mpr ⟨s, Finset.mem_univ s, rfl⟩

theorem valueMin_le_valueMax (p : FiniteDistribution State) (V : State → ℝ) :
    valueMin p V ≤ valueMax p V := by
  classical
  unfold valueMin valueMax valueImage
  apply Finset.min'_le_max'

/-- The source's clipped nominal objective at a real threshold. -/
noncomputable def dualObjective (p : FiniteDistribution State) (V : State → ℝ)
    (σ α : ℝ) : ℝ :=
  p.expectation (fun s ↦ min (V s) α) -
    Real.sqrt (σ * p.variance (fun s ↦ min (V s) α))

/-- Values of the clipped objective over the source interval of actual value
levels. The interval endpoints are derived from the finite carrier. -/
noncomputable def dualValues (p : FiniteDistribution State) (V : State → ℝ)
    (σ : ℝ) : Set ℝ :=
  {z | ∃ α, α ∈ Set.Icc (valueMin p V) (valueMax p V) ∧
    z = dualObjective p V σ α}

theorem dualValues_nonempty (p : FiniteDistribution State) (V : State → ℝ)
    (σ : ℝ) : (dualValues p V σ).Nonempty := by
  refine ⟨dualObjective p V σ (valueMin p V), ?_⟩
  exact ⟨valueMin p V,
    ⟨le_rfl, valueMin_le_valueMax p V⟩, rfl⟩

theorem dualValues_bddAbove (p : FiniteDistribution State) (V : State → ℝ)
    (σ : ℝ) : BddAbove (dualValues p V σ) := by
  refine ⟨valueMax p V, ?_⟩
  rintro z ⟨α, hα, rfl⟩
  have hmean : p.expectation (fun s ↦ min (V s) α) ≤ α := by
    apply p.expectation_le_const
    intro s
    exact min_le_right _ _
  calc
    dualObjective p V σ α ≤ p.expectation (fun s ↦ min (V s) α) :=
      sub_le_self _ (Real.sqrt_nonneg _)
    _ ≤ α := hmean
    _ ≤ valueMax p V := hα.2

theorem primalValues_nonempty (p : FiniteDistribution State) (V : State → ℝ)
    (σ : ℝ) (hσ : 0 < σ) : (qRobustExpectations p σ V).Nonempty := by
  exact qRobustExpectations_nonempty p σ (le_of_lt hσ) V

theorem primalValues_bddBelow (p : FiniteDistribution State) (V : State → ℝ)
    (σ : ℝ) : BddBelow (qRobustExpectations p σ V) := by
  refine ⟨valueMin p V, ?_⟩
  rintro z ⟨q, hq, rfl⟩
  rw [← q.expectation_const (valueMin p V)]
  apply q.expectation_mono
  intro s
  exact valueMin_le p V s

/-- The actual finite primal infimum dominates the bounded-interval dual
supremum. This consumes the support-aware feasible ball and source radius
positivity; it assumes no optimizer, regularity, compactness, or target-shaped
comparison premise. -/
theorem dual_sSup_le_primal_sInf (p : FiniteDistribution State)
    (V : State → ℝ) (σ : ℝ) (hσ : 0 < σ)
    (hV : ∀ s, 0 ≤ V s) :
    sSup (dualValues p V σ) ≤ sInf (qRobustExpectations p σ V) := by
  have hσ0 : 0 ≤ σ := le_of_lt hσ
  have hdual_ne := dualValues_nonempty p V σ
  have hdual_bound := dualValues_bddAbove p V σ
  have hprimal_ne := primalValues_nonempty p V σ hσ
  have hprimal_bound := primalValues_bddBelow p V σ
  have hpoint : ∀ q, q ∈ qChiBall p σ →
      sSup (dualValues p V σ) ≤ q.expectation V := by
    intro q hq
    apply csSup_le hdual_ne
    intro z hz
    obtain ⟨α, hα, rfl⟩ := hz
    change p.expectation (fun s ↦ min (V s) α) -
      Real.sqrt (σ * p.variance (fun s ↦ min (V s) α)) ≤ q.expectation V
    exact StatisticalRL.RobustRL.ChiSquaredWeakDuality.clipped_scalar_le_feasible_expectation
      p q V σ α hq
  apply le_csInf hprimal_ne
  intro z hz
  obtain ⟨q, hq, rfl⟩ := hz
  exact hpoint q hq

end StatisticalRL.RobustRL.ChiSquaredPrimalDualWeakBridge
